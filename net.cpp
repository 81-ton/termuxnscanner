#include <arpa/inet.h>
#include <fcntl.h>
#include <netdb.h>
#include <sys/epoll.h>
#include <sys/socket.h>
#include <unistd.h>
#include <netinet/in.h>
#include <ifaddrs.h>
#include <atomic>
#include <chrono>
#include <cstdio>
#include <cstring>
#include <fstream>
#include <functional>
#include <future>
#include <iomanip>
#include <iostream>
#include <map>
#include <mutex>
#include <queue>
#include <regex>
#include <set>
#include <sstream>
#include <string>
#include <thread>
#include <vector>

using namespace std;

// ------------------ Structures ------------------
struct PortResult {
    int port;
    string banner;
};

struct HostInfo {
    string ip;
    string mac;
    string osGuess;
    string deviceName; // added
    vector<PortResult> openTcp;
};

// ------------------ Constants ------------------
static const vector<int> COMMON_TCP_PORTS = {
    21, 22, 23, 25, 53, 80, 110, 123, 135, 139,
    143, 161, 389, 443, 445, 465, 587, 631, 993,
    995, 1723, 3306, 3389, 5432, 5900, 6379, 8080,
    8443, 10000
};

// ------------------ Utils ------------------
static inline string trim(const string& s){
    size_t a = s.find_first_not_of(" \t\r\n");
    if(a==string::npos) return "";
    size_t b = s.find_last_not_of(" \t\r\n");
    return s.substr(a, b-a+1);
}

static inline void set_nonblocking(int fd){
    int fl = fcntl(fd, F_GETFL, 0);
    fcntl(fd, F_SETFL, fl | O_NONBLOCK);
}

static string run_cmd(const string& cmd){
    FILE* p = popen(cmd.c_str(), "r");
    if(!p) return "";
    char buf[512];
    string out;
    while(fgets(buf, sizeof(buf), p)) out += buf;
    pclose(p);
    return out;
}

// Auto-detect local LAN base
static string auto_lan_base(){
    struct ifaddrs *ifap, *ifa;
    char host[NI_MAXHOST];
    if(getifaddrs(&ifap)==0){
        for(ifa=ifap; ifa; ifa=ifa->ifa_next){
            if(ifa->ifa_addr && ifa->ifa_addr->sa_family==AF_INET){
                getnameinfo(ifa->ifa_addr, sizeof(struct sockaddr_in), host, NI_MAXHOST, nullptr, 0, NI_NUMERICHOST);
                string ip(host);
                if(ip.substr(0,4)=="127.") continue; // skip loopback
                auto pos = ip.rfind('.');
                if(pos!=string::npos) {
                    freeifaddrs(ifap);
                    return ip.substr(0,pos);
                }
            }
        }
        freeifaddrs(ifap);
    }
    return "192.168.1"; // fallback
}

// Ping + TTL
static pair<bool,int> ping_alive_ttl(const string& ip){
    string out = run_cmd("ping -c 1 -W 1 " + ip + " 2>/dev/null | grep ttl");
    if(out.empty()) return {false,-1};
    smatch m; regex r("ttl=([0-9]+)");
    if(regex_search(out,m,r)) return {true, stoi(m[1])};
    return {true,-1};
}

// MAC lookup
static string mac_lookup(const string& ip){
    string out = run_cmd("ip neigh show " + ip + " 2>/dev/null");
    smatch m; regex r("lladdr\\s+([0-9a-fA-F:]{17})");
    if(regex_search(out,m,r)) return m[1];
    out = run_cmd("arp -n " + ip + " 2>/dev/null");
    regex r2("([0-9a-fA-F:]{17})");
    if(regex_search(out,m,r2)) return m[1];
    return "";
}

// OS guess from TTL
static string guess_os_from_ttl(int ttl){
    if(ttl>=255) return "Router/Network";
    if(ttl>=128) return "Windows";
    if(ttl>=64) return "Linux/Android";
    if(ttl>=32) return "Old/Embedded";
    return "Unknown";
}

// Device name via nmap/NetBIOS (best-effort)
static string get_device_name(const string& ip){
    string name = run_cmd("nmap -sP -n " + ip + " 2>/dev/null | grep 'Nmap scan report' | awk '{print $5}'");
    return trim(name);
}

// Banner grab
static string grab_banner(int sock, const string& ip, int port){
    if(port==80 || port==8080){
        string req = "GET / HTTP/1.0\r\nHost: " + ip + "\r\nUser-Agent: Scanner/1.0\r\n\r\n";
        send(sock, req.c_str(), req.size(), 0);
        char buf[1024]; int n = recv(sock, buf, sizeof(buf)-1,0);
        if(n>0){ buf[n]=0; string s(buf); smatch m; regex rServer("(?i)^Server:\\s*(.+)$", regex_constants::multiline);
            if(regex_search(s,m,rServer)) return "HTTP: " + trim(m[1]);
            regex rTitle("(?is)<title>(.*?)</title>");
            if(regex_search(s,m,rTitle)) return "HTTP: <title> " + trim(m[1]);
            return "HTTP: Open";
        }
        return "HTTP: Open";
    }
    char buf[512];
    fd_set rf; FD_ZERO(&rf); FD_SET(sock,&rf);
    timeval tv{0,150000};
    if(select(sock+1,&rf,nullptr,nullptr,&tv)>0){
        int n = recv(sock, buf, sizeof(buf)-1,0);
        if(n>0){ buf[n]=0; string s(buf); auto pos = s.find('\n'); if(pos!=string::npos) s=s.substr(0,pos); s=trim(s); if(!s.empty()) return s;}
    }
    return "Open";
}

// ------------------ TCP Scan (batched to avoid FD_SETSIZE) ------------------
static vector<PortResult> fast_tcp_scan(const string& ip, const vector<int>& ports, int batch=500, int timeout_ms=200){
    vector<PortResult> results;
    size_t total = ports.size();
    for(size_t offset=0; offset<total; offset+=batch){
        size_t end = min(offset+batch,total);
        int ep = epoll_create1(0); if(ep<0) continue;
        struct Conn { int fd; int port; bool connected; }; vector<Conn> conns;
        for(size_t i=offset;i<end;i++){
            int fd = socket(AF_INET,SOCK_STREAM,0); if(fd<0) continue;
            set_nonblocking(fd);
            sockaddr_in addr{}; addr.sin_family=AF_INET; addr.sin_port=htons(ports[i]);
            inet_pton(AF_INET,ip.c_str(),&addr.sin_addr);
            int r = connect(fd,(sockaddr*)&addr,sizeof(addr));
            if(r<0 && errno!=EINPROGRESS){ close(fd); continue; }
            epoll_event ev{}; ev.events=EPOLLOUT|EPOLLERR|EPOLLHUP; ev.data.fd=fd;
            if(epoll_ctl(ep,EPOLL_CTL_ADD,fd,&ev)<0){ close(fd); continue; }
            conns.push_back({fd,(int)ports[i],false});
        }
        auto start = chrono::steady_clock::now(); const int MAX_EVENTS=256; epoll_event events[MAX_EVENTS];
        while(true){
            int remaining = timeout_ms-(int)chrono::duration_cast<chrono::milliseconds>(chrono::steady_clock::now()-start).count();
            if(remaining<=0) break;
            int n = epoll_wait(ep,events,MAX_EVENTS,remaining);
            if(n<=0) break;
            for(int i=0;i<n;i++){
                int fd = events[i].data.fd; int err=0; socklen_t len=sizeof(err); getsockopt(fd,SOL_SOCKET,SO_ERROR,&err,&len);
                auto it = find_if(conns.begin(),conns.end(),[&](const Conn& c){return c.fd==fd;});
                if(it==conns.end()){ close(fd); continue; }
                if(err==0){ string banner=grab_banner(fd,ip,it->port); results.push_back({it->port,banner}); }
                epoll_ctl(ep,EPOLL_CTL_DEL,fd,nullptr); close(fd); it->connected=true;
            }
        }
        for(auto &c:conns){ if(!c.connected){ epoll_ctl(ep,EPOLL_CTL_DEL,c.fd,nullptr); close(c.fd); } }
        close(ep);
    }
    return results;
}

// ------------------ Progress bar ------------------
void show_progress(double fraction){
    int width=40; int pos=(int)(fraction*width);
    cout<<"\r["; for(int i=0;i<width;i++) cout<<(i<pos?'=':' '); cout<<"] "<<(int)(fraction*100)<<"%"; cout.flush();
}

// ------------------ Main ------------------
int main(){
    ios::sync_with_stdio(false);
    cout<<"NSt LAN Scanner v1.0\n";

    string base; cout<<"Enter your LAN base (e.g., 192.168.1) or leave empty for auto: ";
    getline(cin,base);
    if(trim(base).empty()) base = auto_lan_base();
    cout<<"Selected base: "<<base<<".0/24\n";

    // Scan mode
    int scan_mode=1;
    cout<<"Scan mode:\n 1) All IPs in subnet\n 2) Single IP\n 3) Custom range\nChoose: ";
    cin>>scan_mode; cin.ignore();

    vector<string> targets;
    if(scan_mode==1){
        for(int i=1;i<=254;i++) targets.push_back(base+"."+to_string(i));
    } else if(scan_mode==2){
        string ip; cout<<"Enter target IP: "; cin>>ip; targets.push_back(ip);
    } else if(scan_mode==3){
        string from,to; cout<<"Enter start IP (last octet): "; cin>>from; cout<<"Enter end IP (last octet): "; cin>>to;
        for(int i=stoi(from);i<=stoi(to);i++) targets.push_back(base+"."+to_string(i));
    }

    // Ports selection
    cout<<"Enter ports to scan (a-b or all or common): ";
    string port_input; cin.ignore(); getline(cin,port_input);
    vector<int> ports;
    if(port_input=="all"){
        for(int i=1;i<=65535;i++) ports.push_back(i);
    } else if(port_input=="common"){
        ports = COMMON_TCP_PORTS;
    } else {
        smatch m; regex r(R"((\d+)-(\d+))");
        if(regex_search(port_input,m,r)){
            int a=stoi(m[1]); int b=stoi(m[2]);
            for(int i=a;i<=b;i++) ports.push_back(i);
        } else {
            cout<<"Invalid port input, using common ports.\n"; ports=COMMON_TCP_PORTS;
        }
    }

    // Alive sweep
    cout<<"Scanning hosts...\n";
    vector<string> alive; mutex aliveMu;
    unsigned int threadsN = max(2u,thread::hardware_concurrency());
    vector<thread> sweepers; int span=(int)targets.size()/threadsN; int cur=0;
    auto sweep_worker = [&](int begin,int end){
        for(int i=begin;i<end;i++){
            string ip=targets[i];
            auto [ok,ttl] = ping_alive_ttl(ip);
            if(ok){ lock_guard<mutex> lk(aliveMu); alive.push_back(ip); cout<<ip<<" alive\n"; }
        }
    };
    for(unsigned int t=0;t<threadsN;t++){
        int a=cur; int b=(t==threadsN-1)?targets.size():cur+span; cur=b; sweepers.emplace_back(sweep_worker,a,b);
    }
    for(auto &th:sweepers) th.join();
    if(alive.empty()){ cout<<"No alive hosts.\n"; return 0; }

    // Per-host scan
    cout<<"Starting TCP scan...\n";
    vector<HostInfo> hosts; mutex hostsMu; atomic<int> progress{0};
    auto host_worker = [&](int begin,int end){
        for(int i=begin;i<end;i++){
            const string &ip=alive[i];
            int ttl=-1; { auto [ok,t]=ping_alive_ttl(ip); if(ok) ttl=t; }
            string os=guess_os_from_ttl(ttl);
            string mac=mac_lookup(ip);
            string device = get_device_name(ip);
            auto openPorts=fast_tcp_scan(ip,ports,500,220);
            { lock_guard<mutex> lk(hostsMu);
                HostInfo hi{ip,mac,os,device,openPorts};
                hosts.push_back(move(hi));
                progress++; show_progress(progress*1.0/alive.size());
            }
        }
    };
    int count = alive.size(); int chunk = max(1,count/(int)threadsN);
    int i=0; vector<thread> workers;
    for(unsigned int t=0;t<threadsN;t++){
        int a=i; int b=(t==threadsN-1)?count:min(count,i+chunk); i=b; workers.emplace_back(host_worker,a,b);
    }
    for(auto &th:workers) th.join(); cout<<"\nScan complete.\n";

    // HTML report
    ofstream html("scan_results.html");
    html<<"<!doctype html><html><head><meta charset='utf-8'><title>LAN Scan</title>"
         "<style>body{font-family:system-ui,Segoe UI,Arial,sans-serif;padding:16px;background:#0b0e14;color:#e6e6e6}"
         "table{border-collapse:collapse;width:100%;}"
         "th,td{border:1px solid #2a2f3a;padding:8px;vertical-align:top}"
         "th{background:#111826}"
         ".ip{color:#9cdcfe}.ok{color:#7CFC00}.hdr{color:#ffdd88}"
         "</style></head><body>";
    html<<"<h1>LAN Scan Results</h1><p>Hosts scanned: "<<alive.size()<<" | Generated on: ";
    { time_t now=time(nullptr); html<<put_time(localtime(&now),"%Y-%m-%d %H:%M:%S"); }
    html<<"</p><table><tr><th>IP</th><th>MAC</th><th>OS</th><th>Device</th><th>Open TCP Ports (banner)</th></tr>";
    for(const auto &h:hosts){
        html<<"<tr><td class='ip'>"<<h.ip<<"</td>";
        html<<"<td>"<<(h.mac.empty()?"<span class='hdr'>(unknown)</span>":h.mac)<<"</td>";
        html<<"<td>"<<h.osGuess<<"</td>";
        html<<"<td>"<<(h.deviceName.empty()?"(unknown)":h.deviceName)<<"</td>";
        html<<"<td>";
        if(h.openTcp.empty()) html<<"<span class='hdr'>None</span>";
        else for(const auto &p:h.openTcp){ string b=p.banner; for(char &c:b){ if(c=='<') c='['; else if(c=='>') c=']'; } html<<"<div><b>"<<p.port<<"</b> : <span class='ok'>"<<b<<"</span></div>"; }
        html<<"</td></tr>";
    }
    html<<"</table></body></html>"; html.close();

    // CSV report
    ofstream csv("scan_topology.csv"); csv<<"IP,MAC,OS,Device,OpenTCPPorts(Banner)\n";
    for(const auto &h:hosts){ csv<<h.ip<<","<<(h.mac.empty()?"":h.mac)<<","<<h.osGuess<<","<<(h.deviceName.empty()?"":h.deviceName)<<","; bool first=true; for(const auto &p:h.openTcp){ if(!first) csv<<" ; "; first=false; string b=p.banner; for(char &c:b){ if(c==','||c=='\n'||c=='\r') c=' '; } csv<<p.port<<" "<<b; } csv<<"\n"; }
    csv.close();

    cout<<"\nReports generated:\n  • scan_results.html\n  • scan_topology.csv\n";
    return 0;
}