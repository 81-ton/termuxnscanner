// (code starts below)
#include <arpa/inet.h>
#include <fcntl.h>
#include <netdb.h>
#include <sys/epoll.h>
#include <sys/socket.h>
#include <unistd.h>

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

struct PortResult {
    int port;
    string banner;   // "Open" or first line/banner/header snippet
};

struct HostInfo {
    string ip;
    string mac;      // may be empty on non-root
    string osGuess;  // Windows / Linux/Android / Unknown
    vector<PortResult> openTcp;
};

static const vector<int> COMMON_TCP_PORTS = {
    21, 22, 23, 25, 53, 80, 110, 123, 135, 139,
    143, 161, 389, 443, 445, 465, 587, 631, 993,
    995, 1723, 3306, 3389, 5432, 5900, 6379, 8080,
    8443, 10000
};

// ----------- utils -----------
static inline string trim(const string& s){
    size_t a = s.find_first_not_of(" \t\r\n");
    if (a == string::npos) return "";
    size_t b = s.find_last_not_of(" \t\r\n");
    return s.substr(a, b-a+1);
}

static inline void set_nonblocking(int fd){
    int fl = fcntl(fd, F_GETFL, 0);
    fcntl(fd, F_SETFL, fl | O_NONBLOCK);
}

// Try run a shell cmd and get stdout (best-effort, safe if denied)
static string run_cmd(const string& cmd){
    FILE* p = popen(cmd.c_str(), "r");
    if(!p) return "";
    char buf[512];
    string out;
    while (fgets(buf, sizeof(buf), p)) out += buf;
    pclose(p);
    return out;
}

// Alive check + TTL extraction via ping
static pair<bool,int> ping_alive_ttl(const string& ip){
    string out = run_cmd("ping -c 1 -W 1 " + ip + " 2>/dev/null | grep ttl");
    if(out.empty()) return {false, -1};
    // Parse ttl=XX
    smatch m;
    regex r("ttl=([0-9]+)");
    if(regex_search(out, m, r)){
        int ttl = stoi(m[1]);
        return {true, ttl};
    }
    return {true, -1};
}

// MAC lookup (may fail without root on Android; handled gracefully)
static string mac_lookup(const string& ip){
    string out = run_cmd("ip neigh show " + ip + " 2>/dev/null");
    smatch m;
    regex r("lladdr\\s+([0-9a-fA-F:]{17})");
    if(regex_search(out, m, r)) return m[1];

    // fallback: arp -n
    out = run_cmd("arp -n " + ip + " 2>/dev/null");
    regex r2("([0-9a-fA-F:]{17})");
    if(regex_search(out, m, r2)) return m[1];

    return ""; // permission denied or not in ARP cache
}

// OS guess from TTL
static string guess_os_from_ttl(int ttl){
    if(ttl >= 255) return "Network/Router";
    if(ttl >= 128) return "Windows";
    if(ttl >= 64)  return "Linux/Android";
    if(ttl >= 32)  return "Old/Embedded";
    return "Unknown";
}

// After TCP connect success, try grab a small banner quickly
static string grab_banner(int sock, const string& ip, int port){
    // For HTTP ports: send GET for server header/title
    if(port == 80 || port == 8080){
        string req = "GET / HTTP/1.0\r\nHost: " + ip + "\r\nUser-Agent: UltrafastScanner/1.0\r\n\r\n";
        send(sock, req.c_str(), (int)req.size(), 0);
        char buf[1024];
        int n = recv(sock, buf, sizeof(buf)-1, 0);
        if(n > 0){
            buf[n] = 0;
            string s(buf);
            // Try extract Server or Title quickly
            smatch m;
            regex rServer("(?i)^Server:\\s*(.+)$", regex_constants::multiline);
            if(regex_search(s, m, rServer)) return "HTTP: " + trim(m[1]);
            regex rTitle("(?is)<title>(.*?)</title>");
            if(regex_search(s, m, rTitle))  return "HTTP: <title> " + trim(m[1]);
            return "HTTP: Open";
        }
        return "HTTP: Open";
    }

    // For SSH/FTP/SMTP etc. they often send a banner first
    char buf[512];
    // short read try
    fd_set rf; FD_ZERO(&rf); FD_SET(sock, &rf);
    timeval tv{0, 150000}; // 150ms
    if(select(sock+1, &rf, nullptr, nullptr, &tv) > 0){
        int n = recv(sock, buf, sizeof(buf)-1, 0);
        if(n > 0){
            buf[n] = 0;
            string s(buf);
            // Single-line banner snippet
            auto pos = s.find('\n');
            if(pos != string::npos) s = s.substr(0, pos);
            s = trim(s);
            if(!s.empty()) return s;
        }
    }
    return "Open";
}

// ----------- ultra-fast TCP scan for one host using epoll -----------
static vector<PortResult> fast_tcp_scan(const string& ip, const vector<int>& ports, int connect_timeout_ms = 200){
    vector<PortResult> results;

    int ep = epoll_create1(0);
    if(ep < 0) return results;

    struct Conn {
        int fd;
        int port;
        bool connected;
    };

    vector<Conn> conns;
    conns.reserve(ports.size());

    // Kick off nonblocking connects
    for(int port : ports){
        int fd = socket(AF_INET, SOCK_STREAM, 0);
        if(fd < 0) continue;
        set_nonblocking(fd);

        sockaddr_in addr{};
        addr.sin_family = AF_INET;
        addr.sin_port = htons(port);
        inet_pton(AF_INET, ip.c_str(), &addr.sin_addr);

        int r = connect(fd, (sockaddr*)&addr, sizeof(addr));
        if(r < 0 && errno != EINPROGRESS){
            close(fd); continue;
        }

        epoll_event ev{};
        ev.events = EPOLLOUT | EPOLLERR | EPOLLHUP;
        ev.data.fd = fd;
        if(epoll_ctl(ep, EPOLL_CTL_ADD, fd, &ev) < 0){
            close(fd); continue;
        }
        conns.push_back({fd, port, false});
    }

    auto start = chrono::steady_clock::now();
    const int MAX_EVENTS = 256;
    epoll_event events[MAX_EVENTS];

    // Poll until timeout
    while(true){
        int remaining = connect_timeout_ms -
            (int)chrono::duration_cast<chrono::milliseconds>(chrono::steady_clock::now() - start).count();
        if(remaining <= 0) break;

        int n = epoll_wait(ep, events, MAX_EVENTS, remaining);
        if(n <= 0) break;

        for(int i=0;i<n;i++){
            int fd = events[i].data.fd;
            int err = 0; socklen_t len = sizeof(err);
            getsockopt(fd, SOL_SOCKET, SO_ERROR, &err, &len);

            // find conn
            auto it = find_if(conns.begin(), conns.end(), [&](const Conn& c){ return c.fd == fd; });
            if(it == conns.end()) { close(fd); continue; }

            if(err == 0){
                // connected! try banner
                string banner = grab_banner(fd, ip, it->port);
                results.push_back({it->port, banner});
            }
            // remove from epoll & close either way
            epoll_ctl(ep, EPOLL_CTL_DEL, fd, nullptr);
            close(fd);
            it->connected = true;
        }
    }

    // Clean up leftovers
    for(auto &c : conns){
        if(!c.connected){
            epoll_ctl(ep, EPOLL_CTL_DEL, c.fd, nullptr);
            close(c.fd);
        }
    }
    close(ep);
    return results;
}

// ----------- main scan pipeline -----------
int main(){
    ios::sync_with_stdio(false);

    // Adjust to your subnet base if needed:
    string base = "192.168.1"; // e.g., 192.168.1 for 192.168.1.0/24
    int firstHost = 1, lastHost = 254;

    cout << "Ultrafast LAN scan on " << base << ".0/24" << endl;

    // 1) Alive sweep (parallel)
    vector<string> alive;
    mutex aliveMu;

    auto sweep_worker = [&](int begin, int end){
        for(int i=begin; i<=end; ++i){
            string ip = base + "." + to_string(i);
            auto [ok, ttl] = ping_alive_ttl(ip);
            if(ok){
                lock_guard<mutex> lk(aliveMu);
                cout << "\033[36m" << ip << " alive\033[0m" << endl;
                alive.push_back(ip);
            }
        }
    };

    unsigned int threadsN = max(2u, thread::hardware_concurrency());
    vector<thread> sweepers;
    int span = (lastHost - firstHost + 1) / threadsN;
    int cur = firstHost;
    for(unsigned int t=0; t<threadsN; ++t){
        int a = cur;
        int b = (t == threadsN-1) ? lastHost : (cur + span - 1);
        cur = b + 1;
        sweepers.emplace_back(sweep_worker, a, b);
    }
    for(auto &th: sweepers) th.join();

    if(alive.empty()){
        cout << "No alive hosts detected." << endl;
        return 0;
    }

    // 2) Per-host fast TCP scan with epoll + banners, OS guess, MAC lookup
    vector<HostInfo> hosts;
    mutex hostsMu;

    auto host_worker = [&](int begin, int end){
        for(int i=begin; i<end; ++i){
            const string& ip = alive[i];
            // TTL for OS guess
            int ttl = -1;
            {
                auto [ok, t] = ping_alive_ttl(ip);
                if(ok) ttl = t;
            }
            string os = guess_os_from_ttl(ttl);

            // MAC (may be empty due to Android perms)
            string mac = mac_lookup(ip);

            // Ultrafast TCP scan
            auto openPorts = fast_tcp_scan(ip, COMMON_TCP_PORTS, 220);

            {
                lock_guard<mutex> lk(hostsMu);
                HostInfo hi;
                hi.ip = ip;
                hi.mac = mac;
                hi.osGuess = os;
                hi.openTcp = move(openPorts);
                // live console summary
                for (auto &p : hi.openTcp) {
                    cout << "\033[32m" << ip << " TCP " << p.port << " -> " << p.banner << "\033[0m" << endl;
                }
                hosts.push_back(move(hi));
            }
        }
    };

    vector<thread> workers;
    int count = (int)alive.size();
    int chunk = max(1, count / (int)threadsN);
    int i = 0;
    for(unsigned int t=0; t<threadsN; ++t){
        int a = i;
        int b = (t == threadsN-1) ? count : min(count, i + chunk);
        i = b;
        workers.emplace_back(host_worker, a, b);
    }
    for(auto &th: workers) th.join();

    // 3) HTML report
    ofstream html("scan_results.html");
    html << "<!doctype html><html><head><meta charset='utf-8'><title>LAN Scan</title>"
            "<style>body{font-family:system-ui,Segoe UI,Arial,sans-serif;padding:16px;background:#0b0e14;color:#e6e6e6}"
            "table{border-collapse:collapse;width:100%;}"
            "th,td{border:1px solid #2a2f3a;padding:8px;vertical-align:top}"
            "th{background:#111826}"
            ".ip{color:#9cdcfe}.ok{color:#7CFC00}.hdr{color:#ffdd88}"
            "</style></head><body>";
    html << "<h1>LAN Scan Results (" << base << ".0/24)</h1>";
    html << "<p>Hosts scanned: " << alive.size() << " | Generated on: ";
    {
        time_t now = time(nullptr);
        html << put_time(localtime(&now), "%Y-%m-%d %H:%M:%S");
    }
    html << "</p>";
    html << "<table><tr><th>IP</th><th>MAC</th><th>OS Guess</th><th>Open TCP Ports (banner)</th></tr>";
    for(const auto& h : hosts){
        html << "<tr>";
        html << "<td class='ip'>" << h.ip << "</td>";
        html << "<td>" << (h.mac.empty() ? "<span class='hdr'>(no-permission/unknown)</span>" : h.mac) << "</td>";
        html << "<td>" << h.osGuess << "</td>";
        html << "<td>";
        if(h.openTcp.empty()){
            html << "<span class='hdr'>None</span>";
        } else {
            for(const auto& p : h.openTcp){
                // escape simple HTML specials in banner
                string b = p.banner;
                for(char& c: b){ if(c=='<') c='['; else if(c=='>') c=']'; }
                html << "<div><b>" << p.port << "</b> : <span class='ok'>" << b << "</span></div>";
            }
        }
        html << "</td></tr>";
    }
    html << "</table></body></html>";
    html.close();

    // 4) CSV report
    ofstream csv("scan_topology.csv");
    csv << "IP,MAC,OS,OpenTCPPorts(Banner)\n";
    for(const auto& h : hosts){
        csv << h.ip << ",";
        csv << (h.mac.empty() ? "" : h.mac) << ",";
        csv << h.osGuess << ",";
        // flatten port:banner pairs (semicolon separated)
        bool first = true;
        for(const auto& p : h.openTcp){
            if(!first) csv << " ; ";
            first = false;
            string b = p.banner;
            for(char& c: b){ if(c==',' || c=='\n' || c=='\r') c=' '; }
            csv << p.port << " " << b;
        }
        csv << "\n";
    }
    csv.close();

    cout << "\n\033[36mDone.\033[0m Reports written:\n"
            "  • scan_results.html\n"
            "  • scan_topology.csv\n";
    cout << "Tip: open HTML in a browser with: termux-open scan_results.html\n";
    return 0;
}
// (code ends above)

