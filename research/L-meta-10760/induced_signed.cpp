// Exact signed binary-gate search on the induced subgraphs of L-meta-10760.
// Complementing any wire is free. All circuits have arbitrary fan-out.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <stdexcept>
#include <string>
#include <unordered_set>
#include <vector>

using Word = unsigned __int128;
using Bank = std::vector<Word>;
using Debts = std::vector<uint8_t>;
constexpr int E[][2] = {{0,2},{1,3},{0,4},{1,4},{2,4},{0,5},{1,5},{3,5},{0,6},{2,6},{3,6},{5,6}};

int essential(int mask) {
    int used = 0;
    for (auto &edge : E) {
        int pair = (1 << edge[0]) | (1 << edge[1]);
        if ((mask & pair) == pair) used |= pair;
    }
    return used;
}

struct Domain {
    Word rows;
    int vertices;
    int lower;
    Bank freeInputs;
};

struct Key {
    Bank bank;
    Debts debt;
    int left;
    bool operator==(const Key &) const = default;
};
struct Hash {
    size_t operator()(const Key &key) const {
        uint64_t h = key.left;
        auto mix = [&](uint64_t x) { h = (h ^ x) * 1099511628211ULL; };
        for (auto w : key.bank) { mix(uint64_t(w)); mix(uint64_t(w >> 64)); }
        for (auto d : key.debt) mix(d);
        return h;
    }
};
struct Limit {};
struct Gate { int op; Word a, b, z; };

class Search {
    Bank inputs;
    Word target = 0;
    Word positiveRows = 0;
    Word negativeRows = 0;
    std::vector<int> negative;
    std::vector<Domain> domains;
    std::vector<std::vector<int>> perms;
    std::unordered_set<Key, Hash> dead;
    uint64_t limit, visits = 0;
    int operationCount;
    std::vector<Gate> path;
    bool separate(const Bank &bank) const {
        for (auto r : negative) {
            Word bad = positiveRows;
            for (Word w : bank) {
                if (!(w >> r & 1)) bad &= ~w;
                else if (operationCount == 4) bad &= w;
                if (!bad) break;
            }
            if (bad) return false;
        }
        return true;
    }
    bool feasible(int remaining, const Bank &bank, const Debts &debt) const {
        if (int(bank.size()) > remaining + 1) return false;
        for (size_t i = 0; i < debt.size(); ++i) {
            if (debt[i] + int(bank.size()) <= remaining) continue;
            int required = debt[i];
            for (auto w : bank)
                if (!(w & domains[i].rows) && ++required > remaining) return false;
            if (required > remaining) return false;
        }
        return separate(bank);
    }
    Debts advance(const Debts &debt, const Bank &bank, Word z) const {
        auto next = debt;
        for (size_t i=0; i<next.size(); ++i) {
            if (next[i] == 0) continue;
            const auto &d = domains[i];
            Word w = z & d.rows;
            if (!w || std::find(d.freeInputs.begin(), d.freeInputs.end(), w) != d.freeInputs.end())
                continue;
            if (std::any_of(bank.begin(),bank.end(),[&](Word x){return (x & d.rows) == w;}))
                continue;
            --next[i];
        }
        return next;
    }
    bool dfs(int k, const Bank &bank, const Debts &debt) {
        if (++visits > limit) throw Limit{};
        if (std::find(bank.begin(),bank.end(),target) != bank.end()) return true;
        if (!k || !feasible(k,bank,debt)) return false;
        Key key{bank,debt,k};
        std::sort(key.bank.begin(),key.bank.end());
        if (dead.contains(key)) return false;
        for (int i=0;i<int(bank.size());++i) for (int j=i+1;j<int(bank.size());++j) {
            if (path.empty() && std::any_of(perms.begin(),perms.end(),[&](const auto &p) {
                return std::minmax(p[i],p[j]) < std::minmax(i,j); })) continue;
            Word a = bank[i], b = bank[j];
            std::array<Word,4> ops = {a & b, a | b, a & ~b, b & ~a};
            for (int op=0;op<operationCount;++op) {
                Word z=ops[op];
                if (!z || std::find(bank.begin(),bank.end(),z) != bank.end()) continue;
                if (operationCount==2) {
                    // Replacing z by a dominating wire preserves acceptance of
                    // every minimal positive row and rejection of every maximal
                    // negative row throughout a monotone continuation.
                    auto dominates=[&](Word w) {
                        return !(z & ~w & positiveRows) && !(w & ~z & negativeRows);
                    };
                    if (dominates(0) || dominates(~Word(0)) ||
                        std::any_of(bank.begin(),bank.end(),dominates)) continue;
                }
                auto nextDebt=advance(debt,bank,z);
                path.push_back({op,a,b,z});
                for (int keep=0;keep<4;++keep) {
                    if (int(bank.size())-1+std::popcount(unsigned(keep)) > k) continue;
                    Bank child;
                    child.reserve(bank.size()+1);
                    for (int v=0;v<int(bank.size());++v)
                        if ((v!=i || (keep&1)) && (v!=j || (keep&2))) child.push_back(bank[v]);
                    child.push_back(z);
                    if (dfs(k-1,child,nextDebt)) return true;
                }
                path.pop_back();
            }
        }
        if (dead.size() >= 160000) dead.clear();
        dead.insert(std::move(key));
        return false;
    }
public:
    Search(int mask, const std::array<int,128> &known, uint64_t cap, int domainLimit, bool monotone)
      : limit(cap), operationCount(monotone ? 2 : 4) {
        std::vector<int> labels;
        for (int i=0;i<7;++i) if (mask>>i&1) labels.push_back(i);
        int n=int(labels.size()), rows=1<<n;
        inputs.resize(n);
        std::vector<int> expanded(rows);
        for (int r=0;r<rows;++r) {
            for (int i=0;i<n;++i) if (r>>i&1) {
                expanded[r] |= 1<<labels[i];
                inputs[i] |= Word(1)<<r;
            }
            if (essential(expanded[r])) {
                target |= Word(1)<<r;
                if (!monotone || std::popcount(unsigned(r))==2) positiveRows |= Word(1)<<r;
            } else {
                bool maximal=true;
                for (auto v:labels) if (!(expanded[r]>>v&1) && !essential(expanded[r]|(1<<v))) maximal=false;
                if (!monotone || maximal) {
                    negative.push_back(r);
                    negativeRows |= Word(1)<<r;
                }
            }
        }
        for (int s=1;s<128;++s) {
            if ((s&mask)!=s || s==mask || essential(s)!=s || known[s]<=0) continue;
            Word retained=0;
            for (int r=0;r<rows;++r) if (!(expanded[r] & ~s)) retained |= Word(1)<<r;
            Bank free;
            for (auto w : inputs) if (w&retained) free.push_back(w&retained);
            domains.push_back({retained,s,known[s],free});
        }
        std::stable_sort(domains.begin(),domains.end(),[&](const Domain &a,const Domain &b) {
            return a.lower+std::popcount(unsigned(mask ^ a.vertices)) >
                   b.lower+std::popcount(unsigned(mask ^ b.vertices)); });
        if (int(domains.size())>domainLimit) domains.resize(domainLimit);
        std::vector<int> p;
        for (int i=0;i<n;++i) p.push_back(i);
        do {
            bool ok=true;
            for (int i=0;i<n&&ok;++i) for (int j=0;j<i&&ok;++j) {
                int original=(1<<labels[i])|(1<<labels[j]);
                int moved=(1<<labels[p[i]])|(1<<labels[p[j]]);
                ok=bool(essential(original))==bool(essential(moved));
            }
            if (ok) perms.push_back(p);
        } while (std::next_permutation(p.begin(),p.end()));
    }
    int run(int mask, int k) {
        Debts debt;
        for (const auto &d: domains) debt.push_back(d.lower);
        int verdict;
        try { verdict=dfs(k,inputs,debt)?1:0; } catch (const Limit &) { verdict=-1; }
        std::cout << mask << " budget " << k << ' ' <<
            (verdict==1?"SAT":verdict==0?"UNSAT":"UNKNOWN") << " visits " << visits;
        if (verdict==1) {
            auto history=inputs;
            std::cout << " gates";
            for (const auto &g:path) {
                auto ia=std::find(history.begin(),history.end(),g.a)-history.begin();
                auto ib=std::find(history.begin(),history.end(),g.b)-history.begin();
                std::cout << ' ' << g.op << ',' << ia << ',' << ib;
                history.push_back(g.z);
            }
            if (std::find(history.begin(),history.end(),target)==history.end()) std::abort();
        }
        std::cout << std::endl;
        return verdict;
    }
};

int main(int argc,char **argv) {
    if (argc!=5) { std::cerr<<"Usage: induced_signed NODE_LIMIT MAX_DOMAINS MAX_CAP_FOR_FULL_GRAPH mono|signed\n"; return 2; }
    uint64_t cap=std::stoull(argv[1]); int domainLimit=std::stoi(argv[2]), fullCap=std::stoi(argv[3]);
    const std::string mode=argv[4];
    if (mode!="mono" && mode!="signed") return 2;
    if (cap==0 || domainLimit<0 || fullCap<0 || fullCap>16) return 2;
    std::array<int,128> lower{};
    for (int n=2;n<=7;++n) for (int mask=1;mask<128;++mask) {
        if (std::popcount(unsigned(mask))!=n || essential(mask)!=mask) continue;
        // Each successive vertex restriction pays one gate only while its input
        // remains essential. Isolated vertices disappear for free, so use only
        // an immediately smaller essential induced subgraph for this shortcut.
        int start=n-1;
        for (int i=0;i<7;++i) if (mask>>i&1) {
            int s=mask^(1<<i);
            if (essential(s)==s && lower[s]>0) start=std::max(start,lower[s]+1);
        }
        lower[mask]=start;
        for (int k=start;k<=(mask==127?fullCap:14);++k) {
            Search checker(mask,lower,cap,domainLimit,mode=="mono");
            int answer=checker.run(mask,k);
            if (answer) break;
            lower[mask]=k+1;
        }
        std::cout << "lower " << mask << ' ' << lower[mask] << std::endl;
    }
}
