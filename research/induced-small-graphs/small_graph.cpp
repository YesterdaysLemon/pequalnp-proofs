// Exact binary-gate search on an explicitly supplied graph with at most six vertices.
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
std::vector<std::array<int,2>> E;
int vertexCount;

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
                else if (operationCount >= 4) bad &= w;
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
            std::array<Word,5> ops = {a & b, a | b, a & ~b, b & ~a, a ^ b};
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
    Search(int mask, const std::array<int,128> &known, uint64_t cap, int domainLimit, int operations)
      : limit(cap), operationCount(operations) {
        bool monotone = operations == 2;
        std::vector<int> labels;
        for (int i=0;i<vertexCount;++i) if (mask>>i&1) labels.push_back(i);
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
        for (int s=1;s<(1<<vertexCount);++s) {
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
    if (argc!=5) {
        std::cerr << "Usage: small_graph VERTICES EDGE_MASK mono|full NODE_LIMIT\n";
        return 2;
    }
    vertexCount=std::stoi(argv[1]);
    auto edges=std::stoull(argv[2]);
    std::string basis=argv[3];
    uint64_t limit=std::stoull(argv[4]);
    if (vertexCount<2 || vertexCount>6 || !limit || (basis!="mono" && basis!="full")) return 2;
    unsigned bit=0;
    for (int j=1;j<vertexCount;++j) for (int i=0;i<j;++i,++bit)
        if (edges & (1ULL<<bit)) E.push_back({i,j});
    int whole=(1<<vertexCount)-1;
    if ((edges>>bit) || essential(whole)!=whole) return 2;
    std::array<int,128> lower{};
    for (int n=2;n<=vertexCount;++n) for (int mask=1;mask<=whole;++mask) {
        if (std::popcount(unsigned(mask))!=n || essential(mask)!=mask) continue;
        int start=n-1;
        for (int s=1;s<mask;++s) if ((s&mask)==s && lower[s]>0)
            start=std::max(start,lower[s]+std::popcount(unsigned(mask^s)));
        lower[mask]=start;
        for (int k=start;k<=16;++k) {
            Search checker(mask,lower,limit,12,basis=="mono"?2:5);
            int verdict=checker.run(mask,k);
            if (verdict!=0) break;
            lower[mask]=k+1;
        }
        std::cout << "lower " << mask << ' ' << lower[mask] << std::endl;
    }
}
