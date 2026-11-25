// Exact bounded circuit synthesis for nonconstant monotone truth tables with two through six essential inputs.
// The signed and full bases have free complements. Fan-out is unrestricted.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <stdexcept>
#include <utility>
#include <string>
#include <unordered_set>
#include <vector>

using Word = uint64_t;
using Bank = std::vector<Word>;
using Debts = std::vector<uint8_t>;
uint64_t table;
int vertexCount;
bool value(int row) { return (table >> row) & 1; }

struct Domain {
    Word rows;
    Word anchor;
    int lower;
    Bank freeInputs;
};

std::vector<std::pair<Word,int>> priorDomains;
Word project(Word wire, const Domain &d) {
    return ((wire & d.anchor) ? ~wire : wire) & d.rows;
}

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
        for (auto w : key.bank) mix(w);
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
                if (!project(w,domains[i]) && ++required > remaining) return false;
            if (required > remaining) return false;
        }
        return separate(bank);
    }
    Debts advance(const Debts &debt, const Bank &bank, Word z) const {
        auto next = debt;
        for (size_t i=0; i<next.size(); ++i) {
            if (next[i] == 0) continue;
            const auto &d = domains[i];
            Word w = project(z,d);
            if (!w || std::find(d.freeInputs.begin(), d.freeInputs.end(), w) != d.freeInputs.end())
                continue;
            if (std::any_of(bank.begin(),bank.end(),[&](Word x){return project(x,d) == w;}))
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
    Search(uint64_t cap, int domainLimit, int operations)
      : limit(cap), operationCount(operations) {
        bool monotone = operations == 2;
        int n=vertexCount, rows=1<<n;
        inputs.resize(n);
        for (int r=0;r<rows;++r) {
            for (int i=0;i<n;++i) if (r>>i&1) inputs[i] |= Word(1)<<r;
            if (value(r)) {
                target |= Word(1)<<r;
                bool minimal=true;
                for (int i=0;i<n;++i) if ((r>>i&1) && value(r^(1<<i))) minimal=false;
                if (!monotone || minimal) positiveRows |= Word(1)<<r;
            } else {
                bool maximal=true;
                for (int i=0;i<n;++i) if (!(r>>i&1) && !value(r|(1<<i))) maximal=false;
                if (!monotone || maximal) {
                    negative.push_back(r);
                    negativeRows |= Word(1)<<r;
                }
            }
        }
        for (auto [rows,lower]:priorDomains) {
            Domain d{rows,rows & (Word(0)-rows),lower,{}};
            for (auto w:inputs) if (Word v=project(w,d);v) d.freeInputs.push_back(v);
            domains.push_back(std::move(d));
        }
        std::stable_sort(domains.begin(),domains.end(),[&](const Domain &a,const Domain &b) {
            auto score=[&](const Domain &d) {
                int zeros=0;
                for (auto w:inputs) zeros+=project(w,d)==0;
                return d.lower+zeros;
            };
            if (score(a)!=score(b)) return score(a)>score(b);
            return a.lower>b.lower;
        });
        if (int(domains.size())>domainLimit) domains.resize(domainLimit);
        std::vector<int> p;
        for (int i=0;i<n;++i) p.push_back(i);
        do {
            bool ok=true;
            for (int r=0;r<rows && ok;++r) {
                int moved=0;
                for (int j=0;j<n;++j) if (r>>j&1) moved |= 1<<p[j];
                ok=value(r)==value(moved);
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
    if (argc!=8) {
        std::cerr << "Usage: refine INPUTS HEX_TABLE mono|signed|full LOW HIGH DOMAIN_LIMIT NODE_LIMIT\n";
        return 2;
    }
    vertexCount=std::stoi(argv[1]);
    if (vertexCount<2 || vertexCount>6) return 2;
    int whole=(1<<vertexCount)-1;
    table=std::stoull(argv[2],nullptr,16);
    std::string basis=argv[3];
    int low=std::stoi(argv[4]), high=std::stoi(argv[5]), domains=std::stoi(argv[6]);
    auto limit=std::stoull(argv[7]);
    if ((whole<63 && (table>>(whole+1))) || value(0) || !value(whole) || low<0 || high>18 || domains<0 || !limit) return 2;
    if (basis!="mono" && basis!="signed" && basis!="full") return 2;
    int dependent=0;
    for (int r=0;r<=whole;++r) for (int i=0;i<vertexCount;++i) if (!(r & (1<<i))) {
        if (value(r) && !value(r|(1<<i))) return 2;
        if (value(r)!=value(r|(1<<i))) dependent |= 1<<i;
    }
    if (dependent!=whole) return 2;
    std::string mask; int bound;
    while (std::cin >> mask >> bound) {
        Word rows=std::stoull(mask,nullptr,16);
        if ((whole<63 && (rows>>(whole+1))) || !rows || bound<0 || bound>16 || !(rows&table) || !(rows&~table)) return 2;
        priorDomains.push_back({rows,bound});
    }
    for (int k=low;k<=high;++k) {
        Search checker(limit,domains,basis=="mono"?2:(basis=="signed"?4:5));
        if (checker.run(whole,k)!=0) break;
    }
}
