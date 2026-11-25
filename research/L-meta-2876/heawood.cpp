// Bounded monotone circuit search on the Heawood graph. Every candidate with
// exact boundary behavior is independently evaluated on all 16384 inputs.
#include <algorithm>
#include <array>
#include <bit>
#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <numeric>
#include <random>
#include <stdexcept>
#include <vector>

using Bits = std::uint64_t;
constexpr int n = 14, maxGates = 36;
constexpr std::array<int,7> adjacency{1408,8832,12544,6272,11264,5632,2816};
struct Gate { int a, b; bool conjunction; };
struct Circuit { std::vector<Gate> gates; };
using Values = std::array<Bits,n+maxGates>;
using Clock = std::chrono::steady_clock;

bool edge(int input) {
    for (int p=0; p<7; ++p)
        if ((input & (1<<p)) && (input & adjacency[p])) return true;
    return false;
}

struct Search {
    std::mt19937_64 engine;
    std::vector<int> rows;
    Values inputs{};
    Bits target{}, domain{};
    int bestErrors = 59;
    std::uint64_t moves = 0;

    explicit Search(std::uint64_t seed) : engine(seed) {
        for (int m=0; m<(1<<n); ++m)
            if (edge(m) && std::popcount(unsigned(m))==2) rows.push_back(m);
        target = (Bits(1)<<rows.size())-1;
        for (int m=0; m<(1<<n); ++m) {
            if (edge(m)) continue;
            bool maximal=true;
            for (int j=0; j<n; ++j)
                if (!(m & (1<<j)) && !edge(m | (1<<j))) maximal=false;
            if (maximal) rows.push_back(m);
        }
        if (rows.size()!=58 || std::popcount(target)!=21) throw std::runtime_error("wrong boundary");
        domain=(Bits(1)<<rows.size())-1;
        for (int r=0; r<int(rows.size()); ++r)
            for (int j=0; j<n; ++j)
                if (rows[r] & (1<<j)) inputs[j] |= Bits(1)<<r;
    }

    int pick(int bound) { return std::uniform_int_distribution<int>(0,bound-1)(engine); }
    Bits apply(Gate g, const Values& v) const { return g.conjunction ? v[g.a]&v[g.b] : v[g.a]|v[g.b]; }
    Values evaluate(const Circuit& c) const {
        Values v=inputs;
        for (int i=0; i<int(c.gates.size()); ++i) v[n+i]=apply(c.gates[i],v);
        return v;
    }
    Bits forced(const Circuit& c, const Values& original, int changed, Bits val) const {
        Values v=original;
        v[n+changed]=val;
        for (int i=changed+1; i<int(c.gates.size()); ++i) v[n+i]=apply(c.gates[i],v);
        return v[n+c.gates.size()-1];
    }
    int gate(Circuit& c, int a, int b, bool conjunction) {
        c.gates.push_back({a,b,conjunction});
        return n+int(c.gates.size())-1;
    }
    int any(Circuit& c, std::vector<int> list) {
        std::shuffle(list.begin(),list.end(),engine);
        while (list.size()>1) {
            std::swap(list[pick(list.size())],list.back());
            int a=list.back(); list.pop_back();
            std::swap(list[pick(list.size())],list.back());
            int b=list.back(); list.pop_back();
            list.push_back(gate(c,a,b,false));
        }
        return list[0];
    }
    Circuit start(int size) {
        Circuit c;
        std::array<int,7> order{}; std::iota(order.begin(),order.end(),0);
        std::shuffle(order.begin(),order.end(),engine);
        bool dual=pick(2);
        std::vector<int> terms;
        for (int i : order) {
            std::vector<int> neighbors;
            for (int j=0; j<7; ++j) {
                if (dual && (adjacency[j] & (1<<(i+7)))) neighbors.push_back(j);
                if (!dual && (adjacency[i] & (1<<(j+7)))) neighbors.push_back(j+7);
            }
            int sum=any(c,neighbors);
            terms.push_back(gate(c,dual ? i+7 : i,sum,true));
        }
        any(c,terms);
        if (c.gates.size()!=27 || evaluate(c)[40]!=target) throw std::runtime_error("bad seed");
        if (size==26) {
            int removed=pick(26), old=n+removed;
            int bypass=pick(2) ? c.gates[removed].a : c.gates[removed].b;
            c.gates.erase(c.gates.begin()+removed);
            for (auto& g : c.gates) for (int* src : {&g.a,&g.b}) {
                if (*src==old) *src=bypass;
                else if (*src>old) --*src;
            }
        }
        while (int(c.gates.size())<size) {
            int index=pick(c.gates.size());
            Gate extra{pick(n+index),pick(n+index),bool(pick(2))};
            for (auto& g : c.gates) for (int* src : {&g.a,&g.b}) if (*src>=n+index) ++*src;
            c.gates.insert(c.gates.begin()+index,extra);
        }
        return c;
    }
    Circuit trim(const Circuit& c) const {
        std::array<bool,n+maxGates> live{};
        live[n+c.gates.size()-1]=true;
        for (int i=int(c.gates.size())-1; i>=0; --i) if (live[n+i]) {
            live[c.gates[i].a]=true; live[c.gates[i].b]=true;
        }
        std::array<int,n+maxGates> index{}; std::iota(index.begin(),index.end(),0);
        Circuit out;
        for (int i=0; i<int(c.gates.size()); ++i) if (live[n+i]) {
            Gate g=c.gates[i]; g.a=index[g.a]; g.b=index[g.b];
            index[n+i]=n+out.gates.size(); out.gates.push_back(g);
        }
        return out;
    }
    void save(const Circuit& c, const char* path) const {
        for (int m=0; m<(1<<n); ++m) {
            std::array<bool,n+maxGates> v{};
            for (int j=0; j<n; ++j) v[j]=m & (1<<j);
            for (int i=0; i<int(c.gates.size()); ++i) {
                auto g=c.gates[i]; v[n+i]=g.conjunction ? v[g.a]&&v[g.b] : v[g.a]||v[g.b];
            }
            if (v[n+c.gates.size()-1]!=edge(m)) throw std::runtime_error("witness failed full check");
        }
        std::ofstream file(path);
        for (auto g : c.gates) file << (g.conjunction ? "and " : "or ") << g.a << ' ' << g.b << '\n';
        if (!file) throw std::runtime_error("could not write witness");
    }
    int score(Bits error, Bits emphasis, Bits history) const {
        return 2*std::popcount(error)+2*std::popcount(error&emphasis)+std::popcount(error&history);
    }
    void change(Circuit& c, int index, Bits emphasis, Bits history, int slack) {
        int bound=n+index;
        auto v=evaluate(c);
        Bits zero=forced(c,v,index,0), care=zero ^ forced(c,v,index,domain);
        if (!care) {
            c.gates[index]={pick(bound),pick(bound),bool(pick(2))};
            return;
        }
        std::array<int,291> seen{};
        std::array<Gate,291> choices{};
        int best=1000;
        for (int a=0; a<bound; ++a) for (int b=a+1; b<bound; ++b) {
            for (bool op : {false,true}) {
                Gate g{a,b,op};
                Bits error=target ^ (zero | (care & apply(g,v)));
                int cost=score(error,emphasis,history);
                if (cost<best) best=cost;
                if (cost<=best+slack) {
                    if (pick(++seen[cost])==0) choices[cost]=g;
                }
            }
        }
        std::vector<Gate> eligible;
        for (int k=best; k<=best+slack && k<int(seen.size()); ++k)
            if (seen[k]) eligible.push_back(choices[k]);
        if (!eligible.empty()) c.gates[index]=eligible[pick(eligible.size())];
    }

    bool run(int seconds, const char* path) {
        auto end=Clock::now()+std::chrono::seconds(seconds);
        int restarts=0, exactStates=0, bestExact=100;
        while (Clock::now()<end) {
            int size=(++restarts%4==0) ? 29+pick(5) : 26;
            Circuit c=start(size);
            Bits history=0,emphasis=0;
            for (int step=0; step<3500 && Clock::now()<end; ++step) {
                auto v=evaluate(c);
                Bits error=v[n+size-1]^target;
                if (size==26) bestErrors=std::min(bestErrors,std::popcount(error));
                if (!error) {
                    ++exactStates;
                    auto small=trim(c); bestExact=std::min(bestExact,int(small.gates.size()));
                    if (small.gates.size()<=26) { save(small,path); return true; }
                }
                if (step%29==0) { emphasis=error | (engine()&engine()&domain); history=engine()&domain; }
                ++moves;
                if ((step%151)<4) {
                    int index=pick(size), bound=n+index;
                    c.gates[index]={pick(bound),pick(bound),bool(pick(2))};
                } else {
                    int index=pick(size);
                    int slack=pick(100)<15 ? 2+pick(6) : 0;
                    change(c,index,emphasis,history,slack);
                }
            }
        }
        std::cout << "moves " << moves << ", restarts " << restarts << ", best boundary errors at 26 gates "
                  << bestErrors << ", smallest fully correct live circuit " << bestExact
                  << ", exact-state visits " << exactStates << '\n';
        return false;
    }
};
int main(int argc,char** argv) {
    if (argc!=4) return 2;
    Search search(std::strtoull(argv[2],nullptr,10));
    if (search.run(std::atoi(argv[1]),argv[3])) std::cout << "WITNESS VERIFIED ON ALL 16384 INPUTS\n";
}
