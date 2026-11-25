// Lower bounds for monotone extensions of the order-three plane promise.
// Every successful return is a lower bound. A failed strategy has no implication.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <limits>
#include <map>
#include <unordered_map>
#include <vector>

using M = uint32_t;
using Key = uint64_t;
constexpr M half = (1u<<13)-1, all = (1u<<26)-1;
int pop(M m) {return std::popcount(m);}
M bit(int i){return 1u<<i;}
std::array<M,26> adj;
std::array<M,1<<13> lhs{},rhs{};
std::array<bool,1<<13> pointsOK{}, linesOK{};
std::vector<std::array<uint16_t,1<<13>> imgs;
std::vector<bool> dual;
struct Relabel {
    std::array<std::array<M,128>,4> table{};
    M apply(M v)const{
        return table[0][v&127]|table[1][(v>>7)&63]|table[2][(v>>13)&127]|table[3][v>>20];
    }
};
std::vector<Relabel> autos;
struct Orbit {M first=all;std::vector<int> keep;};
std::unordered_map<M,Orbit> orbits;
std::unordered_map<Key,Key> canonCache;
M neighbors(M m){return lhs[m&half] | rhs[m>>13];}
bool edge(M m){return (neighbors(m)&m)!=0;}
bool neg(M m){return !edge(m) && pointsOK[m&half] && linesOK[m>>13];}
bool nonconstant(M one,M free){return neg(one) && edge(one|free);}
M image(int i,M m){
    M a=imgs[i][m&half], b=imgs[i][m>>13];
    return dual[i] ? b|(a<<13) : a|(b<<13);
}
Key canonical(M one,M zero){
    if(!autos.empty()){
        Key raw=(Key(one)<<26)|zero;
        if(auto f=canonCache.find(raw);f!=canonCache.end())return f->second;
        auto [it,inserted]=orbits.try_emplace(one);
        auto &orbit=it->second;
        if(inserted){
            for(int g=0;g<int(autos.size());++g){
                M w=autos[g].apply(one);
                if(w<orbit.first){orbit.first=w;orbit.keep.clear();}
                if(w==orbit.first)orbit.keep.push_back(g);
            }
        }
        M t=all;
        for(int g:orbit.keep)t=std::min(t,autos[g].apply(zero));
        Key answer=(Key(orbit.first)<<26)|t;
        if(canonCache.size()<700000)canonCache.emplace(raw,answer);
        return answer;
    }
    Key best=std::numeric_limits<Key>::max();
    for(int i=0;i<int(imgs.size());i++) {
        Key o=Key(image(i,one))<<26;
        if(o<=best)best=std::min(best,o|image(i,zero));
    }
    return best;
}

struct Shape {M mask; std::vector<M> independent; int vertices, cost;};
std::array<std::vector<Shape>,4> shapes;

void paths(std::vector<int> &p,M chosen){
    int n=int(p.size());
    bool cycle=n>=4 && (adj[p.front()]&bit(p.back()));
    if(n>=4 && p.front()<p.back() && (!cycle ||
          (p.front()==*std::min_element(p.begin(),p.end()) && p[1]<p.back()))) {
        int cost= n+(cycle ? (n+1)/2-1 : n/2-2);
        if(cost>=n && cost-n<=3) {
            Shape s{chosen,{},n,cost};
            for(M x=0;x<bit(n);++x){
                M w=0;
                for(int j=0;j<n;++j)if(x&bit(j))w|=bit(p[j]);
                if(!edge(w) && ((w|neighbors(w))&chosen)==chosen)s.independent.push_back(w);
            }
            shapes[cost-n].push_back(std::move(s));
        }
    }
    if(cycle || n==8)return;
    M cand=adj[p.back()]&~chosen;
    while(cand){
        int v=std::countr_zero(cand);cand&=cand-1;
        M contacts=adj[v]&chosen;
        if(contacts & ~(bit(p.front())|bit(p.back())))continue;
        p.push_back(v);paths(p,chosen|bit(v));p.pop_back();
    }
}
void init(){
    for(int l=0;l<13;++l)for(int d:{0,1,3,9}){
        int p=(l+d)%13;adj[l+13]|=bit(p);adj[p]|=bit(l+13);
    }
    for(M s=0;s<=half;++s){
        if(s){int v=std::countr_zero(s);lhs[s]=lhs[s&(s-1)]|adj[v];rhs[s]=rhs[s&(s-1)]|adj[13+v];}
        pointsOK[s]=linesOK[s]=true;
        for(int v=0;v<13;++v){
            if(pop(s&adj[13+v])>2)pointsOK[s]=false;
            if(pop((s<<13)&adj[v])>2)linesOK[s]=false;
        }
    }
    for(int flip:{0,1})for(int mul:{1,3,9})for(int shift=0;shift<13;++shift){
        imgs.emplace_back();dual.push_back(flip!=0);
        auto &tab=imgs.back();tab[0]=0;
        for(M s=1;s<=half;++s){
            int v=std::countr_zero(s);
            int to=(26*13+shift+(flip?-1:1)*mul*v)%13;
            tab[s]=uint16_t(tab[s&(s-1)]|bit(to));
        }
    }
    if(auto path=std::getenv("P3_SYMMETRIES")){
        std::ifstream file(path,std::ios::binary);std::array<unsigned char,26> perm{};
        while(file.read(reinterpret_cast<char*>(perm.data()),26)){
            M covered=0;
            for(int i=0;i<26;i++){
                if(perm[i]>=26)throw std::runtime_error("bad vertex image");
                covered|=bit(perm[i]);
                for(int j=0;j<i;j++)if(bool(adj[i]&bit(j))!=bool(adj[perm[i]]&bit(perm[j])))
                    throw std::runtime_error("permutation changes incidence");
            }
            if(covered!=all)throw std::runtime_error("invalid permutation");
            autos.emplace_back();
            for(int block=0;block<4;block++){
                int width=block%2?6:7,offset=std::array<int,4>{0,7,13,20}[block];
                auto &tbl=autos.back().table[block];
                for(int m=1;m<(1<<width);m++)tbl[m]=tbl[m&(m-1)]|bit(perm[offset+std::countr_zero(unsigned(m))]);
            }
        }
        if(autos.empty()||!file.eof()||file.gcount())throw std::runtime_error("incomplete group file");
    }
    for(int i=0;i<26;++i){std::vector<int> p{i};paths(p,bit(i));}
}

enum Rule {None, Support, Core, Literals, Fanout, Fix0, Fix1, Two};
struct RuleData {Rule kind=None;M arg=0;};
struct Range {int pass=0,fail=100;RuleData why;};
std::unordered_map<Key,Range> mem;
std::unordered_map<M,std::array<std::vector<M>,4>> allowed;
int fallback=0;uint64_t visits=0;

M singles(M one,M free){
    M eligible=0;
    for(M t=free;t;t&=t-1){M b=t&-t;if(neg(one|b))eligible|=b;}
    return eligible;
}
M closure(M seed,M free,M eligible){
    for(;;){
        M more=neighbors(seed&eligible)&free&~seed;
        if(!more)return seed;
        seed|=more;
    }
}
M core(M one,M free,int need,M eligible){
    int n=pop(free);
    if(n+3<need||closure(free&-free,free,free)!=free)return 0;
    auto [it, inserted]=allowed.try_emplace(one);
    if(inserted){
        M excluded=one|neighbors(one);
        for(int j=0;j<4;++j)for(auto const &s:shapes[j]){
            if((s.mask&excluded)==0 && std::all_of(s.independent.begin(),s.independent.end(),[&](M w){return neg(one|w);}))
                it->second[j].push_back(s.mask);
        }
    }
    for(int excess=3;excess>=0 && n+excess>=need;--excess)for(M s:it->second[excess]){
        if((s&free)==s && (free==eligible || closure(s,free,eligible)==free))return s;
    }
    return 0;
}

// A context supplies one positive and one negative among three cofactors.
// Each of the four possible excluded cofactors needs such a disagreement.
bool separated(M one,M free,int p,int q){
    M a=bit(p), b=bit(q);
    unsigned witnessed=0;
    M where=(adj[p]|adj[q])&free&~(a|b);
    M ctx=0;
    for(;;){
        M base=one|ctx;
        unsigned pos=0,no=0;
        for(int k=0;k<4;++k){
            M row=base|(k&1?a:0)|(k&2?b:0);
            if(edge(row))pos|=1u<<k;
            if(neg(row))no|=1u<<k;
        }
        for(int skip=0;skip<4;++skip)if((pos&~(1u<<skip)) && (no&~(1u<<skip)))witnessed|=1u<<skip;
        if(witnessed==15)return true;
        if(!where)break;
        ctx=where&-where;where-=ctx;
    }
    return false;
}

bool prove(M,M,int);
bool augment(int p, M lines, M &seen, std::array<int,13> &owner){
    for(M t=(adj[p]>>13)&lines&~seen;t;t&=t-1){
        int l=std::countr_zero(t);
        if(seen&bit(l))continue;
        seen|=bit(l);
        if(owner[l]<0 || augment(owner[l],lines,seen,owner)){owner[l]=p;return true;}
    }
    return false;
}
int constructive_upper(M one,M free){
    M hit=neighbors(one)&free;
    M rest=free&~hit, lines=rest>>13;
    int edges=0,matching=0;
    std::array<int,13> owner;owner.fill(-1);
    for(M t=rest&half;t;t&=t-1){
        int p=std::countr_zero(t);
        edges+=pop((adj[p]>>13)&lines);
        M seen=0;if(augment(p,lines,seen,owner))++matching;
    }
    // A bipartite minimum vertex cover gives disjointly assigned stars.
    return std::max(0,pop(hit)+edges+matching-1);
}
bool step(M one,M zero,int need,RuleData &r){
    M free=all&~(one|zero);
    if(!nonconstant(one,free))return need<=0;
    M hit=free&neighbors(one);
    if(hit && nonconstant(one,free&~hit)){r={Literals,hit};return prove(one,zero|hit,need-pop(hit));}
    M eligible=singles(one,free);
    M essential=(neighbors(eligible)|neighbors(one))&free;
    if(pop(essential)-1>=need){r={Support,essential};return true;}
    if(constructive_upper(one,free)<need)return false;
    if(!hit)if(M s=core(one,free,need,eligible)){r={Core,s};return true;}
    M bad=0;
    for(M t=free;t;t&=t-1){
        M p=t&-t;
        if(!nonconstant(one,free^p)||!nonconstant(one|p,free^p))bad|=p;
        for(M u=t^p;u;u&=u-1){
            M q=u&-u;
            if(!separated(one,free,std::countr_zero(p),std::countr_zero(q)))bad|=p|q;
        }
    }
    if(!bad && essential){
        bool ok=true;
        for(M t=free;t && ok;t&=t-1){
            M b=t&-t;
            ok=prove(one,zero|b,need-3) && prove(one|b,zero,need-4);
        }
        if(ok){r={Fanout,0};return true;}
    }
    if(fallback){
        if(fallback>=2)for(M pool:{essential&bad,essential&~bad}){
            for(M t=pool;t;t&=t-1){
                M b=t&-t;
                if(nonconstant(one,free^b) && nonconstant(one|b,free^b) &&
                   prove(one|b,zero,need-2) && prove(one,zero|b,need-2)){
                    r={Two,b};return true;
                }
            }
        }
        M choices=(bad && fallback<3 ? bad : free)&essential;
        for(;choices;choices&=choices-1){
            M b=choices&-choices;
            if(nonconstant(one,free^b)&&prove(one,zero|b,need-1)){r={Fix0,b};return true;}
            if(nonconstant(one|b,free^b)&&prove(one|b,zero,need-1)){r={Fix1,b};return true;}
        }
    }
    return false;
}
bool prove(M one,M zero,int need){
    ++visits;
    if(need<=0)return true;
    Key k=canonical(one,zero);
    if(auto it=mem.find(k);it!=mem.end()){
        if(need<=it->second.pass)return true;
        if(need>=it->second.fail)return false;
    }
    RuleData why;
    bool good=step(k>>26,k&all,need,why);
    if(mem.size()<650000){
        auto &r=mem[k];
        if(good && need>r.pass){r.pass=need;r.why=why;}else if(!good)r.fail=std::min(r.fail,need);
    }
    return good;
}
void collect(M one,M zero,int need,std::map<Key,Range> &out){
    if(need<=0)return;
    Key k=canonical(one,zero);
    if(out.contains(k))return;
    Range r=mem.at(k);
    if(r.pass<need)throw std::runtime_error("missing certificate");
    out.emplace(k,r);
    one=k>>26;zero=k&all;M free=all&~(one|zero),x=r.why.arg;
    switch(r.why.kind){
    case Literals:collect(one,zero|x,r.pass-pop(x),out);break;
    case Fix0:collect(one,zero|x,r.pass-1,out);break;
    case Fix1:collect(one|x,zero,r.pass-1,out);break;
    case Two:collect(one|x,zero,r.pass-2,out);collect(one,zero|x,r.pass-2,out);break;
    case Fanout:
        for(M t=free;t;t&=t-1){M b=t&-t;collect(one,zero|b,r.pass-3,out);collect(one|b,zero,r.pass-4,out);}
        break;
    case Support:case Core:break;
    default:throw std::runtime_error("invalid certificate");
    }
}
int main(int argc,char **argv){
    if(argc!=4 && argc!=5)return 2;
    init();fallback=std::atoi(argv[3]);
    for(int k=std::atoi(argv[1]);k<=std::atoi(argv[2]);++k){
        bool ok=prove(0,0,k);
        std::cout<<"lower "<<k<<" established "<<ok<<" nodes "<<mem.size()<<" calls "<<visits<<std::endl;
        if(!ok)break;
        if(argc==5){
            std::map<Key,Range> out;collect(0,0,k,out);
            std::ofstream f(std::string(argv[4])+std::to_string(k)+".txt");
            for(auto [key,r]:out)f<<(key>>26)<<' '<<(key&all)<<' '<<r.pass<<' '<<r.why.kind<<' '<<r.why.arg<<'\n';
            std::cout<<"certificate rows "<<out.size()<<std::endl;
        }
    }
}
