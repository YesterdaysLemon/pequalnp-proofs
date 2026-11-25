// Exact decision-tree size for ordinary unary PHP(5,4), with row and column symmetries.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <random>
#include <stdexcept>
#include <unordered_map>
#include <vector>

using Rows = std::array<unsigned,5>;
using Key = std::uint64_t;
constexpr int pigeons=5, holes=4;
std::array<std::array<unsigned,256>,24> renameRow{};
std::array<std::array<int,4>,24> permutations{};
std::unordered_map<Key,int> sizes;
std::mt19937 randomizer(164);

void prepare() {
    std::array<int,4> p{0,1,2,3};
    int index=0;
    do {
        permutations[index]=p;
        for(unsigned r=0;r<256;++r) {
            unsigned image=0;
            for(int j=0;j<4;++j) {
                image|=((r>>p[j])&1u)<<j;
                image|=((r>>(4+p[j]))&1u)<<(4+j);
            }
            renameRow[index][r]=image;
        }
        ++index;
    } while(std::next_permutation(p.begin(),p.end()));
}

struct Clause { unsigned pos{},neg{}; };

bool terminal(const Rows& s, Clause* source=nullptr) {
    unsigned occupied=0;
    for(int i=0;i<pigeons;++i) {
        unsigned positive=s[i]>>4;
        if((s[i]&15)==15) {
            if(source) *source={15u<<(4*i),0};
            return true;
        }
        if(unsigned repeated=positive&occupied) {
            if(source) {
                unsigned h=std::countr_zero(repeated);
                int other=0;
                while(!((s[other]>>(4+h))&1u)) ++other;
                *source={0,(1u<<(4*i+h))|(1u<<(4*other+h))};
            }
            return true;
        }
        occupied|=positive;
    }
    return false;
}

Key canonical(const Rows& s) {
    std::array<int,4> sig{};
    for(unsigned r:s) for(int h=0;h<4;++h)
        sig[h]+=((r>>h)&1u)+6*((r>>(4+h))&1u);
    Key best=~Key{0};
    for(int j=0;j<24;++j) {
        const auto &p=permutations[j];
        if(sig[p[0]]>sig[p[1]]||sig[p[1]]>sig[p[2]]||sig[p[2]]>sig[p[3]]) continue;
        Rows sorted;
        for(int i=0;i<5;++i) sorted[i]=renameRow[j][s[i]];
        std::sort(sorted.begin(), sorted.end());
        Key k=0;
        for(unsigned r:sorted) k=(k<<8)|r;
        best=std::min(best,k);
    }
    return best;
}

int optimum(Rows& s) {
    if(terminal(s)) return 1;
    Key key=canonical(s);
    if(auto it=sizes.find(key);it!=sizes.end()) return it->second;
    int best=1<<24;
    for(int i=0;i<5;++i) {
        if(std::find(s.begin(),s.begin()+i,s[i])!=s.begin()+i) continue;
        const unsigned old=s[i],unknown=15&~(old|(old>>4));
        for(unsigned h=0;h<4;++h) if(unknown&(1u<<h)) {
            s[i]=old|(1u<<(4+h));
            int a=optimum(s);
            s[i]=old;
            if(a>=best) continue;
            s[i]=old|(1u<<h);
            int b=optimum(s);
            s[i]=old;
            best=std::min(best,a+b);
        }
    }
    if(best==(1<<24)) throw std::logic_error("Complete assignment without a conflict");
    sizes.emplace(key,best);
    return best;
}

struct Line { Clause c; int a,b,v; };
struct Derivation {
    std::vector<Line> lines;
    std::unordered_map<Key,int> memo;
    bool share=true,learn=false,preferLearned=false,localOrder=true;
    std::array<int,20> priority{};
    Derivation() {
        for(int i=0;i<20;++i) priority[i]=i;
        std::shuffle(priority.begin(),priority.end(),randomizer);
    }
    int add(Clause c,int a=-1,int b=-1,int v=-1) {
        Key k=(Key(c.pos)<<20)|c.neg;
        if(share) if(auto i=memo.find(k);i!=memo.end()) return i->second;
        int j=static_cast<int>(lines.size());
        memo[k]=j; lines.push_back({c,a,b,v});
        return j;
    }
    int learned(const Rows& s) const {
        if(!learn) return -1;
        unsigned pos=0,neg=0;
        for(int i=0;i<5;++i) {
            pos|=(s[i]>>4)<<(4*i);
            neg|=(s[i]&15)<<(4*i);
        }
        for(int j=static_cast<int>(lines.size())-1;j>=0;--j) {
            const auto& c=lines[j].c;
            if((c.pos&~neg)==0 && (c.neg&~pos)==0) return j;
        }
        return -1;
    }
    int build(Rows& s) {
        Clause c;
        if(terminal(s,&c)) return add(c);
        if(int found=learned(s);found>=0) return found;
        int best=preferLearned ? (1<<24) : optimum(s);
        auto vars=priority;
        if(localOrder) std::shuffle(vars.begin(),vars.end(),randomizer);
        int choice=-1;
        for(int v:vars) {
            int i=v/4,h=v%4;
            unsigned old=s[i],mask=1u<<h;
            if((old|(old>>4))&mask) continue;
            s[i]=old|mask;
            int a=preferLearned && learned(s)>=0 ? 0 : optimum(s);
            s[i]=old|(mask<<4);
            int b=preferLearned && learned(s)>=0 ? 0 : optimum(s);
            s[i]=old;
            if(preferLearned) {
                if(a+b<best) {choice=v;best=a+b;}
            } else if(a+b==best) {choice=v;break;}
        }
        if(choice>=0) {
            int v=choice,i=v/4,h=v%4;
            unsigned old=s[i],mask=1u<<h;
            s[i]=old|mask;
            int l=build(s);
            s[i]=old|(mask<<4);
            int r=build(s);
            s[i]=old;
            unsigned pivot=1u<<v;
            Clause low=lines[l].c,high=lines[r].c;
            if(!(low.pos&pivot)) return l;
            if(!(high.neg&pivot)) return r;
            return add({(low.pos^pivot)|high.pos,low.neg|(high.neg^pivot)},l,r,v+1);
        }
        throw std::logic_error("No optimal question");
    }
    std::vector<Line> cone(int root) const {
        std::vector<bool> used(lines.size());
        used[root]=true;
        for(int j=root;j>=0;--j) if(used[j]&&lines[j].a>=0) {
            used[lines[j].a]=true; used[lines[j].b]=true;
        }
        std::vector<int> next(lines.size());
        std::vector<Line> result;
        for(int j=0;j<=root;++j) if(used[j]) {
            next[j]=static_cast<int>(result.size());
            Line l=lines[j];
            if(l.a>=0) {l.a=next[l.a]; l.b=next[l.b];}
            result.push_back(l);
        }
        return result;
    }
};

void save(const std::vector<Line>& p,const char* fname) {
    std::ofstream out(fname);
    out<<"[";
    for(size_t j=0;j<p.size();++j) {
        const auto& l=p[j];
        if(j) out<<",";
        out<<"[["<<l.c.pos<<","<<l.c.neg<<"],";
        if(l.a<0) out<<"null";
        else out<<"["<<l.a<<","<<l.b<<","<<l.v<<"]";
        out<<"]";
    }
    out<<"]\n";
}

int main(int argc,char** argv) {
    if(argc!=3 && argc!=4) return 2;
    prepare();
    Rows initial{};
    std::cout<<"full assignment decision-tree optimum "<<optimum(initial)
             <<" leaves, "<<sizes.size()<<" stored orbits\n"<<std::flush;
    if(argc==4) {
        Derivation tree;
        tree.share=false;
        auto explicitProof=tree.cone(tree.build(initial));
        save(explicitProof,argv[3]);
        std::cout<<"unshared certificate "<<explicitProof.size()<<" lines\n"<<std::flush;
    }
    int best=1000000;
    int trials=std::atoi(argv[1]);
    for(int i=0;i<trials;++i) {
        Derivation d;
        d.localOrder=(i%2==0);
        d.learn=(i%6>=2);
        d.preferLearned=(i%6>=4);
        auto p=d.cone(d.build(initial));
        if(static_cast<int>(p.size())>=best) continue;
        best=static_cast<int>(p.size());
        save(p,argv[2]);
        std::cout<<"tree "<<i+1<<" shared lines "<<best<<"\n"<<std::flush;
    }
}
