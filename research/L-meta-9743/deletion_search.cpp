// Bounded monotone circuits subject to loss limits when a single vertex is deleted.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <unordered_map>
#include <unordered_set>
#include <vector>

using M=std::uint64_t;
using V=std::uint32_t;
struct Wire { M truth; V must; bool operator==(const Wire&)const=default; };
struct WH { size_t operator()(Wire w)const{return w.truth ^ (M(w.must)*0x9e3779b97f4a7c15ULL);} };
struct Key {
    M credits{}; std::array<int,26> bank{}; int count{},budget{};
    bool operator==(const Key&)const=default;
};
struct KH {size_t operator()(const Key&k)const{
    M h=k.credits^(k.budget*71);
    for(int i=0;i<k.count;++i)h=(h^k.bank[i])*1099511628211ULL;
    return h;
}};
struct Limit {};
struct Gate {int a,b,z;bool product;};

class Synthesis {
    int n,k,pc,nc;
    M pBits,nBits,initialCredit{};
    std::array<std::array<bool,16>,16> first{};
    std::vector<Wire> ws;
    std::unordered_map<Wire,int,WH> known;
    std::unordered_set<Key,KH> memo;
    std::vector<int> base;
    std::vector<Gate> path;
    M visits{},cap;
    static M low(int j){return j==64?~M(0):(M(1)<<j)-1;}
    int id(Wire w){
        auto [it,newOne]=known.try_emplace(w,int(ws.size()));
        if(newOne)ws.push_back(w);
        if(ws.size()>1000000)throw Limit{};
        return it->second;
    }
    bool separates(const std::vector<int>& bank) const {
        for(int j=pc;j<pc+nc;++j){
            M missed=pBits;
            for(int i:bank){
                if(!(ws[i].truth & (M(1)<<j)))missed&=~ws[i].truth;
                if(!missed)break;
            }
            if(missed)return false;
        }
        return true;
    }
    bool go(const std::vector<int>& bank,int left,M credit){
        if(++visits>cap)throw Limit{};
        int size=int(bank.size());
        for(int i:bank)if(ws[i].truth==pBits)return true;
        if(!left || size>left+1)return false;
        std::array<int,16> vanishes{};
        for(int i:bank)for(V t=ws[i].must;t;t&=t-1)++vanishes[std::countr_zero(t)];
        V exhausted=0;
        for(int v=0;v<n;++v){
            int available=(credit>>(4*v))&15;
            if(available<vanishes[v])return false;
            if(!available)exhausted|=V(1)<<v;
        }
        if(!separates(bank))return false;
        Key key;key.credits=credit;key.count=size;key.budget=left;
        std::copy(bank.begin(),bank.end(),key.bank.begin());
        std::sort(key.bank.begin(),key.bank.begin()+size);
        if(memo.contains(key))return false;
        for(int i=0;i<size;++i)for(int j=0;j<i;++j){
            if(left==k && !first[i][j])continue;
            Wire a=ws[bank[i]],b=ws[bank[j]];
            V consumed=a.must|b.must;
            if(consumed&exhausted)continue;
            M cost=0;
            for(V t=consumed;t;t&=t-1)cost|=M(1)<<(4*std::countr_zero(t));
            for(bool product:{true,false}){
                Wire z=product?Wire{a.truth&b.truth,consumed}:Wire{a.truth|b.truth,a.must&b.must};
                if(!(z.truth&pBits) || (z.truth&nBits)==nBits)continue;
                if(std::any_of(bank.begin(),bank.end(),[&](int id){
                    M w=ws[id].truth;return !(z.truth&~w&pBits) && !(w&~z.truth&nBits);
                }))continue;
                int out=id(z);
                path.push_back({bank[i],bank[j],out,product});
                for(unsigned keep=0;keep<4;++keep){
                    if(size-1+std::popcount(keep)>left)continue;
                    std::vector<int> next;next.reserve(size+1);
                    for(int h=0;h<size;++h){
                        if((i==h && !(keep&1)) || (j==h && !(keep&2)))continue;
                        next.push_back(bank[h]);
                    }
                    next.push_back(out);
                    if(go(next,left-1,credit-cost))return true;
                }
                path.pop_back();
            }
        }
        if(memo.size()>170000)memo.clear();
        memo.insert(key);return false;
    }
public:
    Synthesis(std::istream& in,M limit):cap(limit){
        int r;
        if(!(in>>n>>k>>pc>>nc>>r)||n<1||n>16||k<0||k>24||pc<1||nc<1||pc+nc>64)throw std::runtime_error("limits");
        pBits=low(pc);nBits=low(nc)<<pc;
        std::vector<int> rows(pc+nc);
        for(int &w:rows)in>>w;
        for(int v=0;v<n;++v){
            int x;in>>x;
            if(x<0||x>15)throw std::runtime_error("deletion allowance");
            initialCredit|=M(x)<<(4*v);
            M truth=0;
            for(int i=0;i<pc+nc;++i)if(rows[i]&(1<<v))truth|=M(1)<<i;
            base.push_back(id({truth,V(1)<<v}));
        }
        while(r--){
            int a,b;in>>a>>b;
            if(a<0||a>=b||b>=n)throw std::runtime_error("first gate");
            first[b][a]=true;
        }
        if(!in)throw std::runtime_error("incomplete data");
    }
    void run(){
        const char *res="UNKNOWN";
        try{
            bool found=go(base,k,initialCredit);
            res=found?"SAT":"UNSAT";
            if(found){
                auto indices=base;
                for(auto g:path){
                    auto at=[&](int i){return std::find(indices.begin(),indices.end(),i)-indices.begin();};
                    std::cout<<indices.size()<<" = "<<(g.product?'&':'|')<<" "<<at(g.a)<<" "<<at(g.b)<<'\n';
                    indices.push_back(g.z);
                }
            }
        }catch(const Limit&){}
        std::cout<<res<<" visits "<<visits<<" wire values "<<ws.size()<<'\n';
    }
};
int main(int argc,char**argv){
    if(argc!=2)return 2;
    Synthesis task(std::cin,std::stoull(argv[1]));task.run();
}
