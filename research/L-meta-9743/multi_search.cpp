// Exact monotone synthesis with simultaneous circuit-size bounds on restricted inputs.
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
struct Wire {
    M table{},zero{},one{};
    bool operator==(const Wire&)const=default;
};
struct WireHash{size_t operator()(const Wire& w)const{
    return (w.table*11400714819323198485ULL ^ w.zero)*1099511628211ULL ^ w.one;
}};
struct Credit {
    std::array<M,4> bits{};
    bool operator==(const Credit&)const=default;
    bool pay(M mask){
        if(mask & ~(bits[0]|bits[1]|bits[2]|bits[3]))return false;
        for(auto &plane:bits){
            M borrow=mask&~plane;
            plane^=mask;mask=borrow;
        }
        return true;
    }
};
struct Key{
    Credit credit;
    std::array<int,26> ids{};int size{},left{};
    bool operator==(const Key&)const=default;
};
struct KeyHash{size_t operator()(const Key& k)const{
    M h=k.left;
    for(auto b:k.credit.bits)h=(h^b)*0x9e3779b97f4a7c15ULL;
    for(int i=0;i<k.size;++i)h=(h^k.ids[i])*1099511628211ULL;
    return h;
}};
struct Gate{int a,b,out;bool product;};
struct Limit{};

class Search{
    int n,k,np,nq;
    M positives,negatives,cap,visits{};
    Credit initial;
    bool impossible{};
    std::vector<Wire> wires;
    std::unordered_map<Wire,int,WireHash> dict;
    std::unordered_set<Key,KeyHash> memo;
    std::vector<int> inputs;
    std::vector<Gate> path;
    std::array<std::array<bool,16>,16> first{};

    static M low(int n){return n==64?~M(0):(M(1)<<n)-1;}
    int intern(Wire w){
        auto [it,fresh]=dict.try_emplace(w,int(wires.size()));
        if(fresh)wires.push_back(w);
        if(wires.size()>1300000)throw Limit{};
        return it->second;
    }
    bool separates(const std::vector<int>& bank)const{
        for(int row=np;row<np+nq;++row){
            M missed=positives;
            for(int i:bank){
                if(!(wires[i].table & (M(1)<<row)))missed &= ~wires[i].table;
                if(!missed)break;
            }
            if(missed)return false;
        }
        return true;
    }
    bool solve(const std::vector<int>& bank,int left,Credit credit){
        if(++visits>cap)throw Limit{};
        for(int id:bank)if(wires[id].table==positives)return true;
        int size=int(bank.size());
        if(!left||size>left+1||!separates(bank))return false;
        Key key;key.size=size;key.left=left;key.credit=credit;
        std::copy(bank.begin(),bank.end(),key.ids.begin());
        std::sort(key.ids.begin(),key.ids.begin()+size);
        if(memo.contains(key))return false;
        for(int i=0;i<size;++i)for(int j=0;j<i;++j){
            if(left==k && !first[i][j])continue;
            Wire a=wires[bank[i]],b=wires[bank[j]];
            M ca=a.zero|a.one,cb=b.zero|b.one;
            for(bool product:{true,false}){
                Wire z=product?Wire{a.table&b.table,a.zero|b.zero,a.one&b.one}
                              :Wire{a.table|b.table,a.zero&b.zero,a.one|b.one};
                if(!(z.table&positives)||(z.table&negatives)==negatives)continue;
                M collapses=(z.zero|z.one)&(ca^cb);
                Credit paid=credit;
                if(!paid.pay(collapses))continue;
                if(std::any_of(bank.begin(),bank.end(),[&](int id){
                    M w=wires[id].table;return !(z.table&~w&positives) && !(w&~z.table&negatives);
                }))continue;
                int out=intern(z);
                path.push_back({bank[i],bank[j],out,product});
                for(unsigned keep=0;keep<4;++keep){
                    if(size-1+std::popcount(keep)>left)continue;
                    Credit nextCredit=paid;
                    if(((keep&1)&&!nextCredit.pay(ca)) || ((keep&2)&&!nextCredit.pay(cb)))continue;
                    std::vector<int> next;next.reserve(size+1);
                    for(int q=0;q<size;++q){
                        if((q==i && !(keep&1))||(q==j && !(keep&2)))continue;
                        next.push_back(bank[q]);
                    }
                    next.push_back(out);
                    if(solve(next,left-1,nextCredit))return true;
                }
                path.pop_back();
            }
        }
        if(memo.size()>170000)memo.clear();
        memo.insert(key);
        return false;
    }
public:
    Search(std::istream& in,M bound):cap(bound){
        int nr,nprobes;
        if(!(in>>n>>k>>np>>nq>>nr>>nprobes)||n<1||n>16||k<0||k>24||np<1||nq<1||np+nq>64||nprobes>64)
            throw std::runtime_error("input bounds");
        positives=low(np);negatives=low(nq)<<np;
        std::vector<Wire> literals(n);
        for(int i=0;i<np+nq;++i){
            int x;in>>x;
            for(int j=0;j<n;++j)if(x&(1<<j))literals[j].table|=M(1)<<i;
        }
        for(int i=0;i<nr;++i){
            int a,b;in>>a>>b;
            if(a<0||a>=b||b>=n)throw std::runtime_error("orbit");
            first[b][a]=true;
        }
        for(int p=0;p<nprobes;++p){
            int slack,yes,no;in>>slack>>yes>>no;
            if(yes&no || slack>15)throw std::runtime_error("probe");
            if(slack<0)impossible=true;
            for(int b=0;b<4;++b)if(slack&(1<<b))initial.bits[b]|=M(1)<<p;
            for(int j=0;j<n;++j){
                if(yes&(1<<j))literals[j].one|=M(1)<<p;
                if(no&(1<<j))literals[j].zero|=M(1)<<p;
            }
        }
        if(!in)throw std::runtime_error("incomplete input");
        for(auto w:literals)inputs.push_back(intern(w));
    }
    void run(){
        const char *status="UNKNOWN";
        try{
            bool found=!impossible && solve(inputs,k,initial);
            status=found?"SAT":"UNSAT";
            if(found){
                auto ids=inputs;
                for(auto g:path){
                    auto at=[&](int x){return std::find(ids.begin(),ids.end(),x)-ids.begin();};
                    std::cout<<ids.size()<<" = "<<(g.product?'&':'|')<<" "<<at(g.a)<<" "<<at(g.b)<<'\n';
                    ids.push_back(g.out);
                }
            }
        }catch(const Limit&){}
        std::cout<<status<<" visits "<<visits<<" wire values "<<wires.size()<<'\n';
    }
};
int main(int argc,char**argv){
    if(argc!=2)return 2;
    Search s(std::cin,std::stoull(argv[1]));s.run();
}
