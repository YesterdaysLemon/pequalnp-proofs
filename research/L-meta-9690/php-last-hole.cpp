// Search CP derivations from the pair clauses of one hole and its required load >= 2.
// Every premise occurs once. An event multiplies, divides, or shares a previous sum.
#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <numeric>
#include <tuple>
#include <unordered_set>
#include <vector>

constexpr int K = 8;
using Vec = std::array<int,K>;
struct Event { int factor, parent, second; };
class Search {
    int n,events,maxMul,maxDiv;
    std::array<Event,K> ops{};
    Vec depth{};
    std::array<int64_t,K> weight{};
    std::vector<std::pair<int,int>> edges;
    std::array<int,15> color{};
    std::array<uint32_t,6> incident{};
    std::unordered_set<uint32_t> prefixes;
    int row=0, maxCap=0, coefficient=0, lastSlots=0;
    uint64_t patterns=0,viable=0,leaves=0;

    bool fold(Vec v,bool rhs,int &out) const {
        for(int i=events;i>0;--i) {
            auto [f,p,q]=ops[i]; int x=v[i];
            if(f<0) {
                int d=-f;
                if(!rhs && x%d) return false;
                x=x/d-(x%d<0);
            } else x*=f;
            v[p]+=x;
            if(q>=0)v[q]+=x;
        }
        out=v[0];return true;
    }
    void profiles(int left,int minimum,Vec counts,int64_t sum,uint32_t code) {
        if(left) {
            for(int b=minimum;b<=events;++b) {
                if(sum+weight[b]>(maxCap?int64_t(coefficient)*weight[0]:weight[row]))continue;
                ++counts[b];
                profiles(left-1,b,counts,sum+weight[b],code+(1u<<(3*b)));
                --counts[b];
            }
            return;
        }
        if(sum!=(maxCap?int64_t(coefficient)*weight[0]:weight[row]))return;
        if(!maxCap)--counts[row];
        int x;
        if(!fold(counts,false,x)||x!=(maxCap?coefficient:0))return;
        std::vector<uint32_t> parts={0};
        for(int b=0;b<=events;++b) {
            int m=(code>>(3*b)) & 7u;
            size_t old=parts.size();
            for(int a=1;a<=m;++a)
                for(size_t i=0;i<old;++i)parts.push_back(parts[i]+(uint32_t(a)<<(3*b)));
        }
        prefixes.insert(parts.begin(),parts.end());
    }
    bool assign(size_t j,Vec counts) {
        if(j==edges.size()) {
            ++leaves;
            Vec inputs=counts;
            if(!maxCap)++inputs[row];
            for(int i=1;i<=events;++i) {
                ++inputs[ops[i].parent];
                if(ops[i].second>=0)++inputs[ops[i].second];
            }
            for(int i=0;i<=events;++i)if(inputs[i]==0)return false;
            if(!maxCap)counts[row]-=2;
            int x;
            if(!fold(counts,true,x))return false;
            if(maxCap) {
                int total=0;
                for(int v=0;v<n;++v) {
                    Vec raw{};
                    for(int b=0;b<=events;++b)raw[b]=(incident[v]>>(3*b))&7u;
                    int value;
                    if(!fold(raw,false,value))std::abort();
                    total+=value;
                }
                if(lastSlots) {
                    if(lastSlots*x >= (lastSlots+1)*coefficient)return false;
                } else if(total<=(n-1)*x)return false;
                std::cout<<"capacity rhs "<<x<<" coefficient sum "<<total<<"\n";
            } else if(x!=-1)return false;
            std::cout<<"FOUND "<<events<<" auxiliary operations\n";
            for(int i=1;i<=events;++i)std::cout<<"event "<<i<<" "<<ops[i].factor<<" "<<ops[i].parent<<" "<<ops[i].second<<"\n";
            std::cout<<"row "<<row<<"\nedges";
            for(size_t i=0;i<edges.size();++i)std::cout<<" "<<color[i];
            std::cout<<"\n";
            return true;
        }
        auto [u,v]=edges[j];
        int start=(u==0 && j>0)?color[j-1]:0;
        for(int b=start;b<=events;++b) {
            uint32_t step=1u<<(3*b);
            if(!prefixes.count(incident[u]+step)||!prefixes.count(incident[v]+step))continue;
            incident[u]+=step;incident[v]+=step;++counts[b];color[j]=b;
            if(assign(j+1,counts))return true;
            incident[u]-=step;incident[v]-=step;--counts[b];
        }
        return false;
    }
    bool inspect() {
        ++patterns;
        int64_t denom=1,loss=0;
        for(int i=1;i<=events;++i)if(ops[i].factor<0)denom*=(-ops[i].factor);
        weight[0]=denom;
        for(int i=1;i<=events;++i) {
            auto [f,p,q]=ops[i];
            int64_t output=weight[p]+(q<0?0:weight[q]);
            weight[i]=f<0?output/(-f):output*f;
            if(f<0)loss+=output-weight[i];
        }
        int64_t minWeight=*std::min_element(weight.begin(),weight.begin()+events+1);
        if(maxCap) {
            if(lastSlots) {
                for(coefficient=1;coefficient<=maxCap;++coefficient) {
                    if(int64_t(coefficient)*denom<(n-1)*minWeight ||
                       2*lastSlots*loss<=int64_t(n*lastSlots-2*lastSlots-2)*coefficient*denom)continue;
                    prefixes.clear();
                    profiles(n-1,0,{},0,0);
                    if(prefixes.empty())continue;
                    ++viable;
                    if(assign(0,{}))return true;
                }
                return false;
            }
            if(2*(n-1)*loss<=int64_t(n-3)*std::max(int64_t(n)*denom,n*(n-1)*minWeight))return false;
            prefixes.clear();
            for(coefficient=1;coefficient<=maxCap;++coefficient)profiles(n-1,0,{},0,0);
            if(prefixes.empty())return false;
            ++viable;
            return assign(0,{});
        }
        for(row=0;row<=events;++row) {
            if(weight[row]<(n-1)*minWeight || 2*loss<(n-4)*weight[row]+2*denom)continue;
            prefixes.clear();
            profiles(n-1,0,{},0,0);
            if(prefixes.empty())continue;
            ++viable;
            if(assign(0,{}))return true;
        }
        return false;
    }
    bool shapes(int i) {
        if(i>events)return inspect();
        auto next=[&](Event e){
            int h=1+std::max(depth[e.parent],e.second<0?0:depth[e.second]);
            auto key=[](Event a){return std::tuple(a.parent,a.second,a.factor);};
            if(h<depth[i-1] || (i>1 && h==depth[i-1] && key(e)<key(ops[i-1])))return false;
            depth[i]=h;ops[i]=e;return shapes(i+1);
        };
        for(int p=0;p<i;++p){
            for(int d=2;d<=maxDiv;++d)if(next({-d,p,-1}))return true;
            for(int m=2;m<=maxMul;++m)if(next({m,p,-1}))return true;
            for(int q=p+1;q<i;++q)if(next({1,p,q}))return true;
        }
        return false;
    }
public:
    Search(int vertices,int e,int m,int d,int cap,int slots):n(vertices),events(e),maxMul(m),maxDiv(d),maxCap(cap),lastSlots(slots) {
        for(int i=0;i<n;++i)for(int j=i+1;j<n;++j)edges.push_back({i,j});
    }
    void run(){
        bool found=shapes(1);
        std::cout<<(found?"witness":"exhausted")<<" n "<<n<<" extra "<<events<<" multiply "<<maxMul
                 <<" divide "<<maxDiv<<" max-cap-coeff "<<maxCap<<" last-slots "<<lastSlots<<" shapes "<<patterns<<" viable "<<viable<<" leaves "<<leaves<<"\n";
    }
};
int main(int argc,char **argv){
    if(argc<5 || argc>7)return 2;
    int n=std::atoi(argv[1]),k=std::atoi(argv[2]),m=std::atoi(argv[3]),d=std::atoi(argv[4]);
    int cap=argc>=6?std::atoi(argv[5]):0,slots=argc==7?std::atoi(argv[6]):0;
    if(n<3||n>6||k<0||k>=K||m<1||m>16||d<2||d>16||cap<0||cap>32||slots<0||slots>6||(!cap&&slots))return 2;
    Search(n,k,m,d,cap,slots).run();
}
