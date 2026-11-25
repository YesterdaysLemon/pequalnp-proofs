// Enumerate chordless cycles with their smallest vertex first.
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <vector>

using M=std::uint64_t;
constexpr int n=42;
M bit(int i){return M(1)<<i;}
std::array<M,n> adj{};
std::vector<int> path,best;
std::array<std::uint64_t,n+1> counts{};
std::uint64_t visits{};

void extend(int start,int last,M chosen,M blocked) {
    ++visits;
    M possible=adj[last]&~chosen&~blocked&~(bit(start)-1);
    for(M t=possible;t;t&=t-1){
        int v=std::countr_zero(t);
        path.push_back(v);
        if(path.size()>=4 && (adj[v]&bit(start))){
            if(path[1]<v){
                ++counts[path.size()];
                if(path.size()>best.size())best=path;
            }
        } else {
            extend(start,v,chosen|bit(v),blocked|(last==start?0:adj[last]));
        }
        path.pop_back();
    }
}

int main(){
    for(int l=0;l<21;++l)for(int d:{0,1,4,14,16}){
        int p=(l+d)%21;
        if(p==0 && l==0)continue;
        adj[p]|=bit(21+l);adj[21+l]|=bit(p);
    }
    for(int v=0;v<n;++v){
        path={v};
        extend(v,v,bit(v),0);
    }
    for(int k=0;k<=n;++k)if(counts[k])std::cout<<k<<" "<<counts[k]<<'\n';
    std::cout<<"longest";
    for(int i:best)std::cout<<" "<<i;
    std::cout<<"\nvisited "<<visits<<'\n';
}
