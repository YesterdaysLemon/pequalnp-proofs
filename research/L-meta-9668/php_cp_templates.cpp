// Search small cutting-plane proofs of PHP(4,3) by enumerating their shared
// sums, multiplications and divisions. Inequalities are written as a*x <= b.
#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <iostream>
#include <map>
#include <numeric>
#include <set>
#include <string>
#include <tuple>
#include <unordered_map>
#include <vector>

constexpr int N=8;
using Vec=std::array<int,N>;
using Edge=std::array<unsigned char,6>;
using Rows=std::array<unsigned char,4>;
struct Op { int factor=0, parent=0, second=-1; }; // negative factor means division
struct Profile { Vec count{}; Edge example{}; };
using Group=std::map<Rows,std::vector<Profile>>;
const std::array<std::array<int,3>,4> incident={{{0,1,2},{0,3,4},{1,3,5},{2,4,5}}};

class Engine {
    int k, maxMul, maxDiv, stride, shard, booleans;
    uint64_t templates=0, feasible=0, combinationCount=0;
    std::array<Op,N> ops{};
    std::array<int,N> depth{};
    std::array<int64_t,N> weight{};
    int64_t denominator=1, maxLoss=0;
    std::unordered_map<std::string,Group> cache;
    long long floorDiv(long long x,int d) const {return x>=0?x/d:-((-x+d-1)/d);}
    bool fold(Vec values, bool rhs, int &out) const {
        for (int i=k;i>0;--i) {
            auto op=ops[i]; int x=values[i];
            if (op.factor<0) {
                int d=-op.factor;
                if (!rhs && x%d) return false;
                x=int(floorDiv(x,d));
            } else x*=op.factor;
            values[op.parent]+=x;
            if(op.second>=0) values[op.second]+=x;
        }
        out=values[0]; return true;
    }
    bool good(int row,int a,int b,int c,int plus=0,int minus=0) const {
        Vec line{}; --line[row]; ++line[a]; ++line[b]; ++line[c];
        if(plus)++line[plus-1];
        if(minus)--line[minus-1];
        int out;
        return fold(line,false,out) && out==0;
    }
    using Match=std::array<std::array<std::array<unsigned char,N>,N>,N>;
    Group buildGroups(const Match &valid, const Match *special=nullptr,int vertex=-1) const {
        std::map<Rows,std::map<Vec,Edge>> bins;
        const Match &v0=vertex==0?*special:valid,&v1=vertex==1?*special:valid;
        const Match &v2=vertex==2?*special:valid,&v3=vertex==3?*special:valid;
        for(int a=0;a<=k;++a) for(int b=0;b<=k;++b) for(int c=0;c<=k;++c) {
            unsigned r0=v0[a][b][c];
            if(!r0)continue;
            for(int d=0;d<=k;++d)for(int e=0;e<=k;++e){
                unsigned r1=v1[a][d][e]; if(!r1)continue;
                for(int f=0;f<=k;++f) {
                    unsigned r2=v2[b][d][f],r3=v3[c][e][f];
                    if(!r2||!r3)continue;
                    Edge edges{(uint8_t)a,(uint8_t)b,(uint8_t)c,(uint8_t)d,(uint8_t)e,(uint8_t)f};
                    Vec totals{}; for(int v:edges)++totals[v];
                    for(int u=0;u<=k;++u)if(r0>>u&1)
                    for(int v=u;v<=k;++v)if(r1>>v&1)
                    for(int w=v;w<=k;++w)if(r2>>w&1)
                    for(int z=w;z<=k;++z)if(r3>>z&1) {
                        Rows rows{(uint8_t)u,(uint8_t)v,(uint8_t)w,(uint8_t)z};
                        bins[rows].emplace(totals,edges);
                    }
                }
            }
        }
        Group result;
        for(const auto &[r,m]:bins)
            for(const auto &[count,example]:m)result[r].push_back({count,example});
        return result;
    }
    bool extra(const Match &valid,const Group &normal,Vec baseUse) {
        for(int bucket=0;bucket<=k;++bucket)for(int sign:{-1,1}){
            Match modified{};bool any=false;
            for(int a=0;a<=k;++a)for(int b=a;b<=k;++b)for(int c=b;c<=k;++c){
                int mask=0;auto w=weight[a]+weight[b]+weight[c]+sign*weight[bucket];
                for(int r=0;r<=k;++r)if(weight[r]==w && good(r,a,b,c,sign>0?bucket+1:0,sign<0?bucket+1:0))mask|=1<<r;
                any|=mask!=0;
                modified[a][b][c]=modified[a][c][b]=modified[b][a][c]=modified[b][c][a]=modified[c][a][b]=modified[c][b][a]=mask;
            }
            if(!any)continue;
            for(int vertex=0;vertex<4;++vertex){
                Group special=buildGroups(valid,&modified,vertex);
                for(const auto &[r,v]:special){
                    auto it=normal.find(r);if(it==normal.end())continue;
                    const auto &p=it->second;
                    int64_t demand=2*denominator+weight[bucket];
                    for(int x:r)demand+=weight[x];
                    if(2*maxLoss<demand)continue;
                    Vec rowCount{};for(int x:r)++rowCount[x];
                    for(const auto &s:v)for(size_t i=0;i<p.size();++i)for(size_t j=i;j<p.size();++j){
                        ++combinationCount;Vec rhs{};bool live=true;
                        for(int b=0;b<=k;++b){
                            int m=s.count[b]+p[i].count[b]+p[j].count[b];
                            rhs[b]=m-rowCount[b]+(sign>0 && b==bucket);
                            if(!(baseUse[b]+m+rowCount[b]+(b==bucket))){live=false;break;}
                        }
                        if(!live)continue;
                        int final;fold(rhs,true,final);
                        if(final!=-1)continue;
                        std::cout<<"FOUND events "<<k<<" lines "<<45+k<<"\n";
                        for(int t=1;t<=k;++t)std::cout<<"event "<<t<<' '<<ops[t].factor<<' '<<ops[t].parent<<' '<<ops[t].second<<"\n";
                        std::cout<<"rows";for(int x:r)std::cout<<' '<<x;std::cout<<"\n";
                        for(const auto *e:{&s.example,&p[i].example,&p[j].example}){
                            std::cout<<"hole";for(int x:*e)std::cout<<' '<<x;std::cout<<"\n";
                        }
                        std::cout<<"bool "<<vertex<<" 0 "<<sign<<' '<<bucket<<'\n';
                        return true;
                    }
                }
            }
        }
        return false;
    }
    bool inspect() {
        ++templates;
        if((templates-1)%stride!=unsigned(shard))return false;
        denominator=1;maxLoss=0;
        for(int i=1;i<=k;++i)if(ops[i].factor<0)denominator*=-ops[i].factor;
        weight[0]=denominator;
        for(int i=1;i<=k;++i){
            auto op=ops[i]; auto x=weight[op.parent]+(op.second<0?0:weight[op.second]);
            weight[i]=op.factor<0?x/(-op.factor):x*op.factor;
            if(op.factor<0)maxLoss+=x-weight[i];
        }
        auto ends=std::minmax_element(weight.begin(),weight.begin()+k+1);
        if(*ends.first*3>*ends.second)return false;
        // Sum of the twelve coefficient cancellations fixes the unrounded
        // constant at half of all pigeon weights (plus half each Boolean
        // axiom's weight). Each rounding can remove at most (d-1)/d.
        if(2*maxLoss < 2*denominator+(12+booleans)*(*ends.first))return false;
        std::string key;
        Match valid{};
        bool possible=false;
        for(int a=0;a<=k;++a)for(int b=a;b<=k;++b)for(int c=b;c<=k;++c){
            int mask=0; auto w=weight[a]+weight[b]+weight[c];
            for(int r=0;r<=k;++r)if(weight[r]==w && good(r,a,b,c))mask|=1<<r;
            key.push_back(char(mask));
            possible|=mask!=0;
            valid[a][b][c]=valid[a][c][b]=valid[b][a][c]=valid[b][c][a]=valid[c][a][b]=valid[c][b][a]=mask;
        }
        if(!possible)return false;
        auto it=cache.find(key);
        if(it==cache.end()){
            if(cache.size()>=1800)cache.clear();
            it=cache.emplace(key,buildGroups(valid)).first;
        }
        if(it->second.empty())return false;
        ++feasible;
        Vec baseUse{};
        for(int i=1;i<=k;++i){++baseUse[ops[i].parent]; if(ops[i].second>=0)++baseUse[ops[i].second];}
        if(booleans)return extra(valid,it->second,baseUse);
        for(const auto &[rows,p]:it->second){
            int64_t demand=2*denominator;
            for(int r:rows)demand+=weight[r];
            if(2*maxLoss<demand)continue;
            Vec rowCount{};for(int r:rows)++rowCount[r];
            for(size_t i=0;i<p.size();++i)for(size_t j=i;j<p.size();++j)for(size_t l=j;l<p.size();++l){
                ++combinationCount;
                Vec constants{};bool alive=true;
                for(int s=0;s<=k;++s){
                    int count=p[i].count[s]+p[j].count[s]+p[l].count[s];
                    constants[s]=count-rowCount[s];
                    if(!(baseUse[s]+count+rowCount[s])){alive=false;break;}
                }
                if(!alive)continue;
                int rhs=0;fold(constants,true,rhs);
                if(rhs!=-1)continue;
                std::cout<<"FOUND events "<<k<<" lines "<<43+k<<"\n";
                for(int s=1;s<=k;++s)std::cout<<"event "<<s<<' '<<ops[s].factor<<' '<<ops[s].parent<<' '<<ops[s].second<<"\n";
                std::cout<<"rows";for(int r:rows)std::cout<<' '<<r;std::cout<<"\n";
                for(auto idx:{i,j,l}){std::cout<<"hole";for(int v:p[idx].example)std::cout<<' '<<v;std::cout<<"\n";}
                return true;
            }
        }
        return false;
    }
    bool descend(int i) {
        if(i>k)return inspect();
        if(i>=N)return false;
        auto next=[&](Op choice){
            int level=1+std::max(depth[choice.parent],choice.second<0?0:depth[choice.second]);
            auto order=[](Op a){return std::tuple(a.parent,a.second,a.factor);};
            if(level<depth[i-1] || (i>1 && level==depth[i-1] && order(choice)<order(ops[i-1])))return false;
            ops[i]=choice;depth[i]=level;return descend(i+1);
        };
        for(int p=0;p<i;++p){
            for(int d=2;d<=maxDiv;++d)if(next({-d,p,-1}))return true;
            for(int m=2;m<=maxMul;++m)if(next({m,p,-1}))return true;
            for(int q=p+1;q<i;++q)if(next({1,p,q}))return true;
        }
        return false;
    }
public:
    Engine(int count,int mul,int div,int shardCount,int shardID,int b)
      :k(count),maxMul(mul),maxDiv(div),stride(shardCount),shard(shardID),booleans(b){}
    void run(){
        bool found=descend(1);
        std::cout<<(found?"witness":"exhausted")<<" events "<<k<<" Boolean axioms "<<booleans<<" multipliers through "<<maxMul
                 <<" divisors through "<<maxDiv<<" templates "<<templates<<" feasible "<<feasible
                 <<" last sums "<<combinationCount<<"\n";
    }
};
int main(int argc,char **argv){
    if(argc!=4&&argc!=6&&argc!=7){std::cerr<<"usage: cp-templates EVENTS MAX_MULTIPLIER MAX_DIVISOR [SHARDS INDEX [BOOLEAN_AXIOMS_0_OR_1]]\n";return 2;}
    int k=std::stoi(argv[1]),m=std::stoi(argv[2]),d=std::stoi(argv[3]);
    int n=argc>=6?std::stoi(argv[4]):1,s=argc>=6?std::stoi(argv[5]):0;
    int b=argc==7?std::stoi(argv[6]):0;
    if(k<0||k>7||m<1||m>16||d<2||d>16||n<=0||s<0||s>=n||b<0||b>1)return 2;
    Engine(k,m,d,n,s,b).run();
}
