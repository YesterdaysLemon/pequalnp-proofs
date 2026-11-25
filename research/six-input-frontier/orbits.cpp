// Partition monotone six-variable truth tables under input permutations and Boolean duality.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iomanip>
#include <iostream>
#include <stdexcept>
#include <unordered_map>
#include <vector>

using Word=std::uint64_t;
constexpr int n=6;
std::array<Word,n> columns{};

Word swap_axes(Word t,int i,int j) {
    int shift=(1<<j)-(1<<i);
    Word moving=(t^(t>>shift)) & columns[i] & ~columns[j];
    return t ^ moving ^ (moving<<shift);
}

Word dual(Word t) {
    t=~t;
    for (int i=0;i<n;++i) {
        int stride=1<<i;
        t=((t&columns[i])>>stride)|((t&~columns[i])<<stride);
    }
    return t;
}

bool essential(Word t) {
    for (int i=0;i<n;++i)
        if (!((t^(t>>(1<<i)))&~columns[i])) return false;
    return true;
}

int main() {
    for (int i=0;i<n;++i) for (int r=0;r<64;++r)
        if ((r>>i)&1) columns[i]|=Word(1)<<r;
    std::vector<uint32_t> five;
    std::unordered_map<uint32_t,int> index;
    uint32_t t5;
    while (std::cin>>std::hex>>t5) {
        index[t5]=int(five.size());
        five.push_back(t5);
    }
    if (five.size()!=7581 || index.size()!=five.size() || !std::is_sorted(five.begin(),five.end()))
        throw std::runtime_error("expected every monotone five-variable table, in ascending order");
    const size_t width=five.size();
    std::vector<bool> seen(width*width);
    auto mark=[&](Word t) {
        auto pos=size_t(index.at(uint32_t(t>>32)))*width+index.at(uint32_t(t));
        if (seen[pos]) return false;
        seen[pos]=true;
        return true;
    };
    std::uint64_t count=0,allEssential=0,covered=0,classes=0;
    for (uint32_t hi:five) for (uint32_t lo:five) {
        if (lo&~hi) continue;
        ++count;
        Word t=(Word(hi)<<32)|lo;
        if (!essential(t)) continue;
        ++allEssential;
        if (!mark(t)) continue;
        std::vector<Word> group{t};
        for (size_t j=0;j<group.size();++j) {
            Word entry=group[j];
            for (int i=0;i+1<n;++i) {
                Word next=swap_axes(entry,i,i+1);
                if (mark(next)) group.push_back(next);
            }
            Word other=dual(entry);
            if (mark(other)) group.push_back(other);
        }
        if (*std::min_element(group.begin(),group.end())!=t || (1440%group.size()))
            throw std::runtime_error("invalid orbit");
        std::cout<<std::hex<<std::setfill('0')<<std::setw(16)<<t<<' '<<std::dec<<group.size()<<'\n';
        ++classes;
        covered+=group.size();
    }
    if (covered!=allEssential || count!=7828354) throw std::runtime_error("incomplete enumeration");
    std::cerr<<count<<" monotone, "<<allEssential<<" essential, "<<classes<<" essential orbits\n";
}
