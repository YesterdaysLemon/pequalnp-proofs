// Signed live-wire search using lower bounds for vertex-deleted graphs.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <string>
#include <unordered_set>
#include <vector>

using W = uint64_t;
using Bank = std::vector<W>;
struct Minor { W mask; int lower, lost; };
struct KHash {
    size_t operator()(const std::vector<W> &v) const {
        W h = 1469598103934665603ULL;
        for (W w : v) { h ^= w + (h << 6) + (h >> 2); h *= 1099511628211ULL; }
        return h;
    }
};
struct Search {
    int n, start, signed_prune, root_sym;
    W target = 0, all;
    std::vector<W> literal;
    std::vector<int> negative;
    std::vector<std::vector<int>> sym;
    uint64_t visits = 0, expanded = 0, minor_cuts = 0;
    std::array<uint64_t, 20> profile{};
    std::array<uint64_t, 20> branching{};
    std::unordered_set<std::vector<W>,KHash> memo;
    using Table = std::array<std::array<W,256>,8>;
    std::vector<Table> tables;
    explicit Search(int removed, int budget, int prune, int symmetry)
      : start(budget), signed_prune(prune), root_sym(symmetry) {
        std::vector<int> labels;
        for (int x : {0,1,2,3,5,6}) if (x != removed) labels.push_back(x);
        n = int(labels.size());
        all = n == 6 ? ~W(0) : ((W(1) << (1 << n)) - 1);
        literal.resize(n);
        for (int x = 0; x < (1 << n); ++x) {
            int old = 0;
            for (int i = 0; i < n; ++i) if ((x >> i) & 1) {
                old |= (1 << labels[i]); literal[i] |= W(1) << x;
            }
            auto blk = [&](int mask) { return std::popcount(unsigned(old & mask)); };
            if (blk(5) == 2 || blk(10) == 2 || (blk(96) > 0 && std::popcount(unsigned(old)) >= 2))
                target |= W(1) << x;
            else negative.push_back(x);
        }
        std::vector<int> p(n);
        for (int i = 0; i < n; ++i) p[i] = i;
        do {
            bool good = true;
            for (int i = 0; i < n; ++i) for (int j = 0; j < i; ++j) {
                int a = (1 << i) | (1 << j), b = (1 << p[i]) | (1 << p[j]);
                if (((target >> a) ^ (target >> b)) & 1) good = false;
            }
            if (good) sym.push_back(p);
        } while (std::next_permutation(p.begin(), p.end()));
        if (root_sym == 2) for (const auto &perm : sym) {
            Table tab{};
            for (int x = 0; x < (1 << n); ++x) {
                int sx = 0;
                for (int v = 0; v < n; ++v) if ((x >> v) & 1) sx |= 1 << perm[v];
                for (int c = 0; c < 256; ++c) if ((c >> (x % 8)) & 1) tab[x/8][c] |= W(1) << sx;
            }
            tables.push_back(tab);
        }
    }
    Search(int variables, W table, int budget)
      : n(variables), start(budget), signed_prune(0), root_sym(0) {
        all = n == 6 ? ~W(0) : ((W(1) << (1 << n)) - 1);
        target = (table & 1) ? all ^ table : table;
        literal.resize(n);
        for (int x = 0; x < (1 << n); ++x) {
            for (int v = 0; v < n; ++v) if ((x >> v) & 1) literal[v] |= W(1) << x;
            if (!((target >> x) & 1)) negative.push_back(x);
        }
    }
    bool separable(const Bank &s) const {
        for (int y : negative) {
            W bad = target;
            for (W w : s) {
                bad &= (w >> y) & 1 ? w : ~w;
                if (!bad) break;
            }
            if (bad) return false;
        }
        return true;
    }
    bool lower_ok(const Bank &s, const std::vector<Minor> &ms) const {
        for (Minor m : ms) {
            int constant = 0;
            for (W w : s) if (!(w & m.mask) || (w & m.mask) == m.mask) ++constant;
            if (m.lower + m.lost + constant > start) return false;
        }
        return true;
    }
    bool dfs(const Bank &s, int k, const std::vector<Minor> &ms) {
        ++visits;
        if (!lower_ok(s, ms)) { ++minor_cuts; return false; }
        if (s.size() == 1 && s[0] == target) return true;
        if (k == 0 || !separable(s)) return false;
        if (root_sym == 2) {
            std::vector<W> best, candidate;
            for (int g = 0; g < int(tables.size()); ++g) {
                auto &tab = tables[g];
                candidate.clear();
                for (W w : s) {
                    W z = 0;
                    for (int j=0;j<8;++j) z |= tab[j][(w >> (8*j)) & 255];
                    candidate.push_back(z);
                }
                std::sort(candidate.begin(), candidate.end());
                candidate.push_back(W(k));
                W meta = 0;
                if (!ms.empty()) for (int i=0;i<n;++i)
                    meta |= W(ms[i].lost) << (5*sym[g][i]);
                candidate.push_back(meta);
                if (best.empty() || candidate < best) best = candidate;
            }
            if (!memo.insert(best).second) return false;
        }
        ++expanded; ++profile[start - k];
        auto before = expanded;
        for (int i = 0; i < int(s.size()); ++i) for (int j = 0; j < i; ++j) {
            if (k == start && root_sym && std::any_of(sym.begin(), sym.end(), [&](auto &p) {
                    return std::minmax(p[i],p[j]) < std::minmax(i,j); })) continue;
            W a = s[i], b = s[j];
            for (W z : {a & b, a | b, a & ~b, b & ~a}) {
                if (!z || std::find(s.begin(), s.end(), z) != s.end()) continue;
                std::vector<Minor> next_ms = ms;
                for (auto &m : next_ms) {
                    W reduced = z & m.mask;
                    if (!reduced || reduced == m.mask || std::any_of(s.begin(), s.end(), [&](W w) {
                        return (w & m.mask) == reduced || (~w & m.mask) == reduced;
                    })) ++m.lost;
                }
                for (int h = 0; h < 4; ++h) {
                    if (int(s.size()) - 1 + std::popcount(unsigned(h)) > k) continue;
                    Bank next;
                    for (int r = 0; r < int(s.size()); ++r)
                        if ((r != i || (h & 1)) && (r != j || (h & 2))) next.push_back(s[r]);
                    next.push_back(z);
                    if (dfs(next, k-1, next_ms)) return true;
                }
            }
        }
        if (expanded > before) ++branching[start-k];
        return false;
    }
    void run() {
        std::vector<Minor> ms;
        if (signed_prune == 1 && n == 6) for (W v : literal) ms.push_back({~v,8,0});
        bool sat = dfs(literal, start, ms);
        std::cout << "variables " << n << " binary " << start << " minors " << ms.size()
                  << " root symmetry " << root_sym << " " << (sat ? "SAT" : "UNSAT") << " visits " << visits
                  << " expanded " << expanded << " minor cuts " << minor_cuts << " profile";
        for (int i = 0; i < start; ++i) std::cout << ' ' << profile[i];
        std::cout << " nonterminal";
        for (int i = 0; i < start; ++i) std::cout << ' ' << branching[i];
        std::cout << std::endl;
    }
};
int main(int argc, char **argv) {
    if (argc == 5 && std::string(argv[1]) == "table") {
        int n = std::stoi(argv[2]), budget = std::stoi(argv[4]);
        if (n < 1 || n > 6 || budget < 0 || budget >= 20) return 2;
        Search(n,std::stoull(argv[3],nullptr,16),budget).run();
        return 0;
    }
    if (argc != 5) {std::cerr << "use: search DELETED_OR_-1 BINARY_BUDGET MINOR_PRUNE ROOT_SYMMETRY\n"; return 2;}
    int removed = std::stoi(argv[1]), budget = std::stoi(argv[2]);
    int prune = std::stoi(argv[3]), symmetry = std::stoi(argv[4]);
    if ((removed != -1 && (removed < 0 || removed > 6 || removed == 4)) ||
        budget < 0 || budget >= 20 || prune < 0 || prune > 1 || symmetry < 0 || symmetry > 2)
        return 2;
    Search(removed,budget,prune,symmetry).run();
}
