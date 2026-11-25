// Exhaustive search over all two-input Boolean operations, modulo free complements.
#include <algorithm>
#include <bit>
#include <cstdint>
#include <iostream>
#include <string>
#include <vector>

using W = uint64_t;
using Bank = std::vector<W>;

struct Search {
    W target;
    std::vector<int> negative;
    uint64_t visits = 0;
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

    bool possible(const Bank &s, int k) {
        ++visits;
        if (s.size() == 1 && s[0] == target) return true;
        if (k == 0 || !separable(s)) return false;
        for (int i = 0; i < int(s.size()); ++i) {
            for (int j = 0; j < i; ++j) {
                W a = s[i], b = s[j];
                for (W z : {a & b, a | b, a & ~b, b & ~a, a ^ b}) {
                    if (!z || std::find(s.begin(), s.end(), z) != s.end()) continue;
                    for (unsigned keep = 0; keep < 4; ++keep) {
                        if (int(s.size()) - 1 + std::popcount(keep) > k) continue;
                        Bank next;
                        for (int v = 0; v < int(s.size()); ++v)
                            if ((v != i || (keep & 1)) && (v != j || (keep & 2)))
                                next.push_back(s[v]);
                        next.push_back(z);
                        if (possible(next, k - 1)) return true;
                    }
                }
            }
        }
        return false;
    }
};

int main(int argc, char **argv) {
    if (argc != 4) return 2;
    int n = std::stoi(argv[1]), budget = std::stoi(argv[3]);
    if (n < 1 || n > 6 || budget < 0 || budget > 15) return 2;
    W table = std::stoull(argv[2], nullptr, 16);
    W mask = n == 6 ? ~W(0) : (W(1) << (1 << n)) - 1;
    Search search{(table & 1) ? (table ^ mask) : table};
    Bank inputs(n);
    for (int i = 0; i < n; ++i) {
        bool essential = false;
        for (int r = 0; r < (1 << n); ++r) {
            if ((r >> i) & 1) inputs[i] |= W(1) << r;
            essential |= ((table >> r) ^ (table >> (r ^ (1 << i)))) & 1;
        }
        if (!essential) { std::cerr << "Remove inessential inputs first\n"; return 2; }
    }
    for (int r = 0; r < (1 << n); ++r)
        if (!((search.target >> r) & 1)) search.negative.push_back(r);
    bool sat = search.possible(inputs, budget);
    std::cout << n << " inputs, budget " << budget << ' ' << (sat ? "SAT" : "UNSAT")
              << ", " << search.visits << " visits\n";
}
