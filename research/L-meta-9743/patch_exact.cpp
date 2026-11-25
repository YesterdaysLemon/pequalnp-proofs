// Exact search for a small monotone circuit on positive and negative samples.
// All inputs must be essential, as witnessed by the sample rows at startup.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <stdexcept>
#include <unordered_map>
#include <unordered_set>
#include <vector>

using Mask = std::uint64_t;
struct Wire {
    Mask positive, negative;
    bool operator==(const Wire &) const = default;
};
struct WireHash {
    size_t operator()(Wire w) const { return w.positive * 11400714819323198485ULL ^ w.negative; }
};
struct Key {
    std::array<int, 22> ids{};
    int size{}, budget{};
    bool operator==(const Key &) const = default;
};
struct KeyHash {
    size_t operator()(const Key &k) const {
        size_t h = k.budget;
        for (int i = 0; i < k.size; ++i) h = (h ^ k.ids[i]) * 1099511628211ULL;
        return h;
    }
};
struct Gate { int a, b, out; bool is_and; };
struct Cutoff {};

class Search {
    std::vector<Wire> wires;
    std::unordered_map<Wire, int, WireHash> identifiers;
    std::unordered_set<Key, KeyHash> exhausted;
    std::vector<Gate> path;
    std::vector<int> inputs;
    std::vector<std::vector<bool>> first_pair;
    Wire goal{};
    int negatives{}, goal_id{};
    uint64_t nodes{}, limit;

    int intern(Wire w) {
        auto [it, inserted] = identifiers.try_emplace(w, int(wires.size()));
        if (inserted) wires.push_back(w);
        if (wires.size() > 1500000) throw Cutoff{};
        return it->second;
    }
    static bool dominates(Wire a, Wire b) {
        return !(b.positive & ~a.positive) && !(a.negative & ~b.negative);
    }
    bool separates(const std::vector<int> &bank) const {
        for (int row = 0; row < negatives; ++row) {
            Mask missing = goal.positive;
            for (int id : bank) {
                if (!(wires[id].negative & (Mask(1) << row))) missing &= ~wires[id].positive;
                if (!missing) break;
            }
            if (missing) return false;
        }
        return true;
    }
    bool dfs(const std::vector<int> &bank, int budget) {
        if (++nodes > limit) throw Cutoff{};
        if (std::find(bank.begin(), bank.end(), goal_id) != bank.end()) return true;
        int size = int(bank.size());
        if (size > budget + 1 || !budget || !separates(bank)) return false;
        Key key;
        key.size = size;
        key.budget = budget;
        std::copy(bank.begin(), bank.end(), key.ids.begin());
        std::sort(key.ids.begin(), key.ids.begin() + size);
        if (exhausted.contains(key)) return false;
        for (int i = 0; i < size; ++i) for (int j = 0; j < i; ++j) {
            if (path.empty() && !first_pair[i][j]) continue;
            Wire a = wires[bank[i]], b = wires[bank[j]];
            for (bool is_and : {true, false}) {
                Wire z = is_and ? Wire{a.positive & b.positive, a.negative & b.negative}
                                : Wire{a.positive | b.positive, a.negative | b.negative};
                if (!z.positive || z.negative == negative_ones) continue;
                if (std::any_of(bank.begin(), bank.end(), [&](int id){ return dominates(wires[id], z); })) continue;
                int out = intern(z);
                path.push_back({bank[i], bank[j], out, is_and});
                for (int keep = 0; keep < 4; ++keep) {
                    int next_size = size - 1 + std::popcount(unsigned(keep));
                    if (next_size > budget) continue;
                    std::vector<int> next;
                    next.reserve(next_size);
                    for (int k = 0; k < size; ++k) {
                        if ((i == k && !(keep & 1)) || (j == k && !(keep & 2))) continue;
                        next.push_back(bank[k]);
                    }
                    next.push_back(out);
                    if (dfs(next, budget - 1)) return true;
                }
                path.pop_back();
            }
        }
        if (exhausted.size() >= 200000) exhausted.clear();
        exhausted.insert(key);
        return false;
    }
    Mask negative_ones{};
    static Mask all_bits(int count) { return count == 64 ? ~Mask(0) : (Mask(1) << count) - 1; }
public:
    Search(int n, const std::vector<int> &pos, const std::vector<int> &neg, uint64_t cap)
        : first_pair(n, std::vector<bool>(n, true)), negatives(int(neg.size())), limit(cap) {
        if (n < 1 || n > 15 || pos.empty() || neg.empty() || pos.size() > 64 || neg.size() > 64)
            throw std::runtime_error("outside row or input capacity");
        for (auto &rows : {pos, neg}) for (int row : rows)
            if (row < 0 || row >= (1 << n)) throw std::runtime_error("invalid sample");
        for (int v = 0; v < n; ++v) {
            bool essential = false;
            for (int p : pos) for (int q : neg) {
                if (!(p & ~q)) throw std::runtime_error("incompatible rows");
                if ((p & ~q) == (1 << v)) essential = true;
            }
            if (!essential) throw std::runtime_error("variable lacks an essentiality witness");
            Wire w{};
            for (int i = 0; i < int(pos.size()); ++i) if (pos[i] & (1 << v)) w.positive |= Mask(1) << i;
            for (int i = 0; i < int(neg.size()); ++i) if (neg[i] & (1 << v)) w.negative |= Mask(1) << i;
            inputs.push_back(intern(w));
        }
        goal = {all_bits(int(pos.size())), 0};
        goal_id = intern(goal);
        negative_ones = all_bits(int(neg.size()));
        if (n > 9) return;
        std::vector<int> perm(n);
        std::iota(perm.begin(), perm.end(), 0);
        std::vector<int> color(1 << n);
        for (int p : pos) color[p] = 1;
        for (int q : neg) color[q] = 2;
        auto preserves = [&](const std::vector<int> &rows, int kind) {
            for (int row : rows) {
                int image = 0;
                for (int m = row; m; m &= m - 1) image |= 1 << perm[std::countr_zero(unsigned(m))];
                if (color[image] != kind) return false;
            }
            return true;
        };
        do {
            if (!preserves(pos, 1) || !preserves(neg, 2)) continue;
            for (int i = 0; i < n; ++i) for (int j = 0; j < i; ++j)
                if (std::minmax(perm[i], perm[j]) < std::minmax(i, j)) first_pair[i][j] = false;
        } while (std::next_permutation(perm.begin(), perm.end()));
    }
    void run(int budget) {
        const char *result = "UNKNOWN";
        try {
            bool found = dfs(inputs, budget);
            result = found ? "SAT" : "UNSAT";
            if (found) {
                std::vector<int> ids = inputs;
                for (auto s : path) {
                    auto index = [&](int id){ return std::find(ids.begin(), ids.end(), id) - ids.begin(); };
                    std::cout << ids.size() << " = " << (s.is_and ? '&' : '|') << ' '
                              << index(s.a) << ' ' << index(s.b) << '\n';
                    ids.push_back(s.out);
                }
            }
        } catch (const Cutoff &) {}
        std::cout << result << " budget " << budget << " visits " << nodes << " wire values " << wires.size() << '\n';
    }
};

int main(int argc, char **argv) {
    if (argc < 2 || argc > 3) return 2;
    int n, budget, p, q;
    if (!(std::cin >> n >> budget >> p >> q) || p < 1 || p > 64 || q < 1 || q > 64 || n < 1 || n > 15) return 2;
    if (argc == 3) budget += std::stoi(argv[2]);
    if (budget < 0 || budget > 20) return 2;
    std::vector<int> pos(p), neg(q);
    for (int &x : pos) if (!(std::cin >> x)) return 2;
    for (int &x : neg) if (!(std::cin >> x)) return 2;
    Search search(n, pos, neg, std::stoull(argv[1]));
    search.run(budget);
}
