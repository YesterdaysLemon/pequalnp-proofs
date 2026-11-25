// Exact bounded fan-in-two circuit search. A node cap returns UNKNOWN.
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

using Pos = unsigned __int128;
using Neg = uint64_t;
struct Wire {
    Pos p{};
    Neg n{};
    bool operator==(const Wire &) const = default;
};
struct WireHash {
    size_t operator()(Wire w) const {
        size_t h = std::hash<Neg>{}(Neg(w.p));
        for (auto v : {Neg(w.p >> 64), w.n})
            h ^= std::hash<Neg>{}(v) + 0x9e3779b97f4a7c15ULL + (h << 6) + (h >> 2);
        return h;
    }
};
struct Key {
    std::array<int, 16> data{};
    int len{}, remaining{}, neg{};
    bool operator==(const Key &) const = default;
};
struct KeyHash {
    size_t operator()(const Key &k) const {
        size_t h = k.remaining * 31 + k.neg;
        for (int i = 0; i < k.len; ++i) h = (h ^ k.data[i]) * 1099511628211ULL;
        return h;
    }
};
struct Step { char op; int a, b, out; };
struct Cutoff {};

class Search {
    std::vector<Wire> wires;
    std::unordered_map<Wire, int, WireHash> ids;
    std::unordered_set<Key, KeyHash> exhausted;
    std::vector<Step> path;
    std::vector<int> inputs;
    Wire goal, zero, one;
    int positives{}, negatives{}, goal_id{};
    uint64_t nodes{}, limit;
    std::vector<std::vector<int>> symmetries;
    bool free_signs{};

    bool root_representative(int i, int j) const {
        if (!path.empty()) return true;
        for (const auto &perm : symmetries) {
            if (j < 0) {
                if (perm[i] < i) return false;
            } else if (std::minmax(perm[i], perm[j]) < std::minmax(i, j)) return false;
        }
        return true;
    }

    int intern(Wire w) {
        if (auto it = ids.find(w); it != ids.end()) return it->second;
        if (wires.size() >= 1500000) throw Cutoff{};
        int id = static_cast<int>(wires.size());
        ids.emplace(w, id);
        wires.push_back(w);
        return id;
    }
    static bool dominates(Wire a, Wire b) {
        return !(b.p & ~a.p) && !(a.n & ~b.n);
    }
    bool feasible(const std::vector<int> &bank, bool allow_not) const {
        Pos lower = 0;
        Neg upper = 0;
        for (int y = 0; y < negatives; ++y) {
            Neg bit = Neg(1) << y;
            Pos missing = goal.p;
            for (auto id : bank) {
                if (!(wires[id].n & bit)) missing &= ~wires[id].p;
                else if (free_signs) missing &= wires[id].p;
                if (!missing) break;
            }
            if (!missing) continue;
            if (free_signs) return false;
            if (!allow_not) return false;
            lower |= missing;
            upper |= bit;
        }
        while (upper) {
            Neg bit = upper & -upper;
            upper -= bit;
            Pos obstruction = lower;
            for (auto id : bank) {
                if (wires[id].n & bit) obstruction &= wires[id].p;
                if (!obstruction) break;
            }
            if (obstruction) return false;
        }
        return true;
    }
    bool dfs(const std::vector<int> &bank, int binary, bool allow_not) {
        if (++nodes > limit) throw Cutoff{};
        if (std::find(bank.begin(), bank.end(), goal_id) != bank.end()) return true;
        int size = int(bank.size());
        if (size > binary + 1 || !feasible(bank, allow_not)) return false;
        Key key;
        key.len = size; key.remaining = binary; key.neg = allow_not;
        std::copy(bank.begin(), bank.end(), key.data.begin());
        std::sort(key.data.begin(), key.data.begin() + size);
        if (exhausted.contains(key)) return false;
        auto add = [&](char op, int i, int j, Wire z, bool next_not, int next_binary) {
            if (z == zero || z == one) return false;
            for (auto id : bank)
                if (wires[id] == z || (!next_not && !free_signs && dominates(wires[id], z))) return false;
            if (!next_not && !free_signs && (dominates(zero, z) || dominates(one, z))) return false;
            int zout = intern(z);
            int choices = (j == -1) ? 2 : 4;
            path.push_back({op, bank[i], j == -1 ? -1 : bank[j], zout});
            for (int keep = 0; keep < choices; ++keep) {
                int next_size = size - (j != -1) + __builtin_popcount(unsigned(keep));
                if (next_size > next_binary + 1) continue;
                std::vector<int> next;
                next.reserve(next_size);
                for (int k = 0; k < size; ++k) {
                    if ((k == i && !(keep & 1)) || (k == j && !(keep & 2))) continue;
                    next.push_back(bank[k]);
                }
                next.push_back(zout);
                if (dfs(next, next_binary, next_not)) return true;
            }
            path.pop_back();
            return false;
        };
        if (allow_not) {
            for (int i = 0; i < size; ++i) {
                if (!root_representative(i, -1)) continue;
                Wire a = wires[bank[i]];
                if (add('!', i, -1, {one.p ^ a.p, one.n ^ a.n}, false, binary)) return true;
            }
        }
        if (binary > 0) {
            for (int i = 0; i < size; ++i) {
                Wire a = wires[bank[i]];
                for (int j = 0; j < i; ++j) {
                    if (!root_representative(i, j)) continue;
                    Wire b = wires[bank[j]];
                    if (add('&', i, j, {a.p & b.p, a.n & b.n}, allow_not, binary - 1)) return true;
                    if (add('|', i, j, {a.p | b.p, a.n | b.n}, allow_not, binary - 1)) return true;
                    if (free_signs && add('A', i, j, {a.p & ~b.p, a.n & ~b.n}, false, binary - 1)) return true;
                    if (free_signs && add('B', i, j, {b.p & ~a.p, b.n & ~a.n}, false, binary - 1)) return true;
                }
            }
        }
        if (exhausted.size() >= 150000) exhausted.clear();
        exhausted.insert(key);
        return false;
    }
public:
    Search(int dropped, int mode, uint64_t max_nodes) : limit(max_nodes), free_signs(mode == 2) {
        constexpr uint64_t truth = 0xfe80e800fe00e800ULL;
        std::vector<int> original;
        int fixed = dropped >= 6;
        if (fixed) dropped -= 6;
        for (int i=0;i<6;++i) if (i!=dropped) original.push_back(i);
        int n=int(original.size()), rows=1<<n;
        std::vector<bool> target(rows);
        for (int x=0;x<rows;++x) {
            int row=fixed ? 1<<dropped : 0;
            for (int i=0;i<n;++i) if (x & (1<<i)) row |= 1<<original[i];
            target[x]=(truth>>row)&1;
        }
        std::vector<Wire> literals(n);
        std::vector<int> perm(n);
        for (int i = 0; i < n; ++i) perm[i] = i;
        do {
            bool good = true;
            for (int x=0; x<rows && good; ++x) {
                int y=0;
                for(int i=0;i<n;++i) if(x & (1<<i)) y|=1<<perm[i];
                if(target[x]!=target[y]) good=false;
            }
            if (good) symmetries.push_back(perm);
        } while (std::next_permutation(perm.begin(), perm.end()));
        for (int x = 0; x < rows; ++x) {
            if (mode == 0) {
                bool keep = true;
                for (int i = 0; i < n; ++i)
                    if (bool((x >> i) & 1) == target[x] && target[x ^ (1 << i)] == target[x])
                        keep = false;
                if (!keep) continue;
            }
            int row = target[x] ? positives++ : negatives++;
            if (row >= (target[x] ? 128 : 64)) throw std::runtime_error("row capacity");
            for (int v = 0; v < n; ++v) if ((x >> v) & 1) {
                if (target[x]) literals[v].p |= Pos(1) << row;
                else literals[v].n |= Neg(1) << row;
            }
        }
        goal = {positives==128 ? ~Pos(0) : (Pos(1) << positives) - 1, 0};
        one = {goal.p, negatives==64 ? ~Neg(0) : (Neg(1) << negatives) - 1};
        for (auto w : literals) inputs.push_back(intern(w));
        goal_id = intern(goal);
        std::cout << "variables";
        for (int v : original) std::cout << ' ' << v;
        std::cout << "; positives " << positives << "; negatives " << negatives << '\n';
    }
    void run(int binary, bool allow_not) {
        std::string status;
        try {
            bool found = dfs(inputs, binary, allow_not);
            status = found ? "SAT" : "UNSAT";
            if (found) {
                std::vector<int> all = inputs;
                for (Step s : path) {
                    auto index = [&](int a) { return std::find(all.begin(), all.end(), a) - all.begin(); };
                    std::cout << all.size() << " = " << s.op << ' ' << index(s.a);
                    if (s.b != -1) std::cout << ' ' << index(s.b);
                    std::cout << '\n';
                    all.push_back(s.out);
                }
            }
        } catch (const Cutoff &) { status = "UNKNOWN"; }
        std::cout << status << " binary " << binary << " available NOT " << allow_not
                  << " free signs " << free_signs << " visits " << nodes << " wire values " << wires.size() << std::endl;
    }
};

int main(int argc, char **argv) {
    if (argc != 5) { std::cerr << "use: search DROPPED_VERTEX_OR_-1 BINARY_BUDGET MODE_0_MONO_1_ONENOT_2_FREESIGNS NODE_LIMIT\n"; return 2; }
    int dropped = std::stoi(argv[1]), binary = std::stoi(argv[2]), mode = std::stoi(argv[3]);
    if (dropped < -1 || dropped > 11 || binary < 0 || binary > 14 || mode < 0 || mode > 2) return 2;
    Search search(dropped, mode, std::stoull(argv[4]));
    search.run(binary, mode == 1);
}
