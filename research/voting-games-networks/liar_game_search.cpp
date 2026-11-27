// Find a first question that strictly improves on splitting each class in half.
// Build: c++ -O3 -std=c++17 liar_game_search.cpp -o liar_game_search
// Usage: ./liar_game_search maximum_lie_allowance maximum_positive_budget_candidates horizons
// Example: ./liar_game_search 7 14 38
#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <stdexcept>
#include <string>
#include <unordered_map>

using State = std::uint64_t;
using Count = std::int64_t;
constexpr int MaxHorizon = 57;
constexpr int MaxBudget = 15;
using Row = std::array<Count, MaxHorizon + 1>;

struct Search {
    int budgets, candidates, horizons;
    int prefixes = 0;
    std::array<Row, MaxHorizon + 1> ball{};
    std::array<std::unordered_map<State, Count>, MaxHorizon + 1> cache;

    Search(int e, int n, int q) : budgets(e), candidates(n), horizons(q) {
        // Cumulative binomial sums. ball[h][r] is the volume of a radius-r binary ball.
        Row choose{};
        choose[0] = 1;
        for (int h = 0; h <= q; ++h) {
            Count sum = 0;
            for (int r = 0; r <= MaxHorizon; ++r) {
                sum += choose[r];
                ball[h][r] = sum;
            }
            if (h < q)
                for (int r = h + 1; r > 0; --r) choose[r] += choose[r - 1];
        }
    }

    // A four-bit digit for each positive allowance. At most 15 candidates together,
    // so digitwise sums below cannot carry. Pennies (allowance zero) are implicit.
    static State unit(int r) { return State{1} << (4 * (r - 1)); }
    static int count(State state, int r) { return (state / unit(r)) & 15; }

    // A binary simplex code on k-bit messages has length 2^k-1, distance 2^(k-1):
    // its coordinates are the nonzero linear functionals of the message over F_2.
    // Repeating the block gives at least n words of mutual distance at least 2r+1.
    static int codeLength(int n, int r) {
        if (n <= 1) return 0;
        int size = 2;
        while (size < n) size *= 2;
        int distance = size / 2;
        int blocks = (2 * r + distance) / distance;
        return (size - 1) * blocks;
    }

    // Exact maximum number of extra pennies for a winning position in h questions.
    // A negative result means even the positive-budget candidates alone cannot win.
    Count capacity(int h, State state) {
        const Count words = Count{1} << h;
        if (state == 0) return words;
        auto it = cache[h].find(state);
        if (it != cache[h].end()) return it->second;

        Count free = words;
        int n = 0, largest = 0, second = 0;
        for (int r = 1; r <= budgets; ++r) {
            const int c = count(state, r);
            if (c == 0) continue;
            n += c;
            second = c >= 2 ? r : largest;
            largest = r;
            free -= c * ball[h][r];
        }
        // Any strategy gives a candidate with budget r exactly ball[h][r]
        // compatible transcripts. For two distinct candidates the adversary can
        // keep both alive while their total remaining budget is at least h.
        if (free < 0 || (n >= 2 && largest + second >= h)) return -1;
        // For n<=2 choose opposite words. For larger n use the explicit simplex
        // code, or greedily exclude radius-2r balls around the previously chosen
        // words. All remaining individual transcripts can be assigned to pennies.
        if (n <= 2 || h >= codeLength(n, largest) ||
            (n - 1) * ball[h][2 * largest] < words) return free;

        Count best = -1;
        auto choose = [&](auto&& self, int r, State selected) -> void {
            if (best == free) return;
            if (r == 0) {
                State other = state - selected;
                if (selected > other) return;  // symmetric yes/no answers
                // Wrong-side candidates lose one budget unit. Budget-one
                // candidates from the wrong side consume penny capacity.
                Count yes = capacity(h - 1, selected + (other >> 4)) - count(other, 1);
                if (yes < 0) return;
                Count no = capacity(h - 1, other + (selected >> 4)) - count(selected, 1);
                if (no >= 0) best = std::max(best, yes + no);
                return;
            }
            int c = count(state, r), middle = c / 2;
            self(self, r - 1, selected + middle * unit(r));
            for (int a = 0; a <= c && best != free; ++a)
                if (a != middle) self(self, r - 1, selected + a * unit(r));
        };
        choose(choose, budgets, 0);
        cache[h].emplace(state, best);
        return best;
    }

    bool inspect(State state) {
        if (state == 0) return false;  // ordinary noiseless binary search
        ++prefixes;
        State half = 0;
        for (int r = 1; r <= budgets; ++r) half += (count(state, r) / 2) * unit(r);
        State child = half + (half >> 4);
        for (int h = 1; h <= horizons; ++h) {
            Count full = capacity(h, state);
            if (full < 0) continue;
            Count balanced = 2 * (capacity(h - 1, child) - count(half, 1));
            if ((full / 2) * 2 > balanced) {
                std::cout << "Counterexample at horizon " << h << ", pennies "
                          << std::max(Count{0}, balanced + 2) << ", positive-budget counts";
                for (int r = 1; r <= budgets; ++r) std::cout << ' ' << count(state, r);
                std::cout << '\n';
                return true;
            }
        }
        return false;
    }

    bool enumerate(int r, int remaining, State state) {
        if (r == 0) return inspect(state);
        for (int c = 0; c <= remaining; c += 2)
            if (enumerate(r - 1, remaining - c, state + c * unit(r))) return true;
        return false;
    }
};

int main(int argc, char** argv) {
    if (argc != 4) {
        std::cerr << "Supply maximum allowance, maximum positive-budget candidates, and horizon.\n";
        return 2;
    }
    int e = std::stoi(argv[1]), n = std::stoi(argv[2]), q = std::stoi(argv[3]);
    if (e < 1 || e > MaxBudget || n < 2 || n > 15 || q < 1 || q > MaxHorizon) {
        std::cerr << "Supported ranges are 1..15, 2..15, and 1..57 respectively.\n";
        return 2;
    }
    Search search(e, n, q);
    if (search.enumerate(e, n, 0)) return 1;
    std::cout << "No counterexample in " << search.prefixes << " nonempty even prefixes "
              << "through horizon " << q << ". For each prefix all even penny counts are covered.\n";
    int threshold = Search::codeLength(n, e);
    std::cout << "For any horizon at least " << threshold + 1
              << ", a simplex code fits both balanced children whenever the volume bound holds.\n";
    return 0;
}
