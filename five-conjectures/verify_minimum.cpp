// Exact finite check of the smallest possible Banks-tree argmax violation.
// Build with c++ -std=c++20 -O2 verify_minimum.cpp -o check && ./check
#include <algorithm>
#include <array>
#include <bit>
#include <iostream>
#include <vector>

using Counts = std::array<int, 7>;
using RowSet = std::vector<unsigned>;
constexpr std::array<int, 8> factorial{1, 1, 2, 6, 24, 120, 720, 5040};

Counts banks_counts(const RowSet& incoming) {
    const unsigned full = (1U << incoming.size()) - 1;
    std::vector<Counts> counts(full + 1, Counts{});
    for (unsigned group = 1; group <= full; ++group) {
        int others = std::popcount(group) - 1;
        for (unsigned choices = group; choices; choices &= choices - 1) {
            auto pivot = std::countr_zero(choices);
            unsigned survivors = group & incoming[pivot];
            if (survivors == 0) {
                counts[group][pivot] += factorial[others];
                continue;
            }
            // Conditional on the first pivot, every relative permutation
            // of its surviving opponents occurs equally often.
            int multiplicity = factorial[others] / factorial[std::popcount(survivors)];
            for (unsigned choices_left = survivors; choices_left; choices_left &= choices_left - 1) {
                auto i = std::countr_zero(choices_left);
                counts[group][i] += multiplicity * counts[survivors][i];
            }
        }
    }
    return counts[full];
}

RowSet decode(unsigned mask, int n) {
    RowSet incoming(n);
    int bit = 0;
    for (int i = 1; i < n; ++i) {
        for (int j = 0; j < i; ++j, ++bit) {
            if (mask & (1U << bit)) {
                incoming[i] |= 1U << j;
            } else {
                incoming[j] |= 1U << i;
            }
        }
    }
    return incoming;
}

int main() {
    std::cout << "n   retained labellings    winner-edge flips\n";
    for (int n = 2; n <= 7; ++n) {
        int labellings = 0, flips = 0;
        const unsigned end = 1U << (n * (n - 1) / 2);
        for (unsigned mask = 0; mask < end; ++mask) {
            auto incoming = decode(mask, n);
            // Every tournament can be relabelled in nondecreasing indegree order.
            auto by_degree = [](unsigned a, unsigned b) {
                return std::popcount(a) < std::popcount(b);
            };
            if (!std::is_sorted(incoming.begin(), incoming.end(), by_degree)) continue;
            ++labellings;
            auto initial = banks_counts(incoming);
            auto max_count = *std::max_element(initial.begin(), initial.begin() + n);
            for (int improved = 0; improved < n; ++improved) {
                if (initial[improved] != max_count) continue;
                for (unsigned losses = incoming[improved]; losses; losses &= losses - 1) {
                    auto rival = std::countr_zero(losses);
                    auto revised = incoming;
                    revised[improved] ^= 1U << rival;
                    revised[rival] ^= 1U << improved;
                    auto updated = banks_counts(revised);
                    ++flips;
                    if (updated[improved] < *std::max_element(updated.begin(), updated.begin() + n)) {
                        std::cerr << "Counterexample: " << n << ' ' << mask << ' '
                                  << improved << ' ' << rival << '\n';
                        return 1;
                    }
                }
            }
        }
        std::cout << n << "   " << labellings << "   " << flips << '\n';
    }
    return 0;
}
