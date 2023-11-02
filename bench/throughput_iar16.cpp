/*
  MIT License

  Copyright (c) 2023 Nicolai Trandafil

  Permission is hereby granted, free of charge, to any person obtaining a copy
  of this software and associated documentation files (the "Software"), to deal
  in the Software without restriction, including without limitation the rights
  to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
  copies of the Software, and to permit persons to whom the Software is
  furnished to do so, subject to the following conditions:

  The above copyright notice and this permission notice shall be included in all
  copies or substantial portions of the Software.

  THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
  IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
  FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
  AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
  LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
  OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
  SOFTWARE.
*/

#include "bye_trie/bye_trie.h"

#include <chrono>
#include <iomanip>
#include <iostream>
#include <random>

using namespace bye_trie;

using std::cout;
using std::mt19937;
using std::setw;
using std::uniform_int_distribution;
using std::chrono::duration_cast;
using std::chrono::milliseconds;
using std::chrono::seconds;

template <class T>
static inline __attribute__((always_inline)) void do_not_optimize(T&& value) noexcept {
    asm volatile("" : "+m"(value) : : "memory");
}

int main() {
    ByeTrie<uint32_t, long, SystemAllocator, 6, Iar16<6>> trie;

    constexpr auto w = 44;

    cout << std::fixed << std::setprecision(2);

    mt19937 gen{0};
    uniform_int_distribution<uint32_t> dist{0, 0xffffff};

    auto const start = std::chrono::steady_clock::now();

    auto const len_24_count = 10'000'000;
    for (int i = 0; i < len_24_count; ++i) {
        trie.insert(Bits{dist(gen), 24}, i);
    }

    auto const end_len_24 = std::chrono::steady_clock::now();

    cout << setw(w) << "count of random 24bit prefixes: " << len_24_count << '\n';

    dist = uniform_int_distribution<uint32_t>{0, 0xffffffff};

    auto const len_32_count = 10'000'000;
    for (int i = 0; i < len_32_count; ++i) {
        trie.insert(Bits{dist(gen), 32}, i);
    }

    auto const end_len_32 = std::chrono::steady_clock::now();

    cout << setw(w) << "count of random 32bit prefixes: " << len_32_count << '\n';
    cout << setw(w) << "insert throughput of 24bit prefixes: "
         << 24.0 / 8 * len_24_count / 1024 / 1024
                    / duration_cast<milliseconds>(end_len_24 - start).count() * 1000
         << "MB/s\n";
    cout << setw(w) << "insert throughput of 32bit prefixes: "
         << 32.0 / 8 * len_32_count / 1024 / 1024
                    / duration_cast<milliseconds>(end_len_32 - end_len_24).count() * 1000
         << "MB/s\n";

    auto const start_match_longest = std::chrono::steady_clock::now();

    auto const match_longest_count = 10'000'000;
    for (int i = 0; i < match_longest_count; ++i) {
        do_not_optimize(trie.match_longest(Bits{dist(gen), 32}));
    }

    auto const end_match_longest = std::chrono::steady_clock::now();

    cout << "---\n";
    cout << setw(w) << "count of match_longest: " << match_longest_count << '\n';
    cout << setw(w) << "match_longest throughput of 32bit prefixes: "
         << 32.0 / 8 * match_longest_count / 1024 / 1024
                    / duration_cast<milliseconds>(end_match_longest - start_match_longest)
                              .count()
                    * 1000
         << "MB/s\n";

    auto const start_match_exact = std::chrono::steady_clock::now();

    auto const match_exact_count = 10'000'000;
    for (int i = 0; i < match_exact_count; ++i) {
        do_not_optimize(trie.match_exact(Bits{dist(gen), 32}));
    }

    auto const end_match_exact = std::chrono::steady_clock::now();

    cout << "---\n";
    cout << setw(w) << "count of match_exact: " << match_exact_count << '\n';
    cout << setw(w) << "match_exact throughput of 32bit prefixes: "
         << 32.0 / 8 * match_exact_count / 1024 / 1024
                    / duration_cast<milliseconds>(end_match_exact - start_match_exact)
                              .count()
                    * 1000
         << "MB/s\n";
}
