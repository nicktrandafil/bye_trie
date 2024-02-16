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

#include "common.h"

#include <bye_trie/bye_trie.h>

#include <concepts>
#include <iostream>

using namespace bye_trie;

int main() {
    constexpr auto networks_count = 1'000'000;

    ByeTrie<uint32_t, long> trie;

    auto const with_parameters = [&](auto f) {
        Bits<uint32_t> bits{4, 8};
        for (unsigned i = 0; i < networks_count; ++i) {
            f(bits, i);
            ++i;
            bits += 32;
        }
    };

    std::cout << "avg. insert: "
              << per_network(benchmark([&] {
                                 with_parameters([&](auto bits, auto i) {
                                     trie.insert(bits, i);
                                 });
                             }),
                             networks_count)
              << "\n";

    std::cout << "prefix count in trie: " << trie.size() << '\n';

    std::cout << "avg. match_exact: "
              << per_network(benchmark([&] {
                                 with_parameters([&](auto bits, auto) {
                                     do_not_optimize(trie.match_exact(bits));
                                 });
                             }),
                             networks_count)
              << "\n";

    std::cout << "avg. match_longest: "
              << per_network(benchmark([&] {
                                 with_parameters([&](auto bits, auto) {
                                     do_not_optimize(trie.match_longest(bits));
                                 });
                             }),
                             networks_count)
              << "\n";
}
