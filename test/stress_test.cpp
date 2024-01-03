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

#include <catch2/catch_all.hpp>

#include <vector>

using namespace bye_trie;

TEST_CASE("Load big data and match every prefix", "[stress]") {
    std::vector<std::pair<Bits<uint32_t>, uint32_t>> prefixes;
    ByeTrie<uint32_t, long> trie;
    using Value = ByeTrie<uint32_t, long>::ValueType;

    uint32_t i = 0;
    Bits<uint32_t> bits{4, 8};
    while (i < 65'000) {
        prefixes.emplace_back(bits, i);
        REQUIRE(!trie.insert(prefixes.back().first, prefixes.back().second).has_value());
        ++i;
        bits += 32;
    }

    for (auto const& [prefix, value] : prefixes) {
        REQUIRE(*trie.match_exact(prefix) == value);
        REQUIRE(*trie.match_longest(prefix)
                == (std::pair<uint8_t, long>{prefix.len(), value}));
        REQUIRE(*trie.find_exact(prefix) == (Value{prefix, value}));
        REQUIRE(*trie.find_longest(prefix) == (Value{prefix, value}));
        REQUIRE(*trie.subs(prefix).begin() == (Value{prefix, value}));
    }
}
