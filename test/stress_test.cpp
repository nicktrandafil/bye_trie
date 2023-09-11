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
#include "bye_trie/ip_net_bye_trie.h"

#include <catch2/catch_all.hpp>

#include <forward_list>
#include <fstream>
#include <iostream>

using namespace bye_trie;

TEST_CASE("Load big data and match every prefix", "[stress]") {
    std::forward_list<std::pair<Bits<uint32_t>, uint32_t>> prefixes;
    ByeTrie<uint32_t, long> trie;
    using Value = ByeTrie<uint32_t, long>::ValueType;

    uint32_t i = 0;
    Bits<uint32_t> bits{4, 8};
    while (i < 65'000) {
        prefixes.emplace_front(bits, i);
        REQUIRE(!trie.insert(prefixes.front().first, prefixes.front().second)
                         .has_value());
        ++i;
        bits += 32;
    }

    for (auto const& [prefix, value] : prefixes) {
        REQUIRE(*trie.match_exact(prefix) == value);
        REQUIRE(*trie.match_longest(prefix)
                == (std::pair<uint8_t, long>{prefix.len(), value}));
        REQUIRE(*trie.find_exact(prefix) == (Value{prefix, value}));
        REQUIRE(*trie.find_longest(prefix) == (Value{prefix, value}));
    }
}

static uint16_t parse_int(std::string_view view) {
    uint16_t result = 0;
    for (auto const c : view) {
        result *= 10;
        result += c - '0';
    }
    return result;
}

template <class T>
static inline __attribute__((always_inline)) void do_not_optimize(T&& value) noexcept {
    asm volatile("" : "+m"(value) : : "memory");
}

TEST_CASE("Real data test", "[stress]") {
    std::vector<std::pair<boost::asio::ip::network_v4, uint16_t>> prefixes;
    ByeTrieV4<long> trie;

    std::ifstream file("uniq_pfx_asn_dfz.csv");
    std::string line;
    while (std::getline(file, line)) {
        auto const view = std::string_view{line};
        auto const addr_end = view.find(',');
        auto const addr = boost::asio::ip::make_address_v4(view.substr(0, addr_end));

        auto const len_end = view.substr(addr_end + 1).find(',');
        auto const len = parse_int(view.substr(addr_end + 1, len_end));

        auto const asn = parse_int(view.substr(addr_end + 1 + len_end + 1));

        auto const prefix = boost::asio::ip::make_network_v4(addr, len);

        prefixes.emplace_back(prefix, asn);
    }

    auto start = std::chrono::steady_clock::now();
    for (auto const& [prefix, value] : prefixes) {
        trie.insert(prefix, value).has_value();
    }

    std::cout << "insert time average ns: "
              << std::chrono::duration_cast<std::chrono::nanoseconds>(
                         std::chrono::steady_clock::now() - start)
                                 .count()
                         / static_cast<unsigned>(prefixes.size())
              << '\n';

    start = std::chrono::steady_clock::now();
    {
        auto inet_max = 255u;
        auto len_max = 32u;

        for (auto i_net = 0u; i_net <= inet_max; ++i_net) {
            for (unsigned short s_len = 0; s_len <= len_max; ++s_len) {
                for (auto ii_net = 0u; ii_net <= inet_max; ++ii_net) {
                    auto const bits = Bits{i_net, 8}
                                              .concatenated(Bits{ii_net, 8})
                                              .concatenated(Bits{0u, 16});
                    auto value = trie.match_longest(boost::asio::ip::make_network_v4(
                            boost::asio::ip::make_address_v4(bits.bits()), s_len));
                    do_not_optimize(value);
                }
            }
        }
        auto const end = std::chrono::steady_clock::now();

        auto const dur = end - start;
        auto const n = inet_max * inet_max * len_max;
        auto const ns =
                std::chrono::duration_cast<std::chrono::nanoseconds>(dur).count() / n;

        std::cout << "match longest average ns: " << ns << '\n';
    }
}
