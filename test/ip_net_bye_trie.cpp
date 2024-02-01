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

#include "bye_trie/ip_net_bye_trie.h"

#include "pair.h"

#include <catch2/catch_all.hpp>

using namespace bye_trie;
using namespace boost::asio::ip;

TEST_CASE("Reversing bits of bytes", "[reverse_bits_of_bytes]") {
    SECTION("uint32_t") {
        REQUIRE(detail::reverse_bits_of_bytes(std::bit_cast<address_v4::bytes_type>(
                        0b00000000'00000000'10100000'01010000))
                == 0b00000000'00000000'00000101'00001010);
    }

    SECTION("Uint128") {
        REQUIRE(detail::reverse_bits_of_bytes(std::bit_cast<address_v6::bytes_type>(
                        Uint128{0b00000000'00000000'10100000'01010000}))
                == Uint128{0b00000000'00000000'00000101'00001010});
    }
}

TEST_CASE(
        "Mostly to ensure compilation tests. We know that the wrapper does nothing but "
        "`reverse_bits_of_bytes`",
        "[white-box]") {
    SECTION("ByeTrieV4") {
        ByeTrieV4<long> trie;
        REQUIRE(trie.insert(make_network_v4("0.0.0.0/0"), 0) == std::nullopt);

        REQUIRE(trie.replace(make_network_v4("0.0.0.0/0"), 0) == 0);
        REQUIRE(trie.match_exact(make_network_v4("0.0.0.0/0")) == 0);
        REQUIRE(trie.match_longest(make_network_v4("1.2.3.4/0"))
                == (std::pair{make_network_v4("1.2.3.4/0"), 0l}));

        auto const subs = trie.subs(make_network_v4("0.0.0.0/0"));
        REQUIRE(++subs.begin() == subs.end());
    }

    SECTION("ByeTrieV6") {
        ByeTrieV6<long> trie;
        REQUIRE(trie.insert(make_network_v6("::/0"), 0) == std::nullopt);

        REQUIRE(trie.replace(make_network_v6("::/0"), 0) == 0);
        REQUIRE(trie.match_exact(make_network_v6("::/0")) == 0);
        REQUIRE(trie.match_longest(make_network_v6("1::/0"))
                == (std::pair{make_network_v6("1::/0"), 0l}));

        auto const subs = trie.subs(make_network_v6("::0/0"));
        REQUIRE(++subs.begin() == subs.end());
    }
}

TEST_CASE("Indirect testing of IteratorV4::operator*()", "[white-box]") {
    SECTION("ByeTrieV4") {
        ByeTrieV4<long> trie;
        using Value = ByeTrieSubsV4<long>::ValueType;
        REQUIRE(trie.insert(make_network_v4("25.0.0.0/8"), 1) == std::nullopt);

        REQUIRE(*trie.subs(make_network_v4("25.1.0.0/8")).begin()
                == Value{.prefix = make_network_v4("25.0.0.0/8"), .value = 1});
    }

    SECTION("ByeTrieV6") {
        ByeTrieV6<long> trie;
        using Value = ByeTrieSubsV6<long>::ValueType;
        REQUIRE(trie.insert(make_network_v6("::/0"), 1) == std::nullopt);

        REQUIRE(*trie.subs(make_network_v6("::/0")).begin()
                == Value{.prefix = make_network_v6("::/0"), .value = 1});
    }
}

TEST_CASE("Visit super nets", "") {
    SECTION("ByeTrieV4") {
        ByeTrieV4<long> trie;
        trie.insert(make_network_v4("25.0.0.0/8"), 1);
        trie.insert(make_network_v4("25.1.0.0/16"), 2);
        trie.insert(make_network_v4("25.2.0.0/16"), 3);
        trie.insert(make_network_v4("25.1.2.0/24"), 4);

        std::vector<Pair<boost::asio::ip::network_v4, long>> actual,
                expected{{make_network_v4("25.0.0.0/8"), 1},
                         {make_network_v4("25.1.0.0/16"), 2},
                         {make_network_v4("25.1.2.0/24"), 4}};

        trie.visit_supers(make_network_v4("25.1.2.0/24"),
                          [&](auto p, auto v) { actual.emplace_back(p, v); });

        REQUIRE(expected == actual);
    }

    SECTION("ByeTrieV6") {
        ByeTrieV6<long> trie;
        trie.insert(make_network_v6("::/0"), 1);
        trie.insert(make_network_v6("::1:0:0:0/80"), 2);
        trie.insert(make_network_v6("::2:0:0:0/80"), 3);
        trie.insert(make_network_v6("::1:2:0:0/96"), 4);

        std::vector<Pair<boost::asio::ip::network_v6, long>> actual,
                expected{{make_network_v6("::/0"), 1},
                         {make_network_v6("::1:0:0:0/80"), 2},
                         {make_network_v6("::1:2:0:0/96"), 4}};

        trie.visit_supers(make_network_v6("::1:2:0:0/96"),
                          [&](auto p, auto v) { actual.emplace_back(p, v); });

        REQUIRE(expected == actual);
    }
}
