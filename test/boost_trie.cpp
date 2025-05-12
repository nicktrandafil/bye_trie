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

#include "boost_trie.h"

#include <catch2/catch_all.hpp>

#include <fstream>
#include <ranges>

using namespace bye_trie;
using namespace boost::asio::ip;

template <class T, class F>
auto map(std::optional<T> x, F f) -> std::optional<std::decay_t<decltype(f(*x))>> {
    if (x) {
        return f(*x);
    } else {
        return std::nullopt;
    }
}

namespace Catch {

template <class A, class B>
struct StringMaker<std::pair<A, B>> {
    static std::string convert(std::pair<A, B> const& value) {
        std::ostringstream oss;
        oss << "(" << value.first << ", " << value.second << ")";
        return oss.str();
    }
};

template <class A>
struct StringMaker<std::optional<A>> {
    static std::string convert(std::optional<A> const& value) {
        std::ostringstream oss;
        if (value) {
            oss << StringMaker<A>::convert(*value);
        } else {
            oss << "<empty>";
        }
        return oss.str();
    }
};

} // namespace Catch

template <class T, class N>
struct DataV4 {
    using Trie = T;
    using Net = N;
    using Value = typename T::ValueType;

    Trie trie;

    Net zero = make_network_v4("0.0.0.0/0");

    Net p0 = make_network_v4("26.0.0.0/8");
    Net p1 = make_network_v4("26.1.0.0/16");

    Net root = make_network_v4("25.0.0.0/8");
    Net sub1 = make_network_v4("25.1.0.0/16");
    Net sub1_2 = make_network_v4("25.1.2.0/24");
    Net leaf = make_network_v4("25.1.2.0/24");
    Net sub2 = make_network_v4("25.2.0.0/16");
};

template <class T, class N>
struct DataV6 {
    using Trie = T;
    using Net = N;
    using Value = typename T::ValueType;

    Trie trie;

    Net zero = make_network_v6("::/0");

    Net p0 = make_network_v6("0100::0/8");
    Net p1 = make_network_v6("0101::0/16");

    Net root = make_network_v6("0102::/16");
    Net sub1 = make_network_v6("0102::1:0:0:0/80");
    Net sub1_2 = make_network_v6("0102::1:0002:0:0/96");
    Net leaf = make_network_v6("0102::1:2:0:0/96");
    Net sub2 = make_network_v6("0102::2:0:0:0/80");
};

struct Data1 : DataV4<BoostTrieV4<long>, network_v4> {
    long v0 = 0;
    long v1 = 1;
    long v2 = 2;
    long v3 = 3;
    long v4 = 4;
};

struct Data1Little : DataV4<BoostTrieV4<char>, network_v4> {
    char v0 = 0;
    char v1 = 1;
    char v2 = 2;
    char v3 = 3;
    char v4 = 4;
};

struct Data1Big : DataV4<BoostTrieV4<std::string>, network_v4> {
    std::string v0 = "0";
    std::string v1 = "1";
    std::string v2 = "2";
    std::string v3 = "3";
    std::string v4 = "4";
};

struct Data2 : DataV6<BoostTrieV6<long>, network_v6> {
    long v0 = 0;
    long v1 = 1;
    long v2 = 2;
    long v3 = 3;
    long v4 = 4;
};

struct Data3 : DataV4<BoostTrieV46<long>, Network> {
    long v0 = 0;
    long v1 = 1;
    long v2 = 2;
    long v3 = 3;
    long v4 = 4;
};

struct Data4 : DataV6<BoostTrieV46<long>, Network> {
    long v0 = 0;
    long v1 = 1;
    long v2 = 2;
    long v3 = 3;
    long v4 = 4;
};

using DataSet = std::tuple<Data1, Data1Little, Data1Big, Data2, Data3, Data4>;

TEMPLATE_LIST_TEST_CASE(
        "Mostly to ensure compilation tests. We know that the wrapper does nothing but "
        "`reverse_bits_of_bytes`",
        "[white-box][BoostTrie]",
        DataSet) {
    TestType d;
    REQUIRE(d.trie.insert(d.p0, d.v1).second);
    REQUIRE(*d.trie.match_exact(d.p0) == d.v1);
    REQUIRE(map(d.trie.match_longest(d.p0), [](auto x) { return std::pair{x.first, *x.second}; })
            == std::pair{d.p0, d.v1});
    REQUIRE(++d.trie.subs(d.p0) == typename TestType::Trie::SubsIterator{});
}

TEMPLATE_LIST_TEST_CASE("Indirect testing of IteratorV4::operator*()", "[white-box]", DataSet) {
    TestType d;
    REQUIRE(d.trie.insert(d.p0, d.v1).second);
    REQUIRE(d.trie.subs(d.p0).key() == d.p0);
    REQUIRE(*d.trie.subs(d.p0) == d.v1);
}

TEMPLATE_LIST_TEST_CASE("Visit super nets", "", DataSet) {
    TestType d;
    d.trie.insert(d.root, d.v1);
    d.trie.insert(d.sub1, d.v1);
    d.trie.insert(d.sub2, d.v2);
    d.trie.insert(d.leaf, d.v3);

    std::vector<std::pair<typename TestType::Net, typename TestType::Value>> expected{
            {d.root, d.v1}, {d.sub1, d.v1}, {d.leaf, d.v3}};

    std::vector<std::pair<typename TestType::Net, typename TestType::Value>> actual;
    d.trie.visit_supers(d.leaf, [&](auto p, auto v) { actual.emplace_back(p, v); });

    REQUIRE(expected == actual);
}

TEMPLATE_LIST_TEST_CASE("move operators", "[special-operators]", DataSet) {
    TestType d;
    d.trie.insert(d.p0, d.v1);

    auto trie = std::move(d.trie);
    REQUIRE(*trie.match_exact(d.p0) == d.v1);
    REQUIRE(d.trie.empty());
}

TEMPLATE_LIST_TEST_CASE("copy operators", "[special-operators]", DataSet) {
    TestType d;
    d.trie.insert(d.p0, d.v1);

    auto trie2 = d.trie;
    REQUIRE(*trie2.match_exact(d.p0) == d.v1);
    REQUIRE(*d.trie.match_exact(d.p0) == d.v1);

    typename TestType::Trie trie3;
    trie3.insert(d.p1, d.v2);
    trie3 = trie2;
    // REQUIRE(!trie3.match_exact(d.p1));
    // REQUIRE(*trie3.match_exact(d.p0) == d.v1);
}

TEMPLATE_LIST_TEST_CASE(
        "insert; we can modify the original value through returned pointer; insertion returns a pointer to the value "
        "in the trie",
        "",
        DataSet) {
    TestType d;
    typename TestType::Trie trie;
    auto r = trie.insert(d.p0, d.v1);
    REQUIRE(r.second);
    REQUIRE(*r.first == d.v1);

    *r.first = d.v2;
    r = trie.insert(d.p0, d.v3);
    REQUIRE(!r.second);
    REQUIRE(*r.first == d.v2);
}

TEMPLATE_LIST_TEST_CASE("erase", "", DataSet) {
    TestType d;
    d.trie.insert(d.p0, d.v1);
    REQUIRE(d.trie.erase(d.p0));
    REQUIRE(!d.trie.erase(d.p0));
}

TEMPLATE_LIST_TEST_CASE("iter", "", DataSet) {
    TestType d;
    d.trie.insert(d.p0, d.v1);
    for (auto it = d.trie.begin(); it != d.trie.end(); ++it) {
        REQUIRE(it.key() == d.p0);
        REQUIRE(*it == d.v1);
    }
}

TEMPLATE_LIST_TEST_CASE("match_exact", "", DataSet) {
    TestType d;
    d.trie.insert(d.p0, d.v1);
    REQUIRE(d.trie.match_exact(d.p0));
    REQUIRE(!d.trie.match_exact(d.p1));
}

TEMPLATE_LIST_TEST_CASE("match_exact_iter", "", DataSet) {
    TestType d;
    d.trie.insert(d.p0, d.v1);
    auto it = d.trie.match_exact_iter(d.p0);
    REQUIRE(it != d.trie.end());
    REQUIRE(it.key() == d.p0);
    REQUIRE(*it == d.v1);

    REQUIRE(d.trie.match_exact_iter(d.p1) == d.trie.end());
}

TEMPLATE_LIST_TEST_CASE("iter_super", "", DataSet) {
    TestType d;
    d.trie.insert(d.root, d.v1);
    d.trie.insert(d.sub1, d.v1);
    auto it = d.trie.match_exact_iter(d.sub1);

    REQUIRE(it.key() == d.sub1);
    REQUIRE(it.next_super());
    REQUIRE(it.key() == d.root);
    REQUIRE(!it.next_super());
}

TEMPLATE_LIST_TEST_CASE("iter_super_zero", "", DataSet) {
    TestType d;
    d.trie.insert(d.zero, d.v1);
    d.trie.insert(d.root, d.v1);
    d.trie.insert(d.sub1, d.v2);
    auto it = d.trie.match_exact_iter(d.sub1);

    REQUIRE(it.key() == d.sub1);
    REQUIRE(it.next_super());
    REQUIRE(it.key() == d.root);
    REQUIRE(it.next_super());
    REQUIRE(it.key() == d.zero);
    REQUIRE(!it.next_super());
}

TEMPLATE_LIST_TEST_CASE("match_longest", "", DataSet) {
    TestType d;
    d.trie.insert(d.root, d.v1);
    auto const res = d.trie.match_longest(d.sub1);
    REQUIRE(res->first.canonical() == d.root);
    REQUIRE(*res->second == d.v1);
}

TEMPLATE_LIST_TEST_CASE("match_longest_iter", "", DataSet) {
    TestType d;
    d.trie.insert(d.root, d.v1);
    auto const it = d.trie.match_longest_iter(d.sub1);
    REQUIRE(it.key() == d.root);
    REQUIRE(*it == d.v1);
}

TEMPLATE_LIST_TEST_CASE("subs", "", DataSet) {
    TestType d;
    d.trie.insert(d.p0, d.v1);
    for (auto it = d.trie.subs(d.p0); it != typename TestType::Trie::SubsIterator{}; ++it) {
        REQUIRE(it.key() == d.p0);
        REQUIRE(*it == d.v1);
        *it = d.v2;
    }
    REQUIRE(*d.trie.match_exact(d.p0) == d.v2);
}

TEMPLATE_LIST_TEST_CASE("go_to_longest", "", DataSet) {
    TestType d;
    d.trie.insert(d.root, d.v1);
    d.trie.insert(d.sub1, d.v1);
    auto it = d.trie.subs(d.root);
    it.go_to_longest(d.sub1_2);
    REQUIRE(it.key() == d.sub1);
    ++it;
    REQUIRE(it == typename TestType::Trie::SubsIterator{});
}

TEMPLATE_LIST_TEST_CASE("visit_supers", "", DataSet) {
    TestType d;
    d.trie.insert(d.zero, d.v1);
    d.trie.insert(d.root, d.v1);
    d.trie.insert(d.sub1, d.v2);
    std::vector<typename TestType::Net> actual;
    std::vector<typename TestType::Net> const expected{d.zero, d.root, d.sub1};
    d.trie.visit_supers(d.sub1, [&actual](auto prefix, auto) { actual.push_back(typename TestType::Net(prefix)); });
    REQUIRE(actual == expected);
}

TEST_CASE("playground") {
    auto const p1 = make_network_v4("1.1.1.0/24");
    auto const p2 = make_network_v4("1.1.1.1/24");
    REQUIRE(p1 != p2);
}

void read_ipv4(BoostTrieV46<long>& trie) {
    using namespace std;
    std::ifstream file{"uniq_pfx_asn_dfz.csv"};
    assert(!!file);
    long count = 0;
    for (auto const x :
         std::ranges::subrange(std::istream_iterator<std::string>(file), std::istream_iterator<std::string>())
                 | std::views::transform([](auto const& x) {
                       auto const v = static_cast<std::string_view>(x);
                       auto const e1 = v.find(',');
                       auto const e2 = v.find(',', e1 + 1);
                       unsigned len;
                       if (std::from_chars(&v[e1 + 1], &v[e2 - e1 + 1], len).ec != std::errc{}) {
                           throw std::runtime_error{"failed to parse the prefix len"};
                       }
                       return make_network_v4(make_address_v4(v.substr(0, e1)), len);
                   })) {
        if (trie.insert(x, count).second) {
            ++count;
        }
    }
}

TEST_CASE("iterate erase") {
    BoostTrieV46<long> trie;
    read_ipv4(trie);
    auto const size = trie.size();

    for (auto it = trie.begin(); it != trie.end();) {
        if (auto const key = it.key(); *it % 2) {
            static_cast<void>(key);
            it = trie.erase(it);
        } else {
            ++it;
        }
    }

    REQUIRE(trie.size() == (size + 1) / 2);
}

TEST_CASE("iterate erase subs") {
    BoostTrieV46<long> trie;
    read_ipv4(trie);
    auto const size = trie.size();

    for (auto it = trie.subs(make_network_v4("0.0.0.0/0")); it != BoostTrieV46<long>::SubsIterator{};) {
        if (auto const key = it.key(); *it % 2) {
            static_cast<void>(key);
            it = trie.erase(it);
        } else {
            ++it;
        }
    }

    REQUIRE(trie.size() == (size + 1) / 2);
}
