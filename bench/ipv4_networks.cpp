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

#include <chrono>
#include <fstream>
#include <iostream>
#include <random>
#include <vector>

using namespace bye_trie;
using namespace boost::asio::ip;

namespace {

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

std::pair<network_v4, uint16_t> parse_network_and_asn(std::string_view line) {
    auto const view = std::string_view{line};
    auto const addr_end = view.find(',');
    auto const addr = make_address_v4(view.substr(0, addr_end));

    auto const len_end = view.substr(addr_end + 1).find(',');
    auto const len = parse_int(view.substr(addr_end + 1, len_end));

    auto const asn = parse_int(view.substr(addr_end + 1 + len_end + 1));
    auto const network = make_network_v4(addr, len);

    return {network, asn};
}

std::chrono::nanoseconds benchmark(std::invocable auto&& f) {
    auto const start = std::chrono::steady_clock::now();
    f();
    return std::chrono::steady_clock::now() - start;
}

std::chrono::nanoseconds per_network(std::chrono::nanoseconds dur, size_t n) {
    return dur / n;
}

} // namespace

int main() {
    ByeTrieV4<long> trie;

    {
        std::vector<std::pair<network_v4, uint16_t>> networks;
        std::ifstream file("uniq_pfx_asn_dfz.csv");
        std::string line;
        while (std::getline(file, line)) {
            networks.push_back(parse_network_and_asn(line));
        }

        std::cout << "average insert time: "
                  << per_network(benchmark([&] {
                                     for (auto const& [network, asn] : networks) {
                                         trie.insert(network, asn).has_value();
                                     }
                                 }),
                                 networks.size())
                  << '\n';
    }

    {
        auto constexpr a = 100u;
        auto constexpr b = 255u + 1;
        auto constexpr c = 255u + 1;

        std::array<unsigned, 10> third_byte;
        std::generate(third_byte.begin(), third_byte.end(), [] {
            static std::uniform_int_distribution<unsigned> distr{1, 6};
            static std::mt19937 engine{0};
            return distr(engine);
        });

        auto const iter = [third_byte](auto f) {
            for (auto i = 0u; i < a; ++i) {
                for (auto first = 0u; first < b; ++first) {
                    for (auto second = 0u; second < c; ++second) {
                        for (auto third : third_byte) {
                            auto const network = make_network_v4(
                                    make_address_v4(Bits{first, 8}
                                                            .concatenated(Bits{second, 8})
                                                            .concatenated(Bits{third, 8})
                                                            .concatenated(Bits{first, 8})
                                                            .bits()),
                                    32);
                            f(network);
                        }
                    }
                }
            }
        };

        std::cout << "average match_longest time (prefix_len=32): "
                  << per_network(benchmark([&] {
                                     iter([&trie](auto network) {
                                         do_not_optimize(trie.match_longest(network));
                                     });
                                 }),
                                 100 * 256 * 256 * third_byte.size())
                  << "\n";

        std::cout << "average match_exact time (prefix_length=32): "
                  << per_network(benchmark([&] {
                                     iter([&trie](auto network) {
                                         do_not_optimize(trie.match_exact(network));
                                     });
                                 }),
                                 100 * 256 * 256 * third_byte.size())
                  << "\n";
    }
}
