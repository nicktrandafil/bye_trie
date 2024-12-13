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

#include <bye_trie/bye_trie.h>

#include <boost/asio/ip/network_v4.hpp>
#include <boost/asio/ip/network_v6.hpp>

#include <ostream>
#include <utility>

namespace bye_trie {

using Uint128 = __uint128_t;

namespace detail {

// clang-format off
inline uint8_t reverse_byte(uint8_t x) noexcept {
    static const uint8_t table[] = {
        0x00, 0x80, 0x40, 0xc0, 0x20, 0xa0, 0x60, 0xe0,
        0x10, 0x90, 0x50, 0xd0, 0x30, 0xb0, 0x70, 0xf0,
        0x08, 0x88, 0x48, 0xc8, 0x28, 0xa8, 0x68, 0xe8,
        0x18, 0x98, 0x58, 0xd8, 0x38, 0xb8, 0x78, 0xf8,
        0x04, 0x84, 0x44, 0xc4, 0x24, 0xa4, 0x64, 0xe4,
        0x14, 0x94, 0x54, 0xd4, 0x34, 0xb4, 0x74, 0xf4,
        0x0c, 0x8c, 0x4c, 0xcc, 0x2c, 0xac, 0x6c, 0xec,
        0x1c, 0x9c, 0x5c, 0xdc, 0x3c, 0xbc, 0x7c, 0xfc,
        0x02, 0x82, 0x42, 0xc2, 0x22, 0xa2, 0x62, 0xe2,
        0x12, 0x92, 0x52, 0xd2, 0x32, 0xb2, 0x72, 0xf2,
        0x0a, 0x8a, 0x4a, 0xca, 0x2a, 0xaa, 0x6a, 0xea,
        0x1a, 0x9a, 0x5a, 0xda, 0x3a, 0xba, 0x7a, 0xfa,
        0x06, 0x86, 0x46, 0xc6, 0x26, 0xa6, 0x66, 0xe6,
        0x16, 0x96, 0x56, 0xd6, 0x36, 0xb6, 0x76, 0xf6,
        0x0e, 0x8e, 0x4e, 0xce, 0x2e, 0xae, 0x6e, 0xee,
        0x1e, 0x9e, 0x5e, 0xde, 0x3e, 0xbe, 0x7e, 0xfe,
        0x01, 0x81, 0x41, 0xc1, 0x21, 0xa1, 0x61, 0xe1,
        0x11, 0x91, 0x51, 0xd1, 0x31, 0xb1, 0x71, 0xf1,
        0x09, 0x89, 0x49, 0xc9, 0x29, 0xa9, 0x69, 0xe9,
        0x19, 0x99, 0x59, 0xd9, 0x39, 0xb9, 0x79, 0xf9,
        0x05, 0x85, 0x45, 0xc5, 0x25, 0xa5, 0x65, 0xe5,
        0x15, 0x95, 0x55, 0xd5, 0x35, 0xb5, 0x75, 0xf5,
        0x0d, 0x8d, 0x4d, 0xcd, 0x2d, 0xad, 0x6d, 0xed,
        0x1d, 0x9d, 0x5d, 0xdd, 0x3d, 0xbd, 0x7d, 0xfd,
        0x03, 0x83, 0x43, 0xc3, 0x23, 0xa3, 0x63, 0xe3,
        0x13, 0x93, 0x53, 0xd3, 0x33, 0xb3, 0x73, 0xf3,
        0x0b, 0x8b, 0x4b, 0xcb, 0x2b, 0xab, 0x6b, 0xeb,
        0x1b, 0x9b, 0x5b, 0xdb, 0x3b, 0xbb, 0x7b, 0xfb,
        0x07, 0x87, 0x47, 0xc7, 0x27, 0xa7, 0x67, 0xe7,
        0x17, 0x97, 0x57, 0xd7, 0x37, 0xb7, 0x77, 0xf7,
        0x0f, 0x8f, 0x4f, 0xcf, 0x2f, 0xaf, 0x6f, 0xef,
        0x1f, 0x9f, 0x5f, 0xdf, 0x3f, 0xbf, 0x7f, 0xff,
    };
    return table[x];
}
// clang-format on

inline uint32_t reverse_bits_of_bytes(
        boost::asio::ip::address_v4::bytes_type val) noexcept {
    std::for_each(val.begin(), val.end(), [](auto& byte) { byte = reverse_byte(byte); });
    return std::bit_cast<uint32_t>(val);
}

inline Uint128 reverse_bits_of_bytes(
        boost::asio::ip::address_v6::bytes_type val) noexcept {
    std::for_each(val.begin(), val.end(), [](auto& byte) { byte = reverse_byte(byte); });
    return std::bit_cast<Uint128>(val);
}

Bits<uint32_t> to_bits(boost::asio::ip::network_v4 prefix) noexcept {
    return Bits<uint32_t>{reverse_bits_of_bytes(prefix.network().to_bytes()),
                          static_cast<uint8_t>(prefix.prefix_length())};
};

boost::asio::ip::network_v4 to_network(Bits<uint32_t> bits) noexcept {
    using namespace boost::asio::ip;
    return make_network_v4(
            address_v4(std::bit_cast<address_v4::bytes_type>(reverse_bits_of_bytes(
                    std::bit_cast<address_v4::bytes_type>(bits.bits())))),
            bits.len());
}

Bits<Uint128> to_bits(boost::asio::ip::network_v6 prefix) noexcept {
    return Bits<Uint128>{reverse_bits_of_bytes(prefix.network().to_bytes()),
                         static_cast<uint8_t>(prefix.prefix_length())};
};

boost::asio::ip::network_v6 to_network(Bits<Uint128> bits) noexcept {
    using namespace boost::asio::ip;
    return make_network_v6(
            address_v6(std::bit_cast<address_v6::bytes_type>(reverse_bits_of_bytes(
                    std::bit_cast<address_v6::bytes_type>(bits.bits())))),
            bits.len());
}

} // namespace detail

inline constexpr unsigned stride = 5;

template <class IpNet, UnsignedIntegral IntType, TrivialLittleObject T>
class IpNetSubsIterator {
    using Inner = SubsIterator<IntType, T, stride>;

public:
    IpNetSubsIterator() = default;

    explicit IpNetSubsIterator(Inner&& x)
            : inner{x} {
    }

    using iterator_category = std::forward_iterator_tag;
    using value_type = T;
    using difference_type = std::ptrdiff_t;
    using pointer = value_type*;
    using reference = value_type&;

    IpNet key() const {
        auto const inner_key = inner.key();
        return detail::to_network(inner_key);
    }

    reference operator*() {
        return *inner;
    }

    pointer operator->() const {
        return inner.operator->();
    }

    IpNetSubsIterator& operator++() {
        ++inner;
        return *this;
    }

    bool operator==(IpNetSubsIterator const& rhs) const = default;

private:
    Inner inner;
};

template <class IpNet, UnsignedIntegral IntType, class T, class Allocator>
class IpNetByeTrie : private ByeTrie<IntType, T, Allocator, stride> {
    using Base = ByeTrie<IntType, T, Allocator, stride>;

public:
    using Base::Base;
    using Base::size;

    auto insert(IpNet const& prefix, T value) {
        return Base::insert(detail::to_bits(prefix), value);
    }

    auto replace(IpNet const& prefix, T value) {
        return Base::replace(detail::to_bits(prefix), value);
    }

    auto match_exact(IpNet const& prefix) const {
        return Base::match_exact(detail::to_bits(prefix));
    }

    std::optional<std::pair<IpNet, T>> match_longest(IpNet const& prefix) const {
        auto const res = Base::match_longest(detail::to_bits(prefix));

        if (!res) {
            return std::nullopt;
        }

        auto const [prefix_length, value] = *res;

        return std::pair{IpNet{prefix.address(), static_cast<uint16_t>(prefix_length)},
                         value};
    }

    auto subs(IpNet const& prefix) const {
        return IpNetSubsIterator<IpNet, IntType, T>{Base::subs(detail::to_bits(prefix))};
    }

    std::vector<std::pair<IpNet, T>> supers(IpNet const& prefix) const {
        std::vector<std::pair<IpNet, T>> ret;
        ret.reserve(sizeof(IntType) * CHAR_BIT);
        visit_supers(prefix,
                     [&ret](auto prefix, auto v) { ret.emplace_back(prefix, v); });
        std::reverse(begin(ret), end(ret));
        return ret;
    }

    template <class F>
    void visit_supers(IpNet const& prefix, F const& on_super) const {
        Base::visit_supers(detail::to_bits(prefix), [on_super](auto prefix, auto v) {
            on_super(detail::to_network(prefix), v);
        });
    }
};

template <class T, class Allocator = SystemAllocator>
class ByeTrieV4
        : public IpNetByeTrie<boost::asio::ip::network_v4, uint32_t, T, Allocator> {
    using Base = IpNetByeTrie<boost::asio::ip::network_v4, uint32_t, T, Allocator>;
    using Base::Base;
};

template <class T>
using IpNetSubsIteratorV4 = IpNetSubsIterator<boost::asio::ip::network_v4, uint32_t, T>;

template <class T, class Allocator = SystemAllocator>
class ByeTrieV6
        : public IpNetByeTrie<boost::asio::ip::network_v6, Uint128, T, Allocator> {
    using Base = IpNetByeTrie<boost::asio::ip::network_v6, Uint128, T, Allocator>;
    using Base::Base;
};

template <class T>
using IpNetSubsIteratorV6 = IpNetSubsIterator<boost::asio::ip::network_v6, Uint128, T>;

} // namespace bye_trie
