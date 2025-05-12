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

#include "net_trie.h"
#include "util.h"

#include <bye_trie/bye_trie.h>

#include <boost/asio/ip/network_v4.hpp>
#include <boost/asio/ip/network_v6.hpp>

namespace bye_trie {

struct KeyAdapterV4 {
    using AdapteeType = boost::asio::ip::network_v4;
    using TargetType = uint32_t;

    static AdapteeType from_target(Bits<TargetType> x) {
        using namespace boost::asio::ip;
        return make_network_v4(address_v4(bytes_reversed<address_v4::bytes_type>(x.bits())), x.len());
    }

    static Bits<TargetType> to_target(AdapteeType x) {
        return Bits{bytes_reversed<uint32_t>(x.network().to_bytes()), x.prefix_length()};
    }

    static AdapteeType truncated(AdapteeType const& x, uint16_t len) noexcept {
        return AdapteeType{x.network(), len};
    }
};

struct KeyAdapterV6 {
    using AdapteeType = boost::asio::ip::network_v6;
    using TargetType = Uint128;

    static AdapteeType from_target(Bits<TargetType> x) {
        using namespace boost::asio::ip;
        return make_network_v6(address_v6(bytes_reversed<address_v6::bytes_type>(x.bits())), x.len());
    }

    static Bits<TargetType> to_target(AdapteeType x) {
        return Bits{bytes_reversed<Uint128>(x.network().to_bytes()), x.prefix_length()};
    }

    static AdapteeType truncated(AdapteeType const& x, uint16_t len) noexcept {
        return AdapteeType{x.network(), len};
    }
};

class Network {
public:
    Network(boost::asio::ip::network_v4 const& net)
            : inner{net} {
    }

    Network(boost::asio::ip::network_v6 const& net)
            : inner{net} {
    }

    bool is_v4() const {
        return inner.index() == 0;
    }

    explicit operator boost::asio::ip::network_v4() const {
        assert(is_v4());
        return std::get<0>(inner);
    }

    explicit operator boost::asio::ip::network_v6() const {
        assert(!is_v4());
        return std::get<1>(inner);
    }

    Network canonical() const {
        return std::visit([](auto const& x) -> Network { return x.canonical(); }, inner);
    }

    bool operator==(Network const& rhs) const = default;

    friend std::ostream& operator<<(std::ostream& os, Network const& x) {
        return std::visit([&](auto const& x) -> std::ostream& { return os << x; }, x.inner);
    }

private:
    std::variant<boost::asio::ip::network_v4, boost::asio::ip::network_v6> inner;
};

struct KeyAdapterV46 {
    using AdapteeType = Network;

    static bool is_first(Network const& x) {
        return x.is_v4();
    }

    static auto as_first(Network const& x) {
        return static_cast<boost::asio::ip::network_v4>(x);
    }

    static auto as_second(Network const& x) {
        return static_cast<boost::asio::ip::network_v6>(x);
    }

    static auto from(boost::asio::ip::network_v4 const& x) {
        return Network{x};
    }

    static auto from(boost::asio::ip::network_v6 const& x) {
        return Network{x};
    }
};

template <class T>
using BoostTrieSubsIteratorV4 = NetTrieSubsIterator<KeyAdapterV4, HeapBacked<T>>;

template <class T>
using BoostTrieIteratorV4 = NetTrieIterator<KeyAdapterV4, HeapBacked<T>>;

template <class T>
using BoostTrieV4 = NetTrie<KeyAdapterV4, HeapBacked<T>>;

template <class T>
using BoostTrieSubsIteratorV6 = NetTrieSubsIterator<KeyAdapterV6, HeapBacked<T>>;

template <class T>
using BoostTrieIteratorV6 = NetTrieIterator<KeyAdapterV6, HeapBacked<T>>;

template <class T>
using BoostTrieV6 = NetTrie<KeyAdapterV6, HeapBacked<T>>;

template <class T>
using BoostTrieSubsIteratorV46 =
        EitherNetTrieSubsIterator<KeyAdapterV46, BoostTrieSubsIteratorV4<T>, BoostTrieIteratorV6<T>>;

template <class T>
using BoostTrieIteratorV46 = JoinedNetTrieIterator<KeyAdapterV46, BoostTrieIteratorV4<T>, BoostTrieIteratorV6<T>>;

template <class T>
using BoostTrieV46 = JoinedNetTrie<KeyAdapterV46, BoostTrieV4<T>, BoostTrieV6<T>>;

} // namespace bye_trie
