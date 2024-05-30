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

#pragma once

#include <algorithm>
#include <array>
#include <bit>
#include <cassert>
#include <climits>
#include <concepts>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <optional>
#include <ostream>
#include <span>
#include <type_traits>
#include <utility>
#include <vector>

static_assert(sizeof(void*) == 8, "64-bit only");

namespace bye_trie {

/// @defgroup group-datatypes Data types
/// Data types provided by the library.

struct MemBlk {
    bool operator==(MemBlk const&) const noexcept = default;
    void* ptr;
    size_t len;
};

template <class T>
concept UnsignedIntegral = std::unsigned_integral<T>
                        || (sizeof(T) <= 16 && std::is_trivial_v<T> && requires(T val) {
                               { ++val };
                               { val == val };
                               { val << 0 };
                               { val >> 0 };
                           });

template <UnsignedIntegral T>
class Bits {
    static constexpr auto int_bit_count = sizeof(T) * CHAR_BIT;

public:
    constexpr Bits()
            : bits_{}
            , len_{} {
    }

    constexpr Bits(T bits, uint8_t len) noexcept
            : bits_(bits)
            , len_(len) {
        assert(len <= int_bit_count);
    }

    constexpr uint8_t len() const noexcept {
        return len_;
    }

    constexpr T bits() const noexcept {
        return bits_;
    }

    constexpr T value() const noexcept {
        assert(len_ <= int_bit_count);
        return (len_ == int_bit_count) ? bits_ : (bits_ & ((T(1) << len_) - 1));
    }

    Bits suffix(uint8_t offset) const noexcept {
        assert(offset < int_bit_count);
        return Bits{bits_ >> offset, static_cast<uint8_t>(len_ - offset)};
    }

    Bits prefix(uint8_t len) const noexcept {
        assert(len < int_bit_count);
        return Bits{(bits_ & ((T(1) << len) - 1)), len};
    }

    Bits sub(uint8_t offset, uint8_t len) const noexcept {
        assert(offset + len <= len_);
        return Bits{take_slice(bits_, offset, len), len};
    }

    Bits concatenated(Bits slice) const noexcept {
        assert(static_cast<uint8_t>(len_ + slice.len()) <= int_bit_count);
        return Bits{bits_ | ((len_ == int_bit_count) ? 0 : (slice.value() << len_)),
                    static_cast<uint8_t>(len_ + slice.len())};
    }

    bool operator==(Bits const& rhs) const noexcept {
        return len_ == rhs.len_ && value() == rhs.value();
    }

    /// \post UB when `len() >= sizeof(T) * CHAR_BIT`
    constexpr Bits& operator++() noexcept {
        if (value() == static_cast<T>(((1 << len_) - 1))) {
            ++len_;
            bits_ = 0;
        } else {
            ++bits_;
        }
        return *this;
    }

    /// \post UB when `len() >= sizeof(T) * CHAR_BIT`
    Bits& operator+=(T rhs) noexcept {
        bits_ += rhs;

        if (auto const len = std::bit_width(bits_); len > len_) {
            len_ = len;
            bits_ = 0;
        }

        return *this;
    }

    std::pair<Bits, Bits> split_at(uint8_t offset) const noexcept {
        return {prefix(offset), suffix(offset)};
    }

    friend std::ostream& operator<<(std::ostream& os, Bits val) noexcept {
        using NotCharType = std ::conditional_t<sizeof(T) == 1, int, T>;
        return os << "Bits{" << static_cast<NotCharType>(val.bits_) << ", "
                  << static_cast<int>(val.len_) << "}";
    }

private:
    static constexpr inline T take_slice(T value, uint8_t start, uint8_t len) noexcept {
        assert(start < sizeof(T) * CHAR_BIT);
        assert(start + len <= sizeof(T) * CHAR_BIT);
        return (len == sizeof(T) * CHAR_BIT) ? (value >> start)
                                             : ((value >> start) & ((T(1) << len) - 1));
    }

private:
    T bits_;
    uint8_t len_;
};

using Uint128 = __uint128_t;

namespace detail {

constexpr void debug_assert(bool expr) {
    if (std::is_constant_evaluated()) {
        if (!expr) {
            throw 0;
        }
    } else {
        assert(expr);
    }
}

template <uint8_t N>
class Stride {
public:
    static constexpr size_t bits_count = N;
    static constexpr size_t external_bitmap_index_count = 1 << bits_count;
    constexpr static size_t internal_bitmap_index_count = [] {
        uint8_t ret = 0;
        for (uint8_t i = 0; i <= Stride<N - 1>::bits_count; ++i) {
            ret += 1 << i;
        }
        return ret;
    }();

    template <class T>
    /*implicit*/ constexpr Stride(Bits<T> bits) noexcept {
        debug_assert(bits.len() <= bits_count);
        inner = {static_cast<uint8_t>(bits.bits()), bits.len()};
    }

    constexpr uint8_t value() const noexcept {
        return inner.value();
    }

    constexpr uint8_t len() const noexcept {
        return inner.len();
    }

    constexpr uint8_t bits() const noexcept {
        return inner.bits();
    }

private:
    Bits<uint8_t> inner;
};

template <class T>
constexpr uint8_t popcount(T x) {
    return static_cast<uint8_t>(std::popcount(x));
}

constexpr inline uint8_t popcount(Uint128 x) {
    return static_cast<uint8_t>(
            std::popcount(static_cast<uint64_t>(x & 0xffffffffffffffffull))
            + std::popcount(static_cast<uint64_t>(x >> 64)));
}

template <uint8_t N>
using BitmapIndexType = std::conditional_t<
        N == 3,
        uint32_t,
        std::conditional_t<
                N == 4,
                uint32_t,
                std::conditional_t<
                        N == 5,
                        uint32_t,
                        std::conditional_t<N == 6,
                                           uint64_t,
                                           std::conditional_t<N == 7, Uint128, void>>>>>;

template <uint8_t N>
constexpr std::optional<uint8_t> find_longest_algo(uint8_t& values_before,
                                                   BitmapIndexType<N> inner,
                                                   Stride<N - 1> bits) noexcept {
    static_assert(N <= 7);
    constexpr auto u1 = static_cast<BitmapIndexType<N>>(1);
    switch (bits.len()) {
    case 6:
        if (auto const idx = (u1 << (63 + (bits.bits() & 0b111111))); inner & idx) {
            values_before = popcount(inner & (idx - 1));
            return 6;
        }
        [[fallthrough]];
    case 5:
        if (auto const idx = (u1 << (31 + (bits.bits() & 0b11111))); inner & idx) {
            values_before = popcount(inner & (idx - 1));
            return 5;
        }
        [[fallthrough]];
    case 4:
        if (auto const idx = (1u << (15 + (bits.bits() & 0b1111))); inner & idx) {
            values_before = popcount(inner & (idx - 1));
            return 4;
        }
        [[fallthrough]];
    case 3:
        if (auto const idx = (1u << (7 + (bits.bits() & 0b111))); inner & idx) {
            values_before = popcount(inner & (idx - 1));
            return 3;
        }
        [[fallthrough]];
    case 2:
        if (auto const idx = (1u << (3 + (bits.bits() & 0b11))); inner & idx) {
            values_before = popcount(inner & (idx - 1));
            return 2;
        }
        [[fallthrough]];
    case 1:
        if (auto const idx = (1u << (1 + (bits.bits() & 0b1))); inner & idx) {
            values_before = popcount(inner & (idx - 1));
            return 1;
        }
        [[fallthrough]];
    case 0:
        if (inner & 1) {
            values_before = 0;
            return 0;
        }
    }
    return std::nullopt;
}

template <uint8_t N>
std::optional<uint8_t> find_longest_select(uint8_t& values_before,
                                           BitmapIndexType<N> inner,
                                           Stride<N - 1> bits) noexcept {
    return find_longest_algo<N>(values_before, inner, bits);
}

template <uint8_t N>
constexpr bool exists_algo(uint8_t& values_before,
                           BitmapIndexType<N> inner,
                           Stride<N - 1> bits) noexcept {
    static_assert(N <= 7);
    constexpr auto u1 = static_cast<BitmapIndexType<N>>(1);
    switch (bits.len()) {
    case 6: {
        auto const idx = (u1 << (63 + bits.value()));
        values_before = popcount(inner & (idx - 1));
        return inner & idx;
    }
    case 5: {
        auto const idx = (u1 << (31 + bits.value()));
        values_before = popcount(inner & (idx - 1));
        return inner & idx;
    }
    case 4: {
        auto const idx = (1u << (15 + bits.value()));
        values_before = popcount(inner & (idx - 1));
        return inner & idx;
    }
    case 3: {
        auto const idx = (1u << (7 + bits.value()));
        values_before = popcount(inner & (idx - 1));
        return inner & idx;
    }
    case 2: {
        auto const idx = (1u << (3 + bits.value()));
        values_before = popcount(inner & (idx - 1));
        return inner & idx;
    }
    case 1: {
        auto const idx = (1u << (1 + bits.value()));
        values_before = popcount(inner & (idx - 1));
        return inner & idx;
    }
    case 0:
        values_before = 0;
        return inner & 1;
    }
    assert(false);
    return false;
}

template <uint8_t N>
bool exists_select(uint8_t& values_before,
                   BitmapIndexType<N> inner,
                   Stride<N - 1> bits) noexcept {
    return exists_algo<N>(values_before, inner, bits);
}

#ifdef bye_trie_LOOKUP_TABLE
template <size_t N>
inline constexpr bool exists_ht(uint8_t& values_before,
                                BitmapIndexType<N> inner,
                                Stride<N - 1> bits) noexcept {
    struct Record {
        bool exists;
        uint8_t values_before;
    };

    constexpr auto const index_count = Stride<N>::internal_bitmap_index_count;
    constexpr auto const pss = 1 << ((N - 1) + std::bit_width(N - 1));

    constexpr std::array<std::array<Record, pss>, (1 << index_count)> ht = [=] {
        std::array<std::array<Record, pss>, (1 << index_count)> ht{};
        for (auto i = 0u; i < (1 << index_count); ++i) {
            Bits<uint32_t> idx{};
            for (auto j = 0u; j < index_count; ++j, ++idx) {
                auto const z = static_cast<size_t>(idx.len()) << (N - 1) | idx.value();
                ht[i][z].exists =
                        exists_algo<N>(ht[i][z].values_before, i, Stride<N - 1>{idx});
            }
        }
        return ht;
    }();

    auto const z = static_cast<size_t>(bits.len()) << (N - 1) | bits.value();
    values_before = ht[inner][z].values_before;
    return ht[inner][z].exists;
}

template <>
inline bool exists_select<3>(uint8_t& values_before,
                             BitmapIndexType<3> inner,
                             Stride<2> bits) noexcept {
    assert([&] {
        uint8_t v1 = 0;
        uint8_t v2 = 0;
        return exists_algo<3>(v1, inner, bits) == exists_ht<3>(v2, inner, bits)
            && v1 == v2;
    }());
    return exists_ht<3>(values_before, inner, bits);
}
#endif

// 0|0000000000000000|00000000|0000|00|0
//                 16        8    4  2 1
//                          15    7  3 1
template <uint8_t N>
class InternalBitmap {
    using Int = BitmapIndexType<N>;

    static constexpr auto u1 = static_cast<Int>(1);

public:
    constexpr static uint8_t index_count = Stride<N>::internal_bitmap_index_count;

    InternalBitmap() = default;

    explicit InternalBitmap(Int inner) noexcept
            : inner{inner} {
    }

    std::optional<uint8_t> find_longest(uint8_t& values_before,
                                        Stride<N - 1> bits) const noexcept {
        return find_longest_select<N>(values_before, inner, bits);
    }

    bool exists(uint8_t& values_before, Stride<N - 1> bits) const noexcept {
        return exists_select<N>(values_before, inner, bits);
    }

    uint8_t total() const noexcept {
        return popcount(inner);
    }

    void set(Stride<N - 1> bits) {
        switch (bits.len()) {
        case 6:
            inner |= (u1 << (63 + bits.value()));
            break;
        case 5:
            inner |= (u1 << (31 + bits.value()));
            break;
        case 4:
            inner |= (1u << (15 + bits.value()));
            break;
        case 3:
            inner |= (1u << (7 + bits.value()));
            break;
        case 2:
            inner |= (1u << (3 + bits.value()));
            break;
        case 1:
            inner |= (1u << (1 + bits.value()));
            break;
        default:
            inner |= 1u;
            break;
        }
    }

    void unset(Stride<N - 1> bits) {
        switch (bits.len()) {
        case 6:
            inner &= ~(u1 << (63 + bits.value()));
            break;
        case 5:
            inner &= ~(u1 << (31 + bits.value()));
            break;
        case 4:
            inner &= ~(1u << (15 + bits.value()));
            break;
        case 3:
            inner &= ~(1u << (7 + bits.value()));
            break;
        case 2:
            inner &= ~(1u << (3 + bits.value()));
            break;
        case 1:
            inner &= ~(1u << (1 + bits.value()));
            break;
        default:
            inner &= ~1u;
            break;
        }
    }

    uint32_t get_inner() const noexcept {
        return inner;
    }

private:
    Int inner;
};

template <uint8_t N>
class ExternalBitmap {
    using Int = BitmapIndexType<N>;

    static constexpr auto u1 = static_cast<Int>(1);

public:
    ExternalBitmap() = default;

    explicit ExternalBitmap(Int inner) noexcept
            : inner{inner} {
    }

    bool exists(Stride<N> x) const noexcept {
        return (inner >> x.value()) & 1;
    }

    uint8_t before(Stride<N> x) const noexcept {
        return popcount(((u1 << x.value()) - 1) & inner);
    }

    uint8_t total() const noexcept {
        return popcount(inner);
    }

    void set(Stride<N> x) {
        inner |= u1 << x.value();
    }

    void unset(Stride<N> x) {
        inner &= ~(u1 << x.value());
    }

private:
    Int inner;
};

template <uint8_t N>
union ErasedNode;

template <uint8_t N>
struct Node {
    InternalBitmap<N> internal_bitmap;
    ExternalBitmap<N> external_bitmap;
    ErasedNode<N>* children;
};

static_assert(sizeof(Node<5>) == 16);

template <uint8_t N>
union ErasedNode {
    constexpr static size_t pointer_count = sizeof(Node<N>) / 8;
    Node<N> node;
    std::array<void*, pointer_count> pointers;
};

template <class T>
concept Trivial = std::is_trivial_v<T>;

template <Trivial T, size_t Capacity>
class StaticVec {
public:
    using Storage = std::array<T, Capacity>;

    explicit StaticVec(unsigned size)
            : size_{size} {
    }

    auto begin() const noexcept {
        return storage_.begin();
    }

    auto end() const noexcept {
        return storage_.begin() + size_;
    }

    T& operator[](size_t i) noexcept {
        assert(i < Capacity); // thanks to sentinel-1
        return storage_[i];
    }

    T operator[](size_t i) const noexcept {
        assert(i <= Capacity); // thanks to sentinel-1
        return storage_[i];
    }

    unsigned size() const noexcept {
        return size_;
    }

private:
    unsigned size_{0};
    Storage storage_;
};

template <uint8_t N>
class NodeVec {
public:
    NodeVec(ErasedNode<N>* ptr, uint8_t branches_count, uint8_t values_count) noexcept
            : branches_count{branches_count}
            , values_count{values_count}
            , inner{std::span{
                      ptr,
                      static_cast<size_t>(
                              branches_count + values_count / ErasedNode<N>::pointer_count
                              + (values_count % ErasedNode<N>::pointer_count != 0))}} {
    }

    NodeVec(NodeVec const&) = delete;
    NodeVec& operator=(NodeVec const&) = delete;

    /// \throw Forwards `Alloc::realloc` exception
    template <class Alloc>
    ErasedNode<N>* insert_branch(uint8_t i, Node<N> branch, Alloc& alloc) noexcept(
            noexcept(alloc.realloc(MemBlk{}, 0))) {
        assert(i <= branches_count);
        auto const old_size = inner.size() * sizeof(ErasedNode<N>);
        auto const new_size = old_size + sizeof(ErasedNode<N>);
        auto const blk = alloc.realloc(MemBlk{inner.data(), old_size}, new_size);
        branches_count += 1;
        inner = std::span{static_cast<ErasedNode<N>*>(blk.ptr), inner.size() + 1};
        std::rotate(inner.begin() + i, inner.end() - 1, inner.end());
        inner[i].node = branch;
        return inner.data();
    }

    /// \throw Forwards `Alloc::realloc` exception
    template <class Alloc, class T>
    ErasedNode<N>* insert_value(uint8_t i, T value, Alloc& alloc) noexcept(
            noexcept(alloc.realloc(MemBlk{}, 0))) {
        assert(i <= values_count);

        if (values_count % ErasedNode<N>::pointer_count == 0) {
            auto const old_size = inner.size() * sizeof(ErasedNode<N>);
            auto const new_size = old_size + sizeof(ErasedNode<N>);
            auto const blk = alloc.realloc(MemBlk{inner.data(), old_size}, new_size);
            inner = std::span{static_cast<ErasedNode<N>*>(blk.ptr), inner.size() + 1};
            inner.back().pointers = {};
        }

        values_count += 1;

        auto const values = inner.subspan(branches_count);
        auto const bytes = as_writable_bytes(values);

        constexpr auto value_size = sizeof(void*);
        std::rotate(bytes.begin() + i * value_size,
                    bytes.end() - 1 * value_size,
                    bytes.end());

        new (&values[i / ErasedNode<N>::pointer_count]
                      .pointers[i % ErasedNode<N>::pointer_count]) T{value};

        return inner.data();
    }

    /// \throw Forwards `Alloc::realloc` exception
    template <class Alloc>
    void erase_branch(uint8_t i,
                      Alloc& alloc) noexcept(noexcept(alloc.realloc(MemBlk{}, 0))) {
        assert(i < branches_count);
        assert(branches_count > 0);
        std::rotate(inner.begin() + i, inner.begin() + i + 1, inner.end());
        auto const old_size = inner.size() * sizeof(ErasedNode<N>);
        auto const new_size = old_size - sizeof(ErasedNode<N>);
        auto const blk = alloc.realloc(MemBlk{inner.data(), old_size}, new_size);
        inner = std::span{static_cast<ErasedNode<N>*>(blk.ptr), inner.size() - 1};
        branches_count -= 1;
    }

    /// \throw Forwards `Alloc::realloc` exception
    template <class Alloc>
    void* erase_value(uint8_t i,
                      Alloc& alloc) noexcept(noexcept(alloc.realloc(MemBlk{}, 0))) {
        assert(i < values_count);
        assert(values_count > 0);

        auto const values = inner.subspan(branches_count);
        auto const bytes = as_writable_bytes(values);

        constexpr auto value_size = sizeof(void*);
        auto const ret = values[i / ErasedNode<N>::pointer_count]
                                 .pointers[i % ErasedNode<N>::pointer_count];
        std::rotate(bytes.begin() + i * value_size,
                    bytes.begin() + (i + 1) * value_size,
                    bytes.end());

        values_count -= 1;

        if (values_count % ErasedNode<N>::pointer_count == 0) {
            auto const old_size = inner.size() * sizeof(ErasedNode<N>);
            auto const new_size = old_size - sizeof(ErasedNode<N>);
            auto const blk = alloc.realloc(MemBlk{inner.data(), old_size}, new_size);
            inner = std::span{static_cast<ErasedNode<N>*>(blk.ptr), inner.size() - 1};
        }

        return ret;
    }

    void*& value(uint8_t i) const noexcept {
        assert(i < values_count);
        return inner[branches_count + i / ErasedNode<N>::pointer_count]
                .pointers[i % ErasedNode<N>::pointer_count];
    }

    std::span<ErasedNode<N>> branches() const noexcept {
        return inner.subspan(0, branches_count);
    }

    auto values() const noexcept {
        assert(values_count <= InternalBitmap<N>::index_count);
        StaticVec<void*,
                  (InternalBitmap<N>::index_count / ErasedNode<N>::pointer_count
                   + (InternalBitmap<N>::index_count % ErasedNode<N>::pointer_count != 0))
                          * ErasedNode<N>::pointer_count /*sentinel-1*/>
                ret(values_count);
        auto const src = inner.subspan(branches_count);
        auto i = 0u;
        for (auto x : src) {
            [&]<auto... I>(std::index_sequence<I...>) {
                // sentinel-1 makes it safe the cases I != 0 safe
                ((ret[i + I] = x.pointers[I]), ...);
            }(std::make_index_sequence<ErasedNode<N>::pointer_count>{});
            i += ErasedNode<N>::pointer_count;
        }
        return ret;
    }

    ErasedNode<N>* data() const noexcept {
        return inner.data();
    }

    uint8_t size() const noexcept {
        return branches_count + values_count;
    }

    size_t size_bytes() const noexcept {
        return inner.size_bytes();
    }

    std::span<ErasedNode<N>> get_inner() const noexcept {
        return inner;
    }

private:
    uint8_t branches_count;
    uint8_t values_count;
    std::span<ErasedNode<N>> inner;
};

/// Stack of `Node`s.
/// The stack has preallocated memory to to hold `Stride::index_count` `Node`s. It can
/// recycle memory to hold more `Node`s.
///
/// \note During trie destruction this stack is used to traverse the trie
/// without allocating additional memory but rather reusing the memory being
/// freed during the destruction. One can mathematically prove that this stack
/// won't go out of memory in the algorithm.
///
/// \details The first element of contiguous array of 16 byte items
/// store meta, the rest store usable data, thus the resident array has size
/// `Stride::index_count` + 1.
template <uint8_t N>
class RecyclingStack {
public:
    void recycle(std::span<ErasedNode<N>> nodes) noexcept {
        assert(nodes.size() > 0);
        if (auto const size = static_cast<uint32_t>(nodes.size()); size == 1) {
            useless_head = new (nodes.data()) Cell{Block{1, 1, useless_head}};
        } else {
            free_head = new (nodes.data() /*start_lifetime_as_array<Cell>(nodes.data(),
                                             nodes.size())*/
                             ) Cell{Block{size, 1, free_head}};
        }
    }

    void push(Node<N> node) noexcept {
        if (used_head->block.capacity > used_head->block.size) {
            used_head[used_head->block.size++].node = node;
            return;
        }

        assert(free_head != nullptr);
        auto const block = free_head;
        free_head = free_head->block.next;
        block->block.next = used_head;
        used_head = block;

        push(node);
    }

    Node<N> pop() noexcept {
        if (used_head->block.size > 1) {
            return used_head[--used_head->block.size].node;
        }

        auto const block = used_head;
        used_head = used_head->block.next;
        block->block.next = free_head;
        free_head = block;
        assert(used_head);

        return pop();
    }

    void for_each_useless(auto f) noexcept {
        for (auto block = useless_head; block != nullptr;) {
            auto const next = block->block.next;
            f(MemBlk{block, block->block.capacity * sizeof(Node<N>)});
            block = next;
        }
    }

    void for_each_free(auto f) noexcept {
        for (auto block = free_head; block != nullptr;) {
            auto const next = block->block.next;
            f(MemBlk{block, block->block.capacity * sizeof(Node<N>)});
            block = next;
        }
    }

    bool empty() noexcept {
        return used_head->block.size == 1 && used_head->block.next == nullptr;
    }

private:
    union Cell;

    struct Block {
        uint32_t capacity;
        uint32_t size;
        Cell* next;
    };

    union Cell {
        Block block;
        Node<N> node;
    };
    static_assert(sizeof(Cell) == sizeof(Node<N>));

    std::array<Cell, Stride<N>::external_bitmap_index_count + 1 /*meta*/> resident{};
    Cell* used_head{new (resident.data()) Cell{
            .block = Block{static_cast<uint8_t>(resident.size()), 1, nullptr}}};
    Cell* useless_head{nullptr};
    Cell* free_head{nullptr};
};

template <uint8_t N, class T>
inline constexpr uint8_t leaf_pos(Bits<T> prefix) noexcept {
    return prefix.len() == 0
                 ? 0
                 : (prefix.len() - prefix.len() % detail::Stride<N>::bits_count);
}

template <class D, class S>
D* as_ptr(S& ptr) noexcept
    requires(sizeof(D) == sizeof(S))
{
    return
#if __cplusplus >= 202300L
            std::start_lifetime_as<D>(&ptr)
#elif defined(bye_trie_STRICT_ALIASING)
            new (ptr) T(std::bit_cast<D>(ptr));
#else
            reinterpret_cast<D*>(&ptr) // UB! OK if strict aliasing is off
#endif
                    ;
}

template <class D, class S>
D* as_ptr(S& ptr) noexcept
    requires(sizeof(D) != sizeof(S))
{
    return
#if __cplusplus >= 202300L
            std::start_lifetime_as<D>(&ptr)
#else
            reinterpret_cast<D*>(&ptr) // UB! OK if strict aliasing is off
#endif
                    ;
}

template <class D, class S>
D as_value(S& x) noexcept
    requires(sizeof(D) == sizeof(S))
{
    return std::bit_cast<D>(x);
}

template <class D, class S>
D as_value(S& x) noexcept
    requires(sizeof(D) < sizeof(S))
{
    return *as_ptr<D>(x);
}

} // namespace detail

template <class T>
concept TrivialLittleObject = std::is_trivial_v<T> && sizeof(T) <= 8;

struct SystemAllocator {
    MemBlk realloc(MemBlk blk, size_t size) noexcept(false) {
        if (auto const ptr = std::realloc(blk.ptr, size)) {
            return MemBlk{ptr, size};
        } else {
            throw std::bad_alloc();
        }
    }

    void dealloc(MemBlk blk) noexcept {
        std::free(blk.ptr);
    }
};

template <class T>
concept Allocator = std::is_nothrow_move_constructible_v<T>
                 && std::is_nothrow_move_assignable_v<T> && requires(T alloc) {
                        { alloc.realloc(MemBlk{}, 0) } -> std::convertible_to<MemBlk>;
                        { alloc.dealloc(MemBlk{}) };
                        noexcept(alloc.dealloc(MemBlk{}));
                    };

template <class T1, class T2>
struct Value {
    bool operator==(Value const& rhs) const noexcept = default;

    friend std::ostream& operator<<(std::ostream& os, Value const& x) {
        return os << "Value{" << x.prefix << ", " << x.value << "}";
    }

    T1 prefix;
    T2 value;
};

template <class T1, class T2>
Value(T1, T2) -> Value<T1, T2>;

template <UnsignedIntegral P, TrivialLittleObject T, uint8_t N>
class SubsIterator {
public:
    using iterator_category = std::forward_iterator_tag;
    using value_type = T;
    using difference_type = std::ptrdiff_t;
    using pointer = T*;
    using reference = T&;

    Bits<P> key() const noexcept {
        auto const slice = this->fixed_bits.concatenated(value_iter_bits);
        return this->prefix.concatenated(slice);
    }

    reference operator*() const noexcept {
        auto const slice = this->fixed_bits.concatenated(value_iter_bits);
        uint8_t vec_idx = 0;
        auto const exists = node.internal_bitmap.exists(vec_idx, slice);
        assert(exists);
        static_cast<void>(exists);
        return *detail::as_ptr<T>(detail::NodeVec{node.children,
                                                  node.external_bitmap.total(),
                                                  static_cast<uint8_t>(vec_idx + 1)}
                                          .value(vec_idx));
    }

    pointer operator->() const noexcept {
        return &**this;
    }

    /// \throw std::bad_alloc
    SubsIterator& operator++() noexcept(false) {
        ++value_iter_bits; // todo: can the skip this?
        while (true) {
            // find next prefix in current node
            {
                auto slice = fixed_bits.concatenated(value_iter_bits);
                while (slice.len() < detail::Stride<N>::bits_count) {
                    uint8_t vec_idx;
                    if (node.internal_bitmap.exists(vec_idx, slice)) {
                        return *this;
                    }
                    ++value_iter_bits;
                    slice = fixed_bits.concatenated(value_iter_bits);
                }
            }

            // go to next child
            {
                auto slice = fixed_bits.concatenated(child_iter_bits);
                while (slice.len() <= detail::Stride<N>::bits_count
                       && !node.external_bitmap.exists(slice)) {
                    ++child_iter_bits;
                    slice = fixed_bits.concatenated(child_iter_bits);
                }

                if (slice.len() <= detail::Stride<N>::bits_count) {
                    auto const branches = detail::NodeVec{node.children,
                                                          node.external_bitmap.total(),
                                                          0}
                                                  .branches();
                    path.emplace_back(node, prefix, fixed_bits, child_iter_bits);
                    prefix = prefix.concatenated(slice);
                    node = branches[node.external_bitmap.before(slice)].node;
                    fixed_bits = value_iter_bits = {};
                    child_iter_bits = Bits<P>{0, detail::Stride<N>::bits_count};
                    continue;
                }
            }

            // go back to the parent
            if (!path.empty()) {
                node = path.back().node;
                prefix = path.back().prefix;
                fixed_bits = path.back().fixed_bits;
                value_iter_bits =
                        Bits<P>(0, detail::Stride<N>::bits_count - fixed_bits.len());
                child_iter_bits = path.back().child_iter_bits;
                ++child_iter_bits;
                path.pop_back();
            } else {
                return *this;
            }
        }
    }

    bool operator==(SubsIterator const& rhs) const noexcept {
        return prefix == rhs.prefix
            && fixed_bits.concatenated(value_iter_bits)
                       == rhs.fixed_bits.concatenated(rhs.value_iter_bits)
            && child_iter_bits == rhs.child_iter_bits;
    }

private:
    template <UnsignedIntegral, TrivialLittleObject, Allocator, uint8_t, class>
    friend class ByeTrie;

    template <UnsignedIntegral, TrivialLittleObject, uint8_t>
    friend class ByeTrieSubs;

    /// \throw std::bad_alloc
    explicit SubsIterator(detail::Node<N> node, Bits<P> prefix) noexcept(false)
            : node{node} {
        std::tie(this->prefix, this->fixed_bits) =
                prefix.split_at(detail::leaf_pos<N>(prefix));
        assert(fixed_bits.len() < detail::Stride<N>::bits_count);
        this->value_iter_bits = Bits<P>(0, 0);
        this->child_iter_bits =
                Bits<P>(0, detail::Stride<N>::bits_count - this->fixed_bits.len());
        uint8_t vec_idx;
        auto const slice = fixed_bits.concatenated(value_iter_bits);
        if (!node.internal_bitmap.exists(vec_idx, slice)) {
            ++(*this);
        }
    }

    /// \throw std::bad_alloc
    SubsIterator one_past_end() const noexcept(false) {
        auto ret = *this;
        if (path.size() != 0) {
            ret.path = {};
            ret.prefix = path[0].prefix;
        }
        ret.value_iter_bits =
                Bits<P>(0, detail::Stride<N>::bits_count - fixed_bits.len());
        ret.child_iter_bits =
                Bits<P>(0, detail::Stride<N>::bits_count - fixed_bits.len() + 1);
        return ret;
    }

    struct State {
        detail::Node<N> node;
        Bits<P> prefix;
        Bits<P> fixed_bits;
        Bits<P> child_iter_bits;
    };

    detail::Node<N> node;
    Bits<P> prefix;
    Bits<P> fixed_bits;
    Bits<P> value_iter_bits;
    Bits<P> child_iter_bits;
    std::vector<State> path;
};

template <UnsignedIntegral P, TrivialLittleObject T, uint8_t N = 5>
class ByeTrieSubs {
public:
    SubsIterator<P, T, N> begin() const noexcept(false) {
        return begin_;
    }

    SubsIterator<P, T, N> const& end() const noexcept(false) {
        return end_;
    }

private:
    template <UnsignedIntegral, TrivialLittleObject, Allocator, uint8_t, class>
    friend class ByeTrie;

    explicit ByeTrieSubs(detail::Node<N> node, Bits<P> prefix) noexcept(false)
            : begin_{SubsIterator<P, T, N>{node, prefix}}
            , end_{begin_.one_past_end()} {
    }

private:
    SubsIterator<P, T, N> begin_;
    SubsIterator<P, T, N> end_;
};

template <UnsignedIntegral P, TrivialLittleObject T, uint8_t N>
class ByeTrieIterator {
public:
    using iterator_category = std::input_iterator_tag;
    using value_type = T;
    using difference_type = std::ptrdiff_t;
    using pointer = value_type*;
    using reference = value_type&;

    Bits<P> key() const noexcept {
        return prefix.concatenated(value_iter_bits);
    }

    reference operator*() const noexcept {
        uint8_t vec_idx = 0;
        auto const exists = node.internal_bitmap.exists(vec_idx, value_iter_bits);
        assert(exists);
        static_cast<void>(exists);
        return *detail::as_ptr<T>(detail::NodeVec{node.children,
                                                  node.external_bitmap.total(),
                                                  static_cast<uint8_t>(vec_idx + 1)}
                                          .value(vec_idx));
    }

    pointer operator->() const noexcept {
        return &**this;
    }

    bool next_super() noexcept {
        while (true) {
            // subs in current node
            for (auto len = static_cast<uint8_t>(value_iter_bits.len() - 1); len != 255;
                 --len) {
                static_assert(std::is_same_v<uint8_t, decltype(len)>);
                value_iter_bits = value_iter_bits.prefix(len);
                uint8_t vec_idx;
                if (node.internal_bitmap.exists(vec_idx, value_iter_bits)) {
                    return true;
                }
            }

            // go to parent node
            if (!path.empty()) {
                value_iter_bits =
                        prefix.suffix(prefix.len() - detail::Stride<N>::bits_count);
                node = path.back().node;
                prefix = path.back().prefix;
                child_iter_bits = Bits<P>{0, detail::Stride<N>::bits_count};
                path.pop_back();
            } else {
                return false;
            }
        }
    }

    /// \throw std::bad_alloc
    ByeTrieIterator& operator++() noexcept(false) {
        ++value_iter_bits;
        while (true) {
            // find next prefix in current node
            {
                while (value_iter_bits.len() < detail::Stride<N>::bits_count) {
                    uint8_t vec_idx;
                    if (node.internal_bitmap.exists(vec_idx, value_iter_bits)) {
                        return *this;
                    }
                    ++value_iter_bits;
                }
            }

            // go to next child
            {
                while (child_iter_bits.len() <= detail::Stride<N>::bits_count
                       && !node.external_bitmap.exists(child_iter_bits)) {
                    ++child_iter_bits;
                }

                if (child_iter_bits.len() <= detail::Stride<N>::bits_count) {
                    auto const branches = detail::NodeVec{node.children,
                                                          node.external_bitmap.total(),
                                                          0}
                                                  .branches();
                    path.emplace_back(node, prefix, child_iter_bits);
                    prefix = prefix.concatenated(child_iter_bits);
                    node = branches[node.external_bitmap.before(child_iter_bits)].node;
                    value_iter_bits = {};
                    child_iter_bits = Bits<P>{0, detail::Stride<N>::bits_count};
                    continue;
                }
            }

            // go back to the parent
            if (!path.empty()) {
                node = path.back().node;
                prefix = path.back().prefix;
                value_iter_bits = Bits<P>(0, detail::Stride<N>::bits_count);
                child_iter_bits = path.back().child_iter_bits;
                ++child_iter_bits;
                path.pop_back();
            } else {
                break;
            }
        }
        return *this;
    }

    bool operator==(ByeTrieIterator const& rhs) const noexcept {
        return prefix == rhs.prefix && value_iter_bits == rhs.value_iter_bits
            && child_iter_bits == rhs.child_iter_bits;
    }

private:
    template <UnsignedIntegral, TrivialLittleObject, Allocator, uint8_t, class>
    friend class ByeTrie;

    /// \throw std::bad_alloc
    explicit ByeTrieIterator(std::vector<detail::Node<N>> nodes,
                             Bits<P> prefix,
                             detail::Node<N> node,
                             Bits<P> reminder) noexcept(false)
            : node{node}
            , prefix{prefix}
            , value_iter_bits{reminder} {
        for (unsigned i = 0; i < nodes.size(); ++i) {
            path.emplace_back(nodes[i],
                              prefix.prefix(i * detail::Stride<N>::bits_count),
                              prefix.sub(i * detail::Stride<N>::bits_count,
                                         detail::Stride<N>::bits_count));
        }

        assert(value_iter_bits.len() < detail::Stride<N>::bits_count);
        this->child_iter_bits = Bits<P>{0, detail::Stride<N>::bits_count};
        uint8_t vec_idx;
        if (!node.internal_bitmap.exists(vec_idx, value_iter_bits)) {
            ++(*this);
        }
    }

    struct State {
        detail::Node<N> node;
        Bits<P> prefix;
        Bits<P> child_iter_bits;
    };

    struct one_past_end_tag {};
    explicit ByeTrieIterator(one_past_end_tag) noexcept
            : node{}
            , prefix{}
            , value_iter_bits{0, detail::Stride<N>::bits_count}
            , child_iter_bits{0, detail::Stride<N>::bits_count + 1}
            , path{} {
    }

    static ByeTrieIterator one_past_end() noexcept {
        return ByeTrieIterator(one_past_end_tag{});
    }

    detail::Node<N> node;
    Bits<P> prefix;
    Bits<P> value_iter_bits;
    Bits<P> child_iter_bits;
    std::vector<State> path;
};

/// Initial Array Optimization of size 65536.
template <uint8_t N>
class Iar16 {
public:
    static constexpr uint8_t iar_size = 16;

    detail::Node<N>& root(auto& prefix) noexcept {
        assert(prefix.len() >= iar_size);
        auto [p, s] = prefix.split_at(iar_size);
        prefix = s;
        return roots_[p.value()];
    }

    auto& roots() const noexcept {
        return roots_;
    }

private:
    std::array<detail::Node<N>, 1 << iar_size> roots_;
};

/// No initial array optimization.
template <uint8_t N>
class Iar0 {
public:
    static constexpr uint8_t iar_size = 0;

    detail::Node<N>& root(auto) noexcept {
        return root_;
    }

    detail::Node<N>& root() noexcept {
        return root_;
    }

    auto roots() const noexcept {
        return std::array<detail::Node<N>, 1>{root_};
    }

private:
    detail::Node<N> root_;
};

template <class T>
concept Config = requires(T t, Bits<uint32_t> bits) {
    requires UnsignedIntegral<typename T::Int>;
    typename std::array<char, T::stride_size>;

    requires Allocator<typename T::Allocator>;

    typename std::array<char, T::iar_size>;
    { t.root(bits) } -> std::same_as<detail::Node<T::stride_size>&>;
    { std::as_const(t).roots() } -> std::ranges::range;
    requires std::same_as<std::ranges::range_value_t<T>, detail::Node<T::stride_size>>;
};

/// Bits Trie.
/// Trie data structure with alphabet of just 0 and 1.
/// \ingroup group-datatypes
template <UnsignedIntegral P,
          TrivialLittleObject T,
          Allocator Alloc = SystemAllocator,
          uint8_t N = 5,
          class Iar = Iar0<N>>
class ByeTrie {
public:
    static_assert(N == 3 || N == 4 || N == 5 || N == 6 || N == 7, "not supported");

    using StrideType = detail::Stride<N>;

    explicit ByeTrie() noexcept(noexcept(Alloc{}))
            : alloc_{}
            , roots_{} {
    }

    explicit ByeTrie(Alloc&& alloc) noexcept
            : alloc_{std::move(alloc)}
            , roots_{} {
    }

    ByeTrie(const ByeTrie&) = delete;
    ByeTrie& operator=(const ByeTrie&) = delete;

    ByeTrie(ByeTrie&& rhs) noexcept
            : roots_{rhs.roots_}
            , size_{rhs.size_} {
        rhs.roots_ = {};
        rhs.size_ = 0;
    }

    ByeTrie& operator=(ByeTrie&& rhs) noexcept {
        this->~ByeTrie();
        new (this) ByeTrie(std::move(rhs));
        return *this;
    }

    /// Insert only if the exact prefix is not present.
    /// \post Strong exception guarantee
    /// \return Existing value
    /// \throw Forwards `Alloc::realloc` exception
    std::optional<T> insert(Bits<P> prefix,
                            T value) noexcept(noexcept(alloc_.realloc(MemBlk{}, 0))) {
        detail::Node<N>* node = &roots_.root(prefix);
        find_leaf_branch(node, prefix, noop);
        extend_leaf(node, prefix); // no-payload leaf on exception, but it's ok
        auto const res = match_exact_or_insert(node, prefix, value);
        return res.second ? std::nullopt : std::optional(detail::as_value<T>(*res.first));
    }

    /// Insert only if the exact prefix is not present.
    /// \post Strong exception guarantee
    /// \return Existing value
    /// \throw Forwards `Alloc::realloc` exception
    std::pair<T*, bool> insert_ref(Bits<P> prefix,
                                   T value) noexcept(noexcept(alloc_.realloc(MemBlk{},
                                                                             0))) {
        detail::Node<N>* node = &roots_.root(prefix);
        find_leaf_branch(node, prefix, noop);
        extend_leaf(node, prefix); // no-payload leaf on exception, but it's ok
        auto const res = match_exact_or_insert(node, prefix, value);
        return {detail::as_ptr<T>(*res.first), res.second};
    }

    /// Replace the exact prefix if present otherwise insert.
    /// \post Strong exception guarantee
    /// \return Previous value
    std::optional<T> replace(Bits<P> prefix,
                             T value) noexcept(noexcept(alloc_.realloc(MemBlk{}, 0))) {
        detail::Node<N>* node = &roots_.root(prefix);
        find_leaf_branch(node, prefix, noop);
        extend_leaf(node, prefix); // no-payload leaf on exception, but it's ok
        if (auto const res = match_exact_or_insert(node, prefix, value); !res.second) {
            using std::swap;
            auto tmp = detail::as_ptr<T>(*res.first);
            swap(*tmp, value);
            return value;
        } else {
            return std::nullopt;
        }
    }

    /// Match exact prefix.
    std::optional<T> match_exact(Bits<P> prefix) const noexcept {
        detail::Node<N>* node = &roots_.root(prefix);

        find_leaf_branch(node, prefix, noop);
        if (prefix.len() > detail::Stride<N - 1>::bits_count) {
            return std::nullopt;
        }

        uint8_t vec_idx;
        if (!node->internal_bitmap.exists(vec_idx, prefix)) {
            return std::nullopt;
        }

        return detail::as_value<T>(detail::NodeVec{node->children,
                                                   node->external_bitmap.total(),
                                                   static_cast<uint8_t>(vec_idx + 1)}
                                           .value(vec_idx));
    }

    T* match_exact_ref(Bits<P> prefix) const noexcept {
        detail::Node<N>* node = &roots_.root(prefix);

        find_leaf_branch(node, prefix, noop);
        if (prefix.len() > detail::Stride<N - 1>::bits_count) {
            return nullptr;
        }

        uint8_t vec_idx;
        if (!node->internal_bitmap.exists(vec_idx, prefix)) {
            return nullptr;
        }

        auto& val = detail::NodeVec{node->children,
                                    node->external_bitmap.total(),
                                    static_cast<uint8_t>(vec_idx + 1)}
                            .value(vec_idx);

#if __cplusplus >= 202300L
        return std::start_lifetime_as<T>(&val);
#else
        return reinterpret_cast<T*>(&val); // UB! OK if strict aliasing is off
#endif
    }

    /// Match exact prefix returning iterator.
    /// \throw std::bad_alloc
    template <class I = Iar, std::enable_if_t<std::is_same_v<I, Iar0<N>>>* = nullptr>
    ByeTrieIterator<P, T, N> match_exact_iter(Bits<P> prefix) const noexcept(false) {
        auto suffix = prefix;
        detail::Node<N>* node = &roots_.root(suffix);

        std::vector<detail::Node<N>> path;
        auto const visit = [&path](auto node, auto) { path.push_back(node); };
        find_leaf_branch(node, suffix, visit);

        if (suffix.len() > detail::Stride<N - 1>::bits_count) {
            return end();
        }

        uint8_t vec_idx;
        if (!node->internal_bitmap.exists(vec_idx, suffix)) {
            return end();
        }

        return ByeTrieIterator<P, T, N>(
                std::move(path),
                prefix.prefix(prefix.len() - suffix.len()),
                *node,
                suffix); // todo: the iterator can assume the give him an existing prefix
                         // and do the redundant check
    }

    /// Match longest prefix.
    std::optional<std::pair<uint8_t, T>> match_longest(Bits<P> prefix) const noexcept {
        detail::Node<N>* node = &roots_.root(prefix);

        std::optional<std::pair<uint8_t, T>> longest;
        uint8_t offset = Iar::iar_size;
        auto const update_longest = [&longest, &offset](auto node, auto slice) {
            uint8_t vec_idx = 0;
            if (auto const len = node.internal_bitmap.find_longest(vec_idx, slice)) {
                longest = std::pair{
                        static_cast<uint8_t>(offset + len.value()),
                        detail::as_value<T>(
                                detail::NodeVec{node.children,
                                                node.external_bitmap.total(),
                                                static_cast<uint8_t>(vec_idx + 1)}
                                        .value(vec_idx)),
                };
            }
            offset += detail::Stride<N>::bits_count;
        };

        find_leaf_branch(node, prefix, update_longest);
        if (prefix.len() < detail::Stride<N>::bits_count) {
            update_longest(*node, prefix);
        }

        return longest;
    }

    std::optional<std::pair<uint8_t, T*>> match_longest_ref(
            Bits<P> prefix) const noexcept {
        detail::Node<N>* node = &roots_.root(prefix);

        std::optional<std::pair<uint8_t, T*>> longest;
        uint8_t offset = Iar::iar_size;
        auto const update_longest = [&longest, &offset](auto node, auto slice) {
            uint8_t vec_idx = 0;
            if (auto const len = node.internal_bitmap.find_longest(vec_idx, slice)) {
                longest = std::pair{static_cast<uint8_t>(offset + len.value()),
#if __cplusplus >= 202300L
                                    std::start_lifetime_as<T>(&detail::NodeVec{
                                            node.children,
                                            node.external_bitmap.total(),
                                            static_cast<uint8_t>(vec_idx + 1)}
                                                                       .value(vec_idx))
#else
                                    reinterpret_cast<T*>(&detail::NodeVec{
                                            node.children,
                                            node.external_bitmap.total(),
                                            static_cast<uint8_t>(vec_idx + 1)}
                                                                  .value(vec_idx)) // UB! OK if strict aliasing is off
#endif
                };
            }
            offset += detail::Stride<N>::bits_count;
        };

        find_leaf_branch(node, prefix, update_longest);
        if (prefix.len() < detail::Stride<N>::bits_count) {
            update_longest(*node, prefix);
        }

        return longest;
    }

    /// Match longest prefix returning iterator.
    template <class I = Iar, std::enable_if_t<std::is_same_v<I, Iar0<N>>>* = nullptr>
    ByeTrieIterator<P, T, N> match_longest_iter(Bits<P> prefix) const noexcept(false) {
        auto suffix = prefix;
        detail::Node<N>* node = &roots_.root(suffix);

        std::optional<std::pair<detail::Node<N>, uint8_t>> longest;
        std::vector<detail::Node<N>> path;
        auto const update_longest = [&longest, &path](auto node, auto slice) {
            uint8_t vec_idx = 0;
            if (auto const len = node.internal_bitmap.find_longest(vec_idx, slice)) {
                longest = std::pair{
                        node, detail::Stride<N>::bits_count * path.size() + len.value()};
            }
            path.push_back(node);
        };

        find_leaf_branch(node, suffix, update_longest);
        if (suffix.len() < detail::Stride<N>::bits_count) {
            update_longest(*node, suffix);
        }

        if (!longest.has_value()) {
            return end();
        }

        path.erase(path.begin() + longest->second / detail::Stride<N>::bits_count,
                   path.end());

        return ByeTrieIterator<P, T, N>(
                path,
                prefix.prefix(path.size() * detail::Stride<N>::bits_count),
                longest->first,
                prefix.sub(path.size() * detail::Stride<N>::bits_count,
                           longest->second
                                   - path.size() * detail::Stride<N>::bits_count));
    }

    /// Erase exact prefix.
    /// \throw Forwards `Alloc::realloc` exception
    std::optional<T> erase_exact(Bits<P> prefix) noexcept(
            noexcept(alloc_.realloc(MemBlk{}, 0))) {
        detail::Node<N>* node = &roots_.root(prefix);
        auto reminder = prefix;

        find_leaf_branch(node, reminder, noop);
        if (reminder.len() > detail::Stride<N - 1>::bits_count) {
            return std::nullopt;
        }

        uint8_t vec_idx;
        if (!node->internal_bitmap.exists(vec_idx, reminder)) {
            return std::nullopt;
        }

        detail::NodeVec vec{node->children,
                            node->external_bitmap.total(),
                            node->internal_bitmap.total()};

        auto const ret = detail::as_value<T>(vec.value(vec_idx));

        if (vec.size() < 2) [[unlikely]] {
            erase_cleaning(prefix);
            return ret;
        }

        vec.erase_value(vec_idx, alloc_);
        node->children = vec.data();
        node->internal_bitmap.unset(reminder);
        size_ -= 1;
        return ret;
    }

    size_t size() const noexcept {
        return size_;
    }

    ~ByeTrie() noexcept {
        for (auto root : roots_.roots()) {
            detail::RecyclingStack<N> stack;
            stack.push(root);
            while (!stack.empty()) { // DFS traversal
                auto const node = stack.pop();
                detail::NodeVec vec{node.children,
                                    node.external_bitmap.total(),
                                    node.internal_bitmap.total()};
                for (auto child : vec.branches()) {
                    stack.push(child.node);
                }
                if (vec.size()) {
                    stack.recycle(vec.get_inner());
                }
            }
            stack.for_each_useless([this](auto blk) { alloc_.dealloc(blk); });
            stack.for_each_free([this](auto blk) { alloc_.dealloc(blk); });
        }
    }

    Alloc& alloc() noexcept {
        return alloc_;
    }

    /// View to sub networks of `prefix`
    /// \throw std::bad_alloc
    ByeTrieSubs<P, T, N> subs(Bits<P> prefix) const noexcept(false) {
        auto suffix = prefix;
        detail::Node<N>* node = &roots_.root(suffix);

        find_leaf_branch(node, suffix, noop);
        if (suffix.len() > detail::Stride<N - 1>::bits_count) {
            return ByeTrieSubs<P, T, N>{{}, prefix};
        }

        return ByeTrieSubs<P, T, N>{*node, prefix};
    }

    /// Visit super networks of `prefix` with `on_super(Bits, T&)`
    /// \throw forwards `on_super` exception
    template <class F>
    void visit_supers(Bits<P> prefix, F const& on_super) const
            noexcept(noexcept(on_super(std::declval<Bits<P>>(), std::declval<T&>()))) {
        auto suffix = prefix;
        detail::Node<N>* node = &roots_.root(suffix);

        uint8_t offset = Iar::iar_size;
        auto const visit = [&offset, prefix, &on_super](auto node, auto reminder) {
            for (auto len = 0u; len <= reminder.len(); ++len) {
                uint8_t vec_idx = 0;
                if (node.internal_bitmap.exists(vec_idx, reminder.prefix(len))) {
                    on_super(prefix.sub(0, offset + len),
                             *detail::as_ptr<T>(
                                     detail::NodeVec{node.children,
                                                     node.external_bitmap.total(),
                                                     static_cast<uint8_t>(vec_idx + 1)}
                                             .value(vec_idx)));
                }
            }
            offset += detail::Stride<N>::bits_count;
        };

        find_leaf_branch(node, suffix, visit);

        if (suffix.len() < detail::Stride<N>::bits_count) {
            visit(*node, suffix);
        }
    }

    // \throw std::bad_alloc
    template <class I = Iar, std::enable_if_t<std::is_same_v<I, Iar0<N>>>* = nullptr>
    ByeTrieIterator<P, T, N> begin() const noexcept(false) {
        return ByeTrieIterator<P, T, N>({}, {}, roots_.root(), {});
    }

    // \throw std::bad_alloc
    template <class I = Iar, std::enable_if_t<std::is_same_v<I, Iar0<N>>>* = nullptr>
    ByeTrieIterator<P, T, N> end() const noexcept(false) {
        return ByeTrieIterator<P, T, N>::one_past_end();
    }

private:
    static constexpr auto noop = [](auto...) {};

    static void find_leaf_branch(detail::Node<N>*& node,
                                 Bits<P>& prefix,
                                 auto on_node) noexcept {
        while (prefix.len() >= detail::Stride<N>::bits_count) {
            on_node(*node, prefix.prefix(detail::Stride<N - 1>::bits_count));
            auto const slice = prefix.prefix(detail::Stride<N>::bits_count);
            if (node->external_bitmap.exists(slice)) {
                auto const vec_idx = node->external_bitmap.before(slice);
                node = &node->children[vec_idx].node;
            } else {
                break;
            }
            prefix = prefix.suffix(detail::Stride<N>::bits_count);
        }
    }

    /// \post Strong exception guarantee
    /// \throw Forwards `Alloc::realloc` exception
    void extend_leaf(detail::Node<N>*& node,
                     Bits<P>& prefix) noexcept(noexcept(alloc_.realloc(MemBlk{}, 0))) {
        while (prefix.len() >= detail::Stride<N>::bits_count) {
            auto const slice = prefix.prefix(detail::Stride<N>::bits_count);
            auto const vec_idx = node->external_bitmap.before(slice);

            node->children = detail::NodeVec{node->children,
                                             node->external_bitmap.total(),
                                             node->internal_bitmap.total()}
                                     .insert_branch(vec_idx, detail::Node<N>{}, alloc_);
            node->external_bitmap.set(slice);

            node = &node->children[vec_idx].node;
            prefix = prefix.suffix(detail::Stride<N>::bits_count);
        }
    }

    /// \post Strong exception guarantee
    /// \throw Forwards `Alloc::realloc` exception
    std::pair<void**, bool> match_exact_or_insert(
            detail::Node<N>*& node,
            Bits<P> prefix,
            T value) noexcept(noexcept(alloc_.realloc(MemBlk{}, 0))) {
        detail::NodeVec vec{
                node->children,
                node->external_bitmap.total(),
                node->internal_bitmap.total(),
        };

        uint8_t vec_idx = 0;
        if (node->internal_bitmap.exists(vec_idx, prefix)) {
            return {&vec.value(vec_idx), false};
        }

        node->children = std::move(vec).insert_value(vec_idx, value, alloc_);
        node->internal_bitmap.set(prefix);

        size_ += 1;

        return {&vec.value(vec_idx), true};
    }

    /// \pre Exists
    /// \throw Forwards `Alloc::realloc` exception
    void erase_cleaning(Bits<P> prefix) noexcept(noexcept(alloc_.realloc(MemBlk{}, 0))) {
        assert(match_exact(prefix).has_value());

        std::array<detail::Node<N>*,
                   sizeof(P) * CHAR_BIT / detail::Stride<N>::bits_count
                           + (sizeof(P) * CHAR_BIT % detail::Stride<N>::bits_count > 0)>
                stack;

        detail::Node<N>* node = &roots_.root(prefix);
        auto reminder = prefix;

        size_t level = 0;
        find_leaf_branch(node, reminder, [&level, &stack](auto& node, auto) {
            stack[level++] = &node;
        });

        detail::NodeVec const vec{node->children,
                                  node->external_bitmap.total(),
                                  node->internal_bitmap.total()};
        alloc_.dealloc(MemBlk{vec.data(), vec.size_bytes()});
        node->children = nullptr;
        node->internal_bitmap = {};
        size_ -= 1;

        reminder = prefix;
        while (level--) {
            auto& node = *stack[level];
            auto const slice = reminder.sub(level * detail::Stride<N>::bits_count,
                                            detail::Stride<N>::bits_count);
            detail::NodeVec vec{node.children,
                                node.external_bitmap.total(),
                                node.internal_bitmap.total()};

            if (vec.size() < 2) {
                alloc_.dealloc(MemBlk{vec.data(), vec.size_bytes()});
                node.children = nullptr;
                node.external_bitmap = {};
            } else {
                vec.erase_branch(node.external_bitmap.before(slice), alloc_);
                node.children = vec.data();
                node.external_bitmap.unset(slice);
                break;
            }
        }
    }

private:
    Alloc alloc_;
    Iar mutable roots_;
    size_t size_{0};
};

} // namespace bye_trie
