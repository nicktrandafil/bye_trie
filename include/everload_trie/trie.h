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
#include <span>
#include <type_traits>
#include <vector>

static_assert(sizeof(void*) == 8, "64-bit only");

/// \todo The result of an arithmetic on two `uint8_t` is an `int`. This
/// implies some explicit casts back to `uint8_t` in the code, which makes
/// the code more verbose. Should I just use `unsigned` instead?

namespace everload_trie {
namespace detail {

/// Piece of prefix used to index branches of a node
inline constexpr uint8_t stride = 5; // bits

/// Piece of prefix used to index values of a node
/// It is one shorter than `stride` because `stride`-length values are
/// stored as 0-length prefixes in one node down.
inline constexpr uint8_t stride_m_1 = 4; // bits

constexpr inline uint8_t take_slice(uint8_t value, uint8_t start, uint8_t len) noexcept {
    assert(start < 8);
    assert(start + len <= 8);
    return (len == 8) ? (value >> start) : ((value >> start) & ((uint8_t(1) << len) - 1));
}

constexpr inline uint32_t take_slice(uint32_t value,
                                     uint8_t start,
                                     uint8_t len) noexcept {
    assert(start < 32);
    assert(start + len <= 32);
    return (len == 32) ? (value >> start)
                       : ((value >> start) & ((uint32_t(1) << len) - 1));
}

constexpr inline uint64_t take_slice(uint64_t value,
                                     uint8_t start,
                                     uint8_t len) noexcept {
    assert(start < 64);
    assert(start + len <= 64);
    return (len == 64) ? (value >> start)
                       : ((value >> start) & ((uint64_t(1) << len) - 1));
}

template <class T>
class Bits {
public:
    Bits()
            : bits_{}
            , len_{} {
    }

    constexpr Bits(T bits, uint8_t len) noexcept
            : bits_(bits)
            , len_(len) {
        assert(len <= sizeof(T) * CHAR_BIT);
    }

    uint8_t len() const noexcept {
        return len_;
    }

    T bits() const noexcept {
        return bits_;
    }

    T value() const noexcept {
        return take_slice(bits_, 0, len_);
    }

    Bits sub(uint8_t offset) const noexcept {
        return Bits{take_slice(bits_, offset, len_ - offset),
                    static_cast<uint8_t>(len_ - offset)};
    }

    Bits sub(uint8_t offset, uint8_t len) const noexcept {
        assert(offset + len <= len_);
        return Bits{take_slice(bits_, offset, len), len};
    }

    Bits concatenated(Bits slice) const noexcept {
        assert(len_ != sizeof(T) * CHAR_BIT);
        assert(static_cast<uint8_t>(len_ + slice.len()) <= sizeof(T) * CHAR_BIT);
        return Bits{bits_ | (slice.value() << len_),
                    static_cast<uint8_t>(len_ + slice.len())};
    }

    bool operator==(Bits const& rhs) const noexcept {
        return len_ == rhs.len_ && value() == rhs.value();
    }

    Bits& operator++() noexcept {
        if (value() == static_cast<T>(((1 << len_) - 1))) {
            bits_ = 0;
            ++len_;
        } else {
            ++bits_;
        }
        return *this;
    }

    std::pair<Bits, Bits> split_at(uint8_t offset) const noexcept {
        return {sub(0, offset), sub(offset)};
    }

private:
    T bits_;
    uint8_t len_;
};

class StrideM1 {
public:
    template <class T>
    /*implicit*/ StrideM1(Bits<T> bits) noexcept {
        assert(bits.len() <= stride_m_1);
        inner = {static_cast<uint8_t>(bits.bits()), bits.len()};
    }

    uint8_t value() const noexcept {
        return inner.value();
    }

    uint8_t len() const noexcept {
        return inner.len();
    }

    uint8_t bits() const noexcept {
        return inner.bits();
    }

private:
    Bits<uint8_t> inner;
};

class Stride {
public:
    template <class T>
    /*implicit*/ Stride(Bits<T> bits) noexcept {
        assert(bits.len() <= stride);
        inner = {static_cast<uint8_t>(bits.bits()), bits.len()};
    }

    uint8_t value() const noexcept {
        return inner.value();
    }

private:
    Bits<uint8_t> inner;
};

// 0|0000000000000000|00000000|0000|00|0
//                 16        8    4  2 1
//                          15    7  3 1
class InternalBitMap {
public:
    InternalBitMap() = default;

    explicit InternalBitMap(uint32_t inner) noexcept
            : inner{inner} {
    }

    std::optional<uint8_t> find_longest(uint8_t& values_before,
                                        StrideM1 bits) const noexcept {
        switch (bits.len()) {
        case 4:
            if (auto const idx = (1u << (15 + (bits.bits() & 0b1111))); inner & idx) {
                values_before = static_cast<uint8_t>(std::popcount(inner & (idx - 1)));
                return 4;
            }
            [[fallthrough]];
        case 3:
            if (auto const idx = (1u << (7 + (bits.bits() & 0b111))); inner & idx) {
                values_before = static_cast<uint8_t>(std::popcount(inner & (idx - 1)));
                return 3;
            }
            [[fallthrough]];
        case 2:
            if (auto const idx = (1u << (3 + (bits.bits() & 0b11))); inner & idx) {
                values_before = static_cast<uint8_t>(std::popcount(inner & (idx - 1)));
                return 2;
            }
            [[fallthrough]];
        case 1:
            if (auto const idx = (1u << (1 + (bits.bits() & 0b1))); inner & idx) {
                values_before = static_cast<uint8_t>(std::popcount(inner & (idx - 1)));
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

    bool exists(uint8_t& values_before, StrideM1 bits) const noexcept {
        switch (bits.len()) {
        [[likely]] case 4: {
            auto const idx = (1u << (15 + bits.value()));
            values_before = static_cast<uint8_t>(std::popcount(inner & (idx - 1)));
            return inner & idx;
        }
        case 3: {
            auto const idx = (1u << (7 + bits.value()));
            values_before = static_cast<uint8_t>(std::popcount(inner & (idx - 1)));
            return inner & idx;
        }
        case 2: {
            auto const idx = (1u << (3 + bits.value()));
            values_before = static_cast<uint8_t>(std::popcount(inner & (idx - 1)));
            return inner & idx;
        }
        case 1: {
            auto const idx = (1u << (1 + bits.value()));
            values_before = static_cast<uint8_t>(std::popcount(inner & (idx - 1)));
            return inner & idx;
        }
        default:
            values_before = 0;
            return inner & 1;
        }
    }

    uint8_t total() const noexcept {
        return static_cast<uint8_t>(std::popcount(inner));
    }

    void set(StrideM1 bits) {
        switch (bits.len()) {
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

    void unset(StrideM1 bits) {
        switch (bits.len()) {
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
    uint32_t inner;
};

class ExternalBitMap {
public:
    ExternalBitMap() = default;

    explicit ExternalBitMap(uint32_t inner) noexcept
            : inner{inner} {
    }

    bool exists(Stride x) const noexcept {
        return (inner >> x.value()) & 1;
    }

    uint8_t before(Stride x) const noexcept {
        return static_cast<uint8_t>(std::popcount(((1u << x.value()) - 1) & inner));
    }

    uint8_t total() const noexcept {
        return static_cast<uint8_t>(std::popcount(inner));
    }

    void set(Stride x) {
        inner |= 1u << x.value();
    }

    void unset(Stride x) {
        inner &= ~(1u << x.value());
    }

private:
    uint32_t inner;
};

union ErasedNode;

struct Node {
    InternalBitMap internal_bitmap;
    ExternalBitMap external_bitmap;
    ErasedNode* children;
};

static_assert(sizeof(Node) == 16);

struct TwoPointers {
    void*& operator[](size_t i) & noexcept {
        return inner[i];
    }

    std::array<void*, 2> inner;
};

union ErasedNode {
    Node node;
    TwoPointers pointers;
};

template <class T>
concept Trivial = std::is_trivial_v<T>;

template <Trivial T, size_t Capacity = 31>
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
        return storage_[i];
    }

    T operator[](size_t i) const noexcept {
        return storage_[i];
    }

    unsigned size() const noexcept {
        return size_;
    }

private:
    unsigned size_{0};
    Storage storage_;
};

class NodeVec {
public:
    NodeVec(ErasedNode* ptr, uint8_t branches_count, uint8_t values_count) noexcept
            : branches_count{branches_count}
            , values_count{values_count}
            , inner{std::span{ptr,
                              static_cast<size_t>(branches_count + values_count / 2
                                                  + values_count % 2)}} {
    }

    NodeVec(NodeVec const&) = delete;
    NodeVec& operator=(NodeVec const&) = delete;

    /// \throw Forwards `Alloc::realloc` exception
    template <class Alloc>
    ErasedNode* insert_branch(uint8_t i, Node branch, Alloc& alloc) noexcept(
            noexcept(alloc.realloc(nullptr, 0))) {
        assert(i <= branches_count);
        auto const new_size = (inner.size() + 1) * sizeof(ErasedNode);
        auto const ptr = alloc.realloc(inner.data(), new_size);
        branches_count += 1;
        inner = std::span{static_cast<ErasedNode*>(ptr), inner.size() + 1};
        std::rotate(inner.begin() + i, inner.end() - 1, inner.end());
        inner[i].node = branch;
        return inner.data();
    }

    /// \throw Forwards `Alloc::realloc` exception
    template <class Alloc>
    ErasedNode* insert_value(uint8_t i,
                             void* value,
                             Alloc& alloc) noexcept(noexcept(alloc.realloc(nullptr, 0))) {
        assert(i <= values_count);

        if (values_count % 2 == 0) {
            auto const new_size = (inner.size() + 1) * sizeof(ErasedNode);
            auto const ptr = alloc.realloc(inner.data(), new_size);
            inner = std::span{static_cast<ErasedNode*>(ptr), inner.size() + 1};
            inner.back().pointers = {};
        }

        values_count += 1;

        auto const values = inner.subspan(branches_count);
        auto const bytes = as_writable_bytes(values);

        constexpr auto value_size = sizeof(void*);
        std::rotate(bytes.begin() + i * value_size,
                    bytes.end() - 1 * value_size,
                    bytes.end());

        values[i / 2].pointers[i % 2] = value;

        return inner.data();
    }

    void erase_branch(uint8_t i) noexcept {
        assert(i < branches_count);
        assert(branches_count > 0);
        std::rotate(inner.begin() + i, inner.begin() + i + 1, inner.end());
        auto const new_size = (inner.size() - 1) * sizeof(ErasedNode);
        auto const ptr = std::realloc(inner.data(), new_size);
        assert(ptr != nullptr);
        inner = std::span{static_cast<ErasedNode*>(ptr), inner.size() - 1};
        branches_count -= 1;
    }

    void* erase_value(uint8_t i) noexcept {
        assert(i < values_count);
        assert(values_count > 0);

        auto const values = inner.subspan(branches_count);
        auto const bytes = as_writable_bytes(values);

        constexpr auto value_size = sizeof(void*);
        auto const ret = values[i / 2].pointers[i % 2];
        std::rotate(bytes.begin() + i * value_size,
                    bytes.begin() + (i + 1) * value_size,
                    bytes.end());

        values_count -= 1;

        if (values_count % 2 == 0) {
            auto const new_size = (inner.size() - 1) * sizeof(ErasedNode);
            auto const ptr = std::realloc(inner.data(), new_size);
            assert(ptr != nullptr);
            inner = std::span{static_cast<ErasedNode*>(ptr), inner.size() - 1};
        }

        return ret;
    }

    void*& value(uint8_t i) const noexcept {
        assert(i < values_count);
        return inner[branches_count + i / 2].pointers[i % 2];
    }

    std::span<ErasedNode> branches() const noexcept {
        return inner.subspan(0, branches_count);
    }

    StaticVec<void*> values() const noexcept {
        StaticVec<void*> ret(values_count);
        auto const src = inner.subspan(branches_count);
        auto i = 0u;
        for (auto x : src) {
            ret[i * 2] = x.pointers[0];
            ret[i * 2 + 1] = x.pointers[1];
            i += 1;
        }
        return ret;
    }

    ErasedNode* data() noexcept {
        return inner.data();
    }

    uint8_t size() const noexcept {
        return branches_count + values_count;
    }

    std::span<ErasedNode> get_inner() const noexcept {
        return inner;
    }

private:
    uint8_t branches_count;
    uint8_t values_count;
    std::span<ErasedNode> inner;
};

/// Stack of `Node`s
///
/// The stack has preallocated memory to to hold 32 `Node`s. It can recycle
/// memory to hold more `Node`s.
///
/// \note During trie destruction this stack is used to traverse the trie
/// without allocating additional memory but rather reusing the memory being
/// freed during the destruction. One can mathematically prove that this stack
/// won't go out of memory in the algorithm.
class RecyclingStack {
public:
    void recycle(std::span<ErasedNode> nodes) noexcept {
        assert(nodes.size() > 0);
        if (auto const size = static_cast<uint32_t>(nodes.size()); size == 1) {
            useless_head = new (nodes.data()) Cell{Block{1, 1, useless_head}};
        } else {
            free_head = new (nodes.data() /*start_lifetime_as_array<Cell>(nodes.data(),
                                             nodes.size())*/
                             ) Cell{Block{size, 1, free_head}};
        }
    }

    void push(Node node) noexcept {
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

    Node pop() noexcept {
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
            f(static_cast<void*>(block));
            block = next;
        }
    }

    void for_each_free(auto f) noexcept {
        for (auto block = free_head; block != nullptr;) {
            auto const next = block->block.next;
            f(static_cast<void*>(block));
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
    static_assert(sizeof(Block) == 16);

    union Cell {
        Block block;
        Node node;
    };
    static_assert(sizeof(Cell) == 16);

    std::array<Cell, 33> resident{};
    Cell* used_head{new (resident.data()) Cell{.block = Block{33, 1, nullptr}}};
    Cell* useless_head{nullptr};
    Cell* free_head{nullptr};
};

template <class T>
inline constexpr uint8_t leaf_pos(Bits<T> prefix) noexcept {
    return prefix.len() - prefix.len() % detail::stride;
}

} // namespace detail

template <class T>
concept UnsignedIntegral = std::unsigned_integral<T>
                        || (sizeof(T) <= 16 && std::is_trivial_v<T> && requires(T val) {
                               { val << 1 };
                               { val >> 1 };
                               { val& val };
                               { val - val };
                               { val == val };
                               { static_cast<uint64_t>(val) };
                           });

template <class T>
concept TrivialLittleObject = std::is_trivial_v<T> && sizeof(T) == 8;

struct SystemAllocator {
    void* realloc(void* ptr, size_t size) noexcept(false) {
        if (auto const ret = std::realloc(ptr, size)) {
            return ret;
        } else {
            throw std::bad_alloc();
        }
    }

    void dealloc(void* ptr) noexcept {
        std::free(ptr);
    }
};

template <class T>
concept Allocator = std::is_nothrow_move_constructible_v<T>
                 && std::is_nothrow_move_assignable_v<T> && requires(T alloc) {
                        { alloc.realloc(nullptr, 0) };
                        { alloc.dealloc(nullptr) };
                        noexcept(alloc.dealloc(nullptr));
                    };

template <UnsignedIntegral P, TrivialLittleObject T>
class Iterator {
public:
    using iterator_category = std::input_iterator_tag;
    using value_type = struct value_type {
        bool operator==(value_type const& rhs) const noexcept = default;

        P bits;
        uint8_t len;
        T value;
    };
    using difference_type = std::ptrdiff_t;
    using pointer = value_type const*;
    using reference = value_type;

    reference operator*() const noexcept {
        auto const slice = this->fixed.concatenated(reminder);
        auto const prefix = this->prefix.concatenated(slice);
        uint8_t idx;
        auto const exists = node.internal_bitmap.exists(idx, slice);
        assert(exists);
        static_cast<void>(exists);
        return {prefix.bits(),
                prefix.len(),
                std::bit_cast<T>(detail::NodeVec{node.children,
                                                 node.external_bitmap.total(),
                                                 static_cast<uint8_t>(idx + 1)}
                                         .values()[idx])};
    }

    Iterator& operator++() noexcept(false) {
        ++reminder;
        do {
            // find next prefix in current node
            {
                auto slice = fixed.concatenated(reminder);
                while (slice.len() < detail::stride) {
                    uint8_t vec_idx;
                    if (node.internal_bitmap.exists(vec_idx, slice)) {
                        return *this;
                    }
                    ++reminder;
                    slice = fixed.concatenated(reminder);
                }
            }

            // add branches of current node to the queue
            {
                auto reminder = detail::Bits<P>{
                        0, static_cast<uint8_t>(detail::stride - fixed.len())};
                auto slice = fixed.concatenated(reminder);
                auto const branches =
                        detail::NodeVec{node.children, node.external_bitmap.total(), 0}
                                .branches();
                states.reserve(states.size() + branches.size());
                while (slice.len() <= detail::stride) {
                    if (node.external_bitmap.exists(slice)) {
                        states.push_back(
                                State{branches[node.external_bitmap.before(slice)].node,
                                      prefix.concatenated(slice)});
                    }
                    ++reminder;
                    slice = fixed.concatenated(reminder);
                }
            }

            // pop next node from the queue
            if (!states.empty()) {
                node = states.front().node;
                prefix = states.front().prefix;
                states.erase(states.begin());
                fixed = reminder = {};
            } else {
                node = {};
                prefix = fixed = reminder = {};
                break;
            }
        } while (true);

        return *this;
    }

    bool operator==(Iterator const& rhs) const noexcept {
        return prefix == rhs.prefix
            && fixed.concatenated(reminder) == rhs.fixed.concatenated(rhs.reminder);
    }

private:
    template <UnsignedIntegral, TrivialLittleObject, Allocator Alloc>
    friend class Trie;

    explicit Iterator(detail::Node node, detail::Bits<P> prefix) noexcept(false)
            : node{node} {
        std::tie(this->prefix, this->fixed) = prefix.split_at(detail::leaf_pos(prefix));
        assert(fixed.len() < detail::stride);
        this->reminder = detail::Bits<P>(0, 0);
        uint8_t vec_idx;
        auto const slice = fixed.concatenated(reminder);
        if (!node.internal_bitmap.exists(vec_idx, slice)) {
            ++(*this);
        }
    }

    //                     0|0000000000000000|00000000|0000|00|0
    // slice len                            4        3    2  1 0
    // bitmap len or count                 16        8    4  2 1
    // accumulated count                   31       15    7  3 1
    struct State {
        detail::Node node;
        detail::Bits<P> prefix;
    };

    detail::Node node;
    detail::Bits<P> prefix;
    detail::Bits<P> fixed;
    detail::Bits<P> reminder;
    std::vector<State> states;
};

template <UnsignedIntegral P, TrivialLittleObject T, Allocator Alloc = SystemAllocator>
class Trie {
public:
    using ValueType = typename Iterator<P, T>::value_type;

    explicit Trie() noexcept(noexcept(Alloc{}))
            : alloc_{}
            , root_{detail::InternalBitMap{0}, detail::ExternalBitMap{0}, nullptr} {
    }

    explicit Trie(Alloc&& alloc) noexcept
            : alloc_{std::move(alloc)}
            , root_{detail::InternalBitMap{0}, detail::ExternalBitMap{0}, nullptr} {
    }

    Trie(const Trie&) = delete;
    Trie& operator=(const Trie&) = delete;

    Trie(Trie&& rhs) noexcept
            : root_{rhs.root_}
            , size_{rhs.size_} {
        rhs.root_ = detail::Node{};
        rhs.size_ = 0;
    }

    Trie& operator=(Trie&& rhs) noexcept {
        root_ = rhs.root_;
        size_ = rhs.size_;
        rhs.root_ = detail::Node{};
        rhs.size_ = 0;
        return *this;
    }

    /// Insert only if the exact prefix is not present
    /// \pre `len <= sizeof(P) * CHAR_BITS`
    /// \post Strong exception guarantee
    /// \return Existing value
    /// \throw Forwards `Alloc::realloc` exception
    std::optional<T> insert(P bits,
                            uint8_t len,
                            T value) noexcept(noexcept(alloc_.realloc(nullptr, 0))) {
        detail::Node* node = &root_;
        detail::Bits<P> prefix{bits, len};
        find_leaf_branch(node, prefix, noop);
        extend_leaf(node, prefix); // no-payload leaf on exception, but it's ok
        auto const prev = match_exact_or_insert(node, prefix, value);
        return prev ? std::optional(std::bit_cast<T>(*prev)) : std::nullopt;
    }

    /// Replace or insert if the exact prefix is not present
    /// \pre `len <= sizeof(P) * CHAR_BITS`
    /// \post Strong exception guarantee
    /// \return Previous value
    /// \throw Forwards `Alloc::realloc` exception
    std::optional<T> replace(P bits,
                             uint8_t len,
                             T value) noexcept(noexcept(alloc_.realloc(nullptr, 0))) {
        detail::Node* node = &root_;
        detail::Bits<P> prefix{bits, len};
        find_leaf_branch(node, prefix, noop);
        extend_leaf(node, prefix); // no-payload leaf on exception, but it's ok
        if (auto const old_value = match_exact_or_insert(node, prefix, value)) {
            using std::swap;
            auto new_value = std::bit_cast<void*>(value);
            swap(*old_value, new_value);
            return std::bit_cast<T>(new_value);
        } else {
            return std::nullopt;
        }
    }

    /// Match exact prefix
    /// \pre `len <= sizeof(P) * CHAR_BIT`
    std::optional<T> match_exact(P bits, uint8_t len) noexcept {
        assert(len <= sizeof(P) * CHAR_BIT);

        detail::Node* node = &root_;
        detail::Bits<P> prefix{bits, len};

        find_leaf_branch(node, prefix, noop);
        if (prefix.len() > detail::stride_m_1) {
            return std::nullopt;
        }

        uint8_t vec_idx;
        if (!node->internal_bitmap.exists(vec_idx, prefix)) {
            return std::nullopt;
        }

        return std::bit_cast<T>(detail::NodeVec{node->children,
                                                node->external_bitmap.total(),
                                                static_cast<uint8_t>(vec_idx + 1)}
                                        .value(vec_idx));
    }

    /// Counterpart of `match_exact` which returns an iterator
    /// \pre `len <= sizeof(P) * CHAR_BIT`
    /// \throw std::bad_alloc
    Iterator<P, T> find_exact(P bits, uint8_t len) noexcept(false) {
        assert(len <= sizeof(P) * CHAR_BIT);

        detail::Node* node = &root_;
        detail::Bits<P> prefix{bits, len};

        find_leaf_branch(node, prefix, noop);
        if (prefix.len() > detail::stride_m_1) {
            return end();
        }

        uint8_t vec_idx;
        if (!node->internal_bitmap.exists(vec_idx, prefix)) {
            return end();
        }

        return Iterator<P, T>{*node, detail::Bits<P>{bits, len}};
    }

    /// Match longest prefix
    /// \pre `len <= sizeof(P) * CHAR_BIT`
    std::optional<std::pair<uint8_t, T>> match_longest(P bits, uint8_t len) noexcept {
        assert(len <= sizeof(P) * CHAR_BIT);
        detail::Node* node = &root_;
        detail::Bits<P> prefix{bits, len};

        std::optional<std::pair<uint8_t, T>> longest;
        uint8_t offset = 0;
        auto const update_longest = [&longest, &offset](auto node, auto slice) {
            uint8_t vec_idx;
            if (auto const len = node.internal_bitmap.find_longest(vec_idx, slice)) {
                longest = std::pair{
                        static_cast<uint8_t>(offset + len.value()),
                        std::bit_cast<T>(
                                detail::NodeVec{node.children,
                                                node.external_bitmap.total(),
                                                static_cast<uint8_t>(vec_idx + 1)}
                                        .value(vec_idx)),
                };
            }
            offset += detail::stride;
        };

        find_leaf_branch(node, prefix, update_longest);
        if (prefix.len() < detail::stride) {
            update_longest(*node, prefix);
        }

        return longest;
    }

    /// Counterpart of `match_longest` which returns an iterator
    /// \pre `len <= sizeof(P) * CHAR_BIT`
    /// \throw std::bad_alloc
    Iterator<P, T> find_longest(P bits, uint8_t len) noexcept(false) {
        assert(len <= sizeof(P) * CHAR_BIT);
        detail::Node* node = &root_;
        detail::Bits<P> prefix{bits, len};

        std::optional<std::pair<uint8_t, detail::Node>> longest;
        uint8_t offset = 0;
        auto const update_longest = [&longest, &offset](auto node, auto slice) {
            uint8_t vec_idx;
            if (auto const len = node.internal_bitmap.find_longest(vec_idx, slice)) {
                longest = std::pair{static_cast<uint8_t>(offset + len.value()), node};
            }
            offset += detail::stride;
        };

        find_leaf_branch(node, prefix, update_longest);
        if (prefix.len() < detail::stride) {
            update_longest(*node, prefix);
        }

        if (longest) {
            return Iterator<P, T>{longest->second, detail::Bits<P>{bits, longest->first}};
        } else {
            return end();
        }
    }

    /// Erase exact prefix
    /// \pre `len <= sizeof(P) * CHAR_BIT`
    bool erase_exact(P bits, uint8_t len) noexcept {
        detail::Node* node = &root_;
        detail::Bits<P> prefix{bits, len};

        find_leaf_branch(node, prefix, noop);
        if (prefix.len() > detail::stride_m_1) {
            return false;
        }

        uint8_t vec_idx;
        if (!node->internal_bitmap.exists(vec_idx, prefix)) {
            return false;
        }

        detail::NodeVec vec{node->children,
                            node->external_bitmap.total(),
                            node->internal_bitmap.total()};

        if (vec.size() < 2) [[unlikely]] {
            erase_cleaning(bits, len);
            return true;
        }

        vec.erase_value(vec_idx);
        node->children = vec.data();
        node->internal_bitmap.unset(prefix);
        size_ -= 1;
        return true;
    }

    size_t size() const noexcept {
        return size_;
    }

    ~Trie() noexcept {
        detail::RecyclingStack stack;
        stack.push(root_);
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
        stack.for_each_useless([this](auto ptr) { alloc_.dealloc(ptr); });
        stack.for_each_free([this](auto ptr) { alloc_.dealloc(ptr); });
    }

    Alloc& alloc() noexcept {
        return alloc_;
    }

    Iterator<P, T> begin() const noexcept(false) {
        return Iterator<P, T>{root_, detail::Bits<P>{0, 0}};
    }

    Iterator<P, T> end() const noexcept(false) {
        return Iterator<P, T>{{}, {}};
    }

private:
    static constexpr auto noop = [](auto...) {};

    static void find_leaf_branch(detail::Node*& node,
                                 detail::Bits<P>& prefix,
                                 auto on_node) noexcept {
        while (prefix.len() >= detail::stride) {
            on_node(*node, prefix.sub(0, detail::stride_m_1));
            auto const slice = prefix.sub(0, detail::stride);
            if (node->external_bitmap.exists(slice)) {
                auto const vec_idx = node->external_bitmap.before(slice);
                node = &node->children[vec_idx].node;
            } else {
                break;
            }
            prefix = prefix.sub(detail::stride);
        }
    }

    /// \post Strong exception guarantee
    /// \throw Forwards `Alloc::realloc` exception
    void extend_leaf(detail::Node*& node,
                     detail::Bits<P>& prefix) noexcept(noexcept(alloc_.realloc(nullptr,
                                                                               0))) {
        while (prefix.len() >= detail::stride) {
            auto const slice = prefix.sub(0, detail::stride);
            auto const vec_idx = node->external_bitmap.before(slice);

            node->children = detail::NodeVec{node->children,
                                             node->external_bitmap.total(),
                                             node->internal_bitmap.total()}
                                     .insert_branch(vec_idx, detail::Node{}, alloc_);
            node->external_bitmap.set(slice);

            node = &node->children[vec_idx].node;
            prefix = prefix.sub(detail::stride);
        }
    }

    /// \post Strong exception guarantee
    /// \throw Forwards `Alloc::realloc` exception
    void** match_exact_or_insert(detail::Node*& node,
                                 detail::Bits<P> slice,
                                 T value) noexcept(noexcept(alloc_.realloc(nullptr, 0))) {
        detail::NodeVec vec{
                node->children,
                node->external_bitmap.total(),
                node->internal_bitmap.total(),
        };

        uint8_t vec_idx;
        if (node->internal_bitmap.exists(vec_idx, slice)) {
            return &vec.value(vec_idx);
        }

        node->children =
                std::move(vec).insert_value(vec_idx, std::bit_cast<void*>(value), alloc_);
        node->internal_bitmap.set(slice);

        size_ += 1;
        return nullptr;
    }

    /// \pre Exists
    void erase_cleaning(P bits, uint8_t len) noexcept {
        assert(match_exact(bits, len).has_value());

        std::array<detail::Node*,
                   sizeof(P) * CHAR_BIT / detail::stride
                           + (sizeof(P) * CHAR_BIT % detail::stride > 0)>
                stack;

        detail::Node* node = &root_;
        detail::Bits<P> prefix{bits, len};

        size_t level = 0;
        find_leaf_branch(node, prefix, [&level, &stack](auto& node, auto) {
            stack[level++] = &node;
        });

        alloc_.dealloc(node->children);
        node->children = nullptr;
        node->internal_bitmap = {};
        size_ -= 1;

        prefix = detail::Bits<P>{bits, len};
        while (level--) {
            auto& node = *stack[level];
            auto const slice = prefix.sub(level * detail::stride, detail::stride);
            detail::NodeVec vec{node.children,
                                node.external_bitmap.total(),
                                node.internal_bitmap.total()};

            if (vec.size() < 2) {
                alloc_.dealloc(stack[level]->children);
                node.children = nullptr;
                node.external_bitmap = {};
            } else {
                // todo there was index confusion, add a test
                vec.erase_branch(node.external_bitmap.before(slice));
                node.children = vec.data();
                node.external_bitmap.unset(slice);
                break;
            }
        }
    }

private:
    Alloc alloc_;
    detail::Node root_;
    size_t size_{0};
};

} // namespace everload_trie
