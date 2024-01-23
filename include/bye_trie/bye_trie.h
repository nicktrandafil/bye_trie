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

    /// \post UB when `len() >= sizeof(T) * CHAR_BIT`
    Bits& operator++() noexcept {
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
        return {sub(0, offset), sub(offset)};
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

namespace detail {

/// Slice of prefix used to index branches of a node.
inline constexpr uint8_t stride = 5; // bits

/// Slice of prefix used to index values of a node.
/// It is one shorter than `stride` because `stride`-length prefixes are
/// stored as 0-length prefixes in one node down.
inline constexpr uint8_t stride_m_1 = 4; // bits

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
class InternalBitmap {
public:
    InternalBitmap() = default;

    explicit InternalBitmap(uint32_t inner) noexcept
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
        case 0:
            values_before = 0;
            return inner & 1;
        }
        assert(false);
        return false;
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

class ExternalBitmap {
public:
    ExternalBitmap() = default;

    explicit ExternalBitmap(uint32_t inner) noexcept
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
    InternalBitmap internal_bitmap;
    ExternalBitmap external_bitmap;
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

template <Trivial T, size_t Capacity = 31 + 1 /*sentinel*/>
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
        assert(i <= size_); // `=` thanks to sentinel
        return storage_[i];
    }

    T operator[](size_t i) const noexcept {
        assert(i <= size_); // `=` thanks to sentinel
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
            noexcept(alloc.realloc(MemBlk{}, 0))) {
        assert(i <= branches_count);
        auto const old_size = inner.size() * sizeof(ErasedNode);
        auto const new_size = old_size + sizeof(ErasedNode);
        auto const blk = alloc.realloc(MemBlk{inner.data(), old_size}, new_size);
        branches_count += 1;
        inner = std::span{static_cast<ErasedNode*>(blk.ptr), inner.size() + 1};
        std::rotate(inner.begin() + i, inner.end() - 1, inner.end());
        inner[i].node = branch;
        return inner.data();
    }

    /// \throw Forwards `Alloc::realloc` exception
    template <class Alloc>
    ErasedNode* insert_value(uint8_t i, void* value, Alloc& alloc) noexcept(
            noexcept(alloc.realloc(MemBlk{}, 0))) {
        assert(i <= values_count);

        if (values_count % 2 == 0) {
            auto const old_size = inner.size() * sizeof(ErasedNode);
            auto const new_size = old_size + sizeof(ErasedNode);
            auto const blk = alloc.realloc(MemBlk{inner.data(), old_size}, new_size);
            inner = std::span{static_cast<ErasedNode*>(blk.ptr), inner.size() + 1};
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

    /// \throw Forwards `Alloc::realloc` exception
    template <class Alloc>
    void erase_branch(uint8_t i,
                      Alloc& alloc) noexcept(noexcept(alloc.realloc(MemBlk{}, 0))) {
        assert(i < branches_count);
        assert(branches_count > 0);
        std::rotate(inner.begin() + i, inner.begin() + i + 1, inner.end());
        auto const old_size = inner.size() * sizeof(ErasedNode);
        auto const new_size = old_size - sizeof(ErasedNode);
        auto const blk = alloc.realloc(MemBlk{inner.data(), old_size}, new_size);
        inner = std::span{static_cast<ErasedNode*>(blk.ptr), inner.size() - 1};
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
        auto const ret = values[i / 2].pointers[i % 2];
        std::rotate(bytes.begin() + i * value_size,
                    bytes.begin() + (i + 1) * value_size,
                    bytes.end());

        values_count -= 1;

        if (values_count % 2 == 0) {
            auto const old_size = inner.size() * sizeof(ErasedNode);
            auto const new_size = old_size - sizeof(ErasedNode);
            auto const blk = alloc.realloc(MemBlk{inner.data(), old_size}, new_size);
            inner = std::span{static_cast<ErasedNode*>(blk.ptr), inner.size() - 1};
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
        assert(values_count <= 31);
        StaticVec<void*> ret(values_count);
        auto const src = inner.subspan(branches_count);
        auto i = 0u;
        for (auto x : src) {
            ret[i * 2] = x.pointers[0];
            ret[i * 2 + 1] = x.pointers[1]; // sentinel makes it safe
            i += 1;
        }
        return ret;
    }

    ErasedNode* data() const noexcept {
        return inner.data();
    }

    uint8_t size() const noexcept {
        return branches_count + values_count;
    }

    size_t size_bytes() const noexcept {
        return inner.size_bytes();
    }

    std::span<ErasedNode> get_inner() const noexcept {
        return inner;
    }

private:
    uint8_t branches_count;
    uint8_t values_count;
    std::span<ErasedNode> inner;
};

/// Stack of `Node`s.
/// The stack has preallocated memory to to hold 32 `Node`s. It can recycle
/// memory to hold more `Node`s.
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
            f(MemBlk{block, block->block.capacity * sizeof(Node)});
            block = next;
        }
    }

    void for_each_free(auto f) noexcept {
        for (auto block = free_head; block != nullptr;) {
            auto const next = block->block.next;
            f(MemBlk{block, block->block.capacity * sizeof(Node)});
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
concept TrivialLittleObject = std::is_trivial_v<T> && sizeof(T) == 8;

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

template <UnsignedIntegral P, TrivialLittleObject T>
class SubsIterator {
public:
    using iterator_category = std::input_iterator_tag;
    using value_type = struct value_type {
        bool operator==(value_type const& rhs) const noexcept = default;

        friend std::ostream& operator<<(std::ostream& os, value_type const& x) {
            return os << "Value{" << x.prefix << ", " << x.value << "}";
        }

        Bits<P> prefix;
        T value;
    };
    using difference_type = std::ptrdiff_t;
    using pointer = value_type const*;
    using reference = value_type;

    reference operator*() const noexcept {
        auto const slice = this->fixed_bits.concatenated(value_iter_bits);
        auto const prefix = this->prefix.concatenated(slice);
        uint8_t vec_idx = 0;
        auto const exists = node.internal_bitmap.exists(vec_idx, slice);
        assert(exists);
        static_cast<void>(exists);
        return {prefix,
                std::bit_cast<T>(detail::NodeVec{node.children,
                                                 node.external_bitmap.total(),
                                                 static_cast<uint8_t>(vec_idx + 1)}
                                         .values()[vec_idx])};
    }

    SubsIterator& operator++() noexcept(false) {
        ++value_iter_bits;
        while (true) {
            // find next prefix in current node
            {
                auto slice = fixed_bits.concatenated(value_iter_bits);
                while (slice.len() < detail::stride) {
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
                while (slice.len() <= detail::stride
                       && !node.external_bitmap.exists(slice)) {
                    ++child_iter_bits;
                    slice = fixed_bits.concatenated(child_iter_bits);
                }

                if (slice.len() <= detail::stride) {
                    auto const branches = detail::NodeVec{node.children,
                                                          node.external_bitmap.total(),
                                                          0}
                                                  .branches();
                    path.emplace_back(node, prefix, fixed_bits, child_iter_bits);
                    prefix = prefix.concatenated(slice);
                    node = branches[node.external_bitmap.before(slice)].node;
                    fixed_bits = value_iter_bits = {};
                    child_iter_bits = Bits<P>{0, detail::stride};
                    continue;
                }
            }

            // go back to the parent
            if (!path.empty()) {
                node = path.back().node;
                prefix = path.back().prefix;
                fixed_bits = path.back().fixed_bits;
                value_iter_bits = Bits<P>(0, detail::stride - fixed_bits.len());
                child_iter_bits = path.back().child_iter_bits;
                ++child_iter_bits;
                path.pop_back();
            } else {
                node = {};
                prefix = fixed_bits = value_iter_bits = child_iter_bits = {};
                break;
            }
        }
        return *this;
    }

    bool operator==(SubsIterator const& rhs) const noexcept {
        return prefix == rhs.prefix
            && fixed_bits.concatenated(value_iter_bits)
                       == rhs.fixed_bits.concatenated(rhs.value_iter_bits);
    }

private:
    template <UnsignedIntegral, TrivialLittleObject, Allocator, class>
    friend class ByeTrie;

    template <UnsignedIntegral, TrivialLittleObject>
    friend class ByeTrieSubs;

    explicit SubsIterator(detail::Node node, Bits<P> prefix) noexcept(false)
            : node{node} {
        std::tie(this->prefix, this->fixed_bits) =
                prefix.split_at(detail::leaf_pos(prefix));
        assert(fixed_bits.len() < detail::stride);
        this->value_iter_bits = Bits<P>(0, 0);
        this->child_iter_bits = Bits<P>(0, detail::stride - this->fixed_bits.len());
        uint8_t vec_idx;
        auto const slice = fixed_bits.concatenated(value_iter_bits);
        if (!node.internal_bitmap.exists(vec_idx, slice)) {
            ++(*this);
        }
    }

    struct State {
        detail::Node node;
        Bits<P> prefix;
        Bits<P> fixed_bits;
        Bits<P> child_iter_bits;
    };

    detail::Node node;
    Bits<P> prefix;
    Bits<P> fixed_bits;
    Bits<P> value_iter_bits;
    Bits<P> child_iter_bits;
    std::vector<State> path;
};

template <UnsignedIntegral P, TrivialLittleObject T>
class ByeTrieSubs {
public:
    using ValueType = typename SubsIterator<P, T>::value_type;

    SubsIterator<P, T> begin() const noexcept(false) {
        return begin_;
    }

    SubsIterator<P, T> end() const noexcept(false) {
        return SubsIterator<P, T>{{}, {}};
    }

private:
    template <UnsignedIntegral, TrivialLittleObject, Allocator, class>
    friend class ByeTrie;

    explicit ByeTrieSubs(detail::Node node, Bits<P> prefix) noexcept(false)
            : begin_{SubsIterator<P, T>{node, prefix}} {
    }

private:
    SubsIterator<P, T> begin_;
};

/// Initial Array Optimization of size 65536.
class Iar16 {
public:
    static constexpr uint8_t len = 16;

    detail::Node& root(auto& prefix) noexcept {
        assert(prefix.len() >= len);
        auto [p, s] = prefix.split_at(len);
        prefix = s;
        return roots_[p.value()];
    }

    auto& roots() const noexcept {
        return roots_;
    }

private:
    std::array<detail::Node, 1 << len> roots_;
};

/// No initial array optimization.
class Iar0 {
public:
    static constexpr uint8_t len = 0;

    detail::Node& root(auto) noexcept {
        return root_;
    }

    auto roots() const noexcept {
        return std::array<detail::Node, 1>{root_};
    }

private:
    detail::Node root_;
};

/// Bits Trie.
/// Trie data structure with alphabet of just 0 and 1.
/// \ingroup group-datatypes
template <UnsignedIntegral P,
          TrivialLittleObject T,
          Allocator Alloc = SystemAllocator,
          class Iar = Iar0>
class ByeTrie {
public:
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
        detail::Node* node = &roots_.root(prefix);
        find_leaf_branch(node, prefix, noop);
        extend_leaf(node, prefix); // no-payload leaf on exception, but it's ok
        auto const prev = match_exact_or_insert(node, prefix, value);
        return prev ? std::optional(std::bit_cast<T>(*prev)) : std::nullopt;
    }

    /// Replace the exact prefix if present otherwise insert.
    /// \post Strong exception guarantee
    /// \return Previous value
    /// \throw Forwards `Alloc::realloc` exception
    std::optional<T> replace(Bits<P> prefix,
                             T value) noexcept(noexcept(alloc_.realloc(MemBlk{}, 0))) {
        detail::Node* node = &roots_.root(prefix);
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

    /// Match exact prefix.
    std::optional<T> match_exact(Bits<P> prefix) const noexcept {
        detail::Node* node = &roots_.root(prefix);

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

    /// Match longest prefix.
    std::optional<std::pair<uint8_t, T>> match_longest(Bits<P> prefix) const noexcept {
        detail::Node* node = &roots_.root(prefix);

        std::optional<std::pair<uint8_t, T>> longest;
        uint8_t offset = Iar::len;
        auto const update_longest = [&longest, &offset](auto node, auto slice) {
            uint8_t vec_idx = 0;
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

    /// Erase exact prefix.
    /// \throw Forwards `Alloc::realloc` exception
    bool erase_exact(Bits<P> prefix) noexcept(noexcept(alloc_.realloc(MemBlk{}, 0))) {
        detail::Node* node = &roots_.root(prefix);
        auto reminder = prefix;

        find_leaf_branch(node, reminder, noop);
        if (reminder.len() > detail::stride_m_1) {
            return false;
        }

        uint8_t vec_idx;
        if (!node->internal_bitmap.exists(vec_idx, reminder)) {
            return false;
        }

        detail::NodeVec vec{node->children,
                            node->external_bitmap.total(),
                            node->internal_bitmap.total()};

        if (vec.size() < 2) [[unlikely]] {
            erase_cleaning(prefix);
            return true;
        }

        vec.erase_value(vec_idx, alloc_);
        node->children = vec.data();
        node->internal_bitmap.unset(reminder);
        size_ -= 1;
        return true;
    }

    size_t size() const noexcept {
        return size_;
    }

    ~ByeTrie() noexcept {
        for (auto root : roots_.roots()) {
            detail::RecyclingStack stack;
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
    ByeTrieSubs<P, T> subs(Bits<P> prefix) const noexcept(false) {
        auto suffix = prefix;
        detail::Node* node = &roots_.root(suffix);

        find_leaf_branch(node, suffix, noop);
        if (suffix.len() > detail::stride_m_1) {
            return ByeTrieSubs<P, T>{{}, prefix};
        }

        return ByeTrieSubs<P, T>{*node, prefix};
    }

private:
    static constexpr auto noop = [](auto...) {};

    static void find_leaf_branch(detail::Node*& node,
                                 Bits<P>& prefix,
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
                     Bits<P>& prefix) noexcept(noexcept(alloc_.realloc(MemBlk{}, 0))) {
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
    void** match_exact_or_insert(detail::Node*& node, Bits<P> prefix, T value) noexcept(
            noexcept(alloc_.realloc(MemBlk{}, 0))) {
        detail::NodeVec vec{
                node->children,
                node->external_bitmap.total(),
                node->internal_bitmap.total(),
        };

        uint8_t vec_idx = 0;
        if (node->internal_bitmap.exists(vec_idx, prefix)) {
            return &vec.value(vec_idx);
        }

        node->children =
                std::move(vec).insert_value(vec_idx, std::bit_cast<void*>(value), alloc_);
        node->internal_bitmap.set(prefix);

        size_ += 1;
        return nullptr;
    }

    /// \pre Exists
    /// \throw Forwards `Alloc::realloc` exception
    void erase_cleaning(Bits<P> prefix) noexcept(noexcept(alloc_.realloc(MemBlk{}, 0))) {
        assert(match_exact(prefix).has_value());

        std::array<detail::Node*,
                   sizeof(P) * CHAR_BIT / detail::stride
                           + (sizeof(P) * CHAR_BIT % detail::stride > 0)>
                stack;

        detail::Node* node = &roots_.root(prefix);
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
            auto const slice = reminder.sub(level * detail::stride, detail::stride);
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
