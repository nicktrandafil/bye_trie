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
#include <optional>
#include <span>
#include <vector>

static_assert(sizeof(void*) == 8, "64-bit only");

namespace everload_trie {
namespace detail {

inline constexpr uint8_t stride = 5;     // bits
inline constexpr uint8_t stride_m_1 = 4; // bits

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
                                        uint8_t i,
                                        uint8_t len) const noexcept {
        assert(i < 32);
        assert(len < stride);
        switch (len) {
        case 4:
            if (auto const idx = (1u << (15 + (i & 0b1111))); inner & idx) {
                values_before = static_cast<uint8_t>(std::popcount(inner & (idx - 1)));
                return 4;
            }
            [[fallthrough]];
        case 3:
            if (auto const idx = (1u << (7 + (i & 0b111))); inner & idx) {
                values_before = static_cast<uint8_t>(std::popcount(inner & (idx - 1)));
                return 3;
            }
            [[fallthrough]];
        case 2:
            if (auto const idx = (1u << (3 + (i & 0b11))); inner & idx) {
                values_before = static_cast<uint8_t>(std::popcount(inner & (idx - 1)));
                return 2;
            }
            [[fallthrough]];
        case 1:
            if (auto const idx = (1u << (1 + (i & 0b1))); inner & idx) {
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

    bool exists(uint8_t& values_before, uint8_t i, uint8_t len) const noexcept {
        assert(i < 32);
        assert(len < stride);
        switch (len) {
        [[likely]] case 4 : {
            auto const idx = (1u << (15 + i));
            values_before = static_cast<uint8_t>(std::popcount(inner & (idx - 1)));
            return inner & idx;
        }
        case 3: {
            auto const idx = (1u << (7 + i));
            values_before = static_cast<uint8_t>(std::popcount(inner & (idx - 1)));
            return inner & idx;
        }
        case 2: {
            auto const idx = (1u << (3 + i));
            values_before = static_cast<uint8_t>(std::popcount(inner & (idx - 1)));
            return inner & idx;
        }
        case 1: {
            auto const idx = (1u << (1 + i));
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

    void set(uint8_t i, uint8_t len) {
        assert(i < 32);
        assert(len < stride);
        switch (len) {
        case 4:
            inner |= (1u << (15 + i));
            break;
        case 3:
            inner |= (1u << (7 + i));
            break;
        case 2:
            inner |= (1u << (3 + i));
            break;
        case 1:
            inner |= (1u << (1 + i));
            break;
        default:
            inner |= 1u;
            break;
        }
    }

    void unset(uint8_t i, uint8_t len) {
        assert(i < 32);
        assert(len < stride);
        switch (len) {
        case 4:
            inner &= ~(1u << (15 + i));
            break;
        case 3:
            inner &= ~(1u << (7 + i));
            break;
        case 2:
            inner &= ~(1u << (3 + i));
            break;
        case 1:
            inner &= ~(1u << (1 + i));
            break;
        default:
            inner &= ~1u;
            break;
        }
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

    bool exists(uint8_t i) const noexcept {
        assert(i < 32);
        return (inner >> i) & 1;
    }

    uint8_t before(uint8_t i) const noexcept {
        assert(i < 32);
        return static_cast<uint8_t>(std::popcount(((1u << i) - 1) & inner));
    }

    uint8_t total() const noexcept {
        return static_cast<uint8_t>(std::popcount(inner));
    }

    void set(uint8_t i) {
        assert(i < 32);
        inner |= 1u << i;
    }

    void unset(uint8_t i) {
        assert(i < 32);
        inner &= ~(1u << i);
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

constexpr inline uint8_t take_slice(uint32_t value, uint8_t start, uint8_t len) noexcept {
    assert(start <= 32);
    assert(len < 32);
    static_assert(stride < 32);
    return (start == 32)
                 ? 0
                 : static_cast<uint8_t>((value >> start) & ((uint32_t(1) << len) - 1));
}

constexpr inline uint8_t take_slice(uint64_t value, uint8_t start, uint8_t len) noexcept {
    assert(start <= 64);
    assert(len < 64);
    static_assert(stride < 64);
    return (start == 64)
                 ? 0
                 : static_cast<uint8_t>((value >> start) & ((uint64_t(1) << len) - 1));
}

template <class T>
class BitsSlice {
public:
    constexpr BitsSlice(T bits, uint8_t start, uint8_t len) noexcept
            : bits_(bits)
            , start_(start)
            , len_(len) {
    }

    uint8_t offset() const noexcept {
        return start_;
    }

    uint8_t len() const noexcept {
        return len_;
    }

    uint8_t value() const noexcept {
        return take_slice(bits_, start_, len_);
    }

    BitsSlice sub(size_t start) const noexcept {
        assert(start <= len_);
        BitsSlice ret{*this};
        ret.start_ += start;
        ret.len_ -= start;
        return ret;
    }

    BitsSlice sub(unsigned start, unsigned len) const noexcept {
        assert(len <= len_);
        assert(start <= len_);
        BitsSlice ret{*this};
        ret.start_ += start;
        ret.len_ = len;
        return ret;
    }

private:
    T bits_;
    uint8_t start_;
    uint8_t len_;
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

    /// \throw std::bad_alloc
    ErasedNode* insert_branch(uint8_t i, Node branch) noexcept(false) {
        assert(i <= branches_count);
        auto const new_size = (inner.size() + 1) * sizeof(ErasedNode);
        auto const ptr = std::realloc(inner.data(), new_size);
        if (ptr == nullptr) {
            throw std::bad_alloc{};
        }

        branches_count += 1;
        inner = std::span{static_cast<ErasedNode*>(ptr), inner.size() + 1};

        std::rotate(inner.begin() + i, inner.end() - 1, inner.end());

        inner[i].node = branch;

        return inner.data();
    }

    /// \throw std::bad_alloc
    ErasedNode* insert_value(uint8_t i, void* value) noexcept(false) {
        assert(i <= values_count);

        if (values_count % 2 == 0) {
            auto const new_size = (inner.size() + 1) * sizeof(ErasedNode);
            auto const ptr = std::realloc(inner.data(), new_size);
            if (ptr == nullptr) {
                throw std::bad_alloc{};
            }

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

private:
    uint8_t branches_count;
    uint8_t values_count;
    std::span<ErasedNode> inner;
};

class RecyclingStack {
public:
    void recycle(std::span<ErasedNode> nodes) noexcept {
        assert(nodes.size() > 0);
        free_head = new (nodes.data()) FreeBlock{nodes.size(), free_head};
    }

    void push(Node node) noexcept {
    }

private:
    struct FreeBlock {
        size_t size;
        FreeBlock* next;
    };
    static_assert(sizeof(FreeBlock) == 16);

    struct UsedBlock;

    union Cell {
        UsedBlock* next;
        Node* node;
    };

    struct UsedBlock {
        uint32_t capacity;
        uint32_t size;
        Cell* cell;
    };
    static_assert(sizeof(UsedBlock) == 16);

    std::array<Cell, 33> resident;
    UsedBlock used_head{*new (resident.data()) UsedBlock{33, 0, resident.data()}};
    FreeBlock* free_head{nullptr};
};

} // namespace detail

template <class T>
concept UnsignedIntegral =
        std::unsigned_integral<T> || (std::is_trivial_v<T> && requires(T val) {
            { val << 1 };
            { val >> 1 };
            { val& val };
            { val - val };
            { val == val };
            { static_cast<uint64_t>(val) };
        });

template <class T>
concept TrivialLittleObject = std::is_trivial_v<T> && sizeof(T) == 8;

template <TrivialLittleObject T>
class Trie {
public:
    Trie() noexcept
            : root_{detail::InternalBitMap{0}, detail::ExternalBitMap{0}, nullptr} {
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
    /// \return Existing value
    /// \throw std::bad_alloc
    /// \post Strong exception guarantee
    std::optional<T> insert(uint32_t bits, uint8_t len, T value) noexcept(false) {
        detail::Node* node = &root_;
        detail::BitsSlice<uint32_t> prefix{bits, 0, len};
        find_leaf_branch(node, prefix, noop);
        extend_leaf(node, prefix);
        auto const prev = match_exact_or_insert(node, prefix, value);
        return prev ? std::optional(std::bit_cast<T>(*prev)) : std::nullopt;
    }

    /// Replace or insert if the exact prefix is not present
    /// \return Previous value
    /// \throw std::bad_alloc
    /// \post Strong exception guarantee
    std::optional<T> replace(uint32_t bits, uint8_t len, T value) noexcept(false) {
        detail::Node* node = &root_;
        detail::BitsSlice<uint32_t> prefix{bits, 0, len};
        find_leaf_branch(node, prefix, noop);
        extend_leaf(node, prefix);
        if (auto const old_value = match_exact_or_insert(node, prefix, value)) {
            using std::swap;
            auto new_value = std::bit_cast<void*>(value);
            swap(*old_value, new_value);
            return std::bit_cast<T>(new_value);
        } else {
            return std::nullopt;
        }
    }

    std::optional<T> match_exact(uint32_t bits, uint8_t len) noexcept {
        detail::Node* node = &root_;
        detail::BitsSlice<uint32_t> prefix{bits, 0, len};

        find_leaf_branch(node, prefix, noop);
        if (prefix.len() > detail::stride_m_1) {
            return std::nullopt;
        }

        auto const idx = prefix.value();
        uint8_t vec_idx;
        if (!node->internal_bitmap.exists(vec_idx, idx, prefix.len())) {
            return std::nullopt;
        }

        return std::bit_cast<T>(detail::NodeVec{node->children,
                                                node->external_bitmap.total(),
                                                static_cast<uint8_t>(vec_idx + 1)}
                                        .value(vec_idx));
    }

    std::optional<std::pair<uint8_t, T>> match_longest(uint32_t bits,
                                                       uint8_t len) noexcept {
        detail::Node* node = &root_;
        detail::BitsSlice<uint32_t> prefix{bits, 0, len};
        std::optional<std::pair<uint8_t, T>> longest;
        find_leaf_branch(node, prefix, [&longest](auto node, auto prefix) {
            auto const slice = prefix.sub(0, std::min(detail::stride_m_1, prefix.len()));
            auto const idx = slice.value();
            uint8_t vec_idx;
            if (auto const len =
                        node.internal_bitmap.find_longest(vec_idx, idx, slice.len())) {
                longest = std::pair{
                        static_cast<uint8_t>(slice.offset() + *len),
                        std::bit_cast<T>(
                                detail::NodeVec{node.children,
                                                node.external_bitmap.total(),
                                                static_cast<uint8_t>(vec_idx + 1)}
                                        .value(vec_idx)),
                };
            }
        });
        return longest;
    }

    bool erase_exact(uint32_t bits, uint8_t len) noexcept {
        detail::Node* node = &root_;
        detail::BitsSlice<uint32_t> prefix{bits, 0, len};

        find_leaf_branch(node, prefix, noop);
        if (prefix.len() > detail::stride_m_1) {
            return false;
        }

        auto const idx = prefix.value();
        uint8_t vec_idx;
        if (!node->internal_bitmap.exists(vec_idx, idx, prefix.len())) {
            return false;
        }

        detail::NodeVec vec{node->children,
                            node->external_bitmap.total(),
                            node->internal_bitmap.total()};

        if (vec.size() < 2) [[unlikely]] {
            erase_cleaning(bits, len);
            return true;
        }

        vec.erase_value(idx);
        node->children = vec.data();
        node->internal_bitmap.unset(vec_idx, prefix.len());
        size_ -= 1;
        return true;
    }

    size_t size() const noexcept {
        return size_;
    }

    /// \throw std::bad_alloc
    ~Trie() {
        std::vector<detail::Node> stack{{root_}};
        while (stack.size()) { // dfs traversal
            auto const node = stack.back();
            stack.pop_back();

            auto const branches_count = node.external_bitmap.total();
            auto const m = stack.size();
            stack.resize(m + branches_count);
            std::transform(node.children,
                           node.children + branches_count,
                           stack.begin() + m,
                           [](auto x) { return x.node; });

            std::free(node.children);
        }
    }

private:
    static constexpr auto noop = [](auto...) {};

    static void find_leaf_branch(detail::Node*& node,
                                 detail::BitsSlice<uint32_t>& prefix,
                                 auto on_node) noexcept {
        while (prefix.len() >= detail::stride) {
            on_node(*node, prefix);
            auto const idx = prefix.sub(0, detail::stride).value();
            if (node->external_bitmap.exists(idx)) {
                auto const vec_idx = node->external_bitmap.before(idx);
                node = &node->children[vec_idx].node;
            } else {
                break;
            }
            prefix = prefix.sub(detail::stride);
        }
        on_node(*node, prefix);
    }

    /// \throw std::bad_alloc
    /// \post Strong exception guarantee
    static void extend_leaf(detail::Node*& node,
                            detail::BitsSlice<uint32_t>& prefix) noexcept(false) {
        while (prefix.len() >= detail::stride) {
            auto const idx = prefix.sub(0, detail::stride).value();
            auto const vec_idx = node->external_bitmap.before(idx);

            node->children = detail::NodeVec{node->children,
                                             node->external_bitmap.total(),
                                             node->internal_bitmap.total()}
                                     .insert_branch(vec_idx, detail::Node{});
            node->external_bitmap.set(idx);

            node = &node->children[vec_idx].node;
            prefix = prefix.sub(detail::stride);
        }
    }

    /// \throw std::bad_alloc
    /// \post Strong exception guarantee
    void** match_exact_or_insert(detail::Node*& node,
                                 detail::BitsSlice<uint32_t> slice,
                                 T value) noexcept(false) {
        detail::NodeVec vec{
                node->children,
                node->external_bitmap.total(),
                node->internal_bitmap.total(),
        };

        auto const idx = slice.value();
        uint8_t vec_idx;
        if (node->internal_bitmap.exists(vec_idx, idx, slice.len())) {
            return &vec.value(vec_idx);
        }

        node->children =
                std::move(vec).insert_value(vec_idx, std::bit_cast<void*>(value));
        node->internal_bitmap.set(idx, slice.len());

        size_ += 1;
        return nullptr;
    }

    /// \pre Exists
    void erase_cleaning(uint32_t bits, uint8_t len) noexcept {
        std::array<detail::Node*,
                   sizeof(uint32_t) * 8
                           / (detail::stride + sizeof(uint32_t) * 8 % detail::stride > 0)>
                stack;

        detail::Node* node = &root_;
        detail::BitsSlice<uint32_t> prefix{bits, 0, len};

        size_t level = 0;
        find_leaf_branch(node, prefix, [&level, &stack](auto& node, auto) {
            stack[level++] = &node;
        });

        detail::NodeVec const vec{node->children, 0, 1};
        std::free(node->children);
        node->children = nullptr;
        node->internal_bitmap = {};
        level -= 1;
        size_ -= 1;

        prefix = detail::BitsSlice<uint32_t>{bits, 0, len};
        while (level--) {
            auto const slice = prefix.sub(level * detail::stride);
            detail::NodeVec vec{stack[level]->children,
                                stack[level]->external_bitmap.total(),
                                stack[level]->internal_bitmap.total()};

            if (vec.size() < 2) {
                std::free(stack[level]->children);
                stack[level]->children = nullptr;
                stack[level]->external_bitmap = {};
            } else {
                vec.erase_branch(slice.value());
                stack[level]->children = vec.data();
                stack[level]->external_bitmap.unset(slice.value());
                break;
            }
        }
    }

private:
    detail::Node root_;
    size_t size_{0};
};

} // namespace everload_trie
