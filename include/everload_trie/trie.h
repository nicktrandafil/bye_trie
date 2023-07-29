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
#include <vector>

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

    std::optional<uint8_t> longest_before(uint8_t i, uint8_t len) const noexcept {
        assert(i < 32);
        assert(len < stride);
        uint8_t shift = 0;
        switch (len) {
        [[likely]] case 4:
            if (auto const idx = (1u << (15 + (i >> shift))); inner & idx) {
                return std::popcount(inner & (idx - 1));
            }
            shift += 1;
            [[fallthrough]];
        case 3:
            if (auto const idx = (1u << (7 + (i >> shift))); inner & idx) {
                return std::popcount(inner & (idx - 1));
            }
            shift += 1;
            [[fallthrough]];
        case 2:
            if (auto const idx = (1u << (3 + (i >> shift))); inner & idx) {
                return std::popcount(inner & (idx - 1));
            }
            shift += 1;
            [[fallthrough]];
        case 1:
            if (auto const idx = (1u << (1 + (i >> shift))); inner & idx) {
                return std::popcount(inner & (idx - 1));
            }
            [[fallthrough]];
        case 0:
            if (inner & 1) {
                return 0;
            }
        }
        return std::nullopt;
    }

    bool before(uint8_t& values_before, uint8_t i, uint8_t len) const noexcept {
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

    size_t total() const noexcept {
        return static_cast<size_t>(std::popcount(inner));
    }

    void set(uint8_t i, uint8_t len) {
        assert(i < 32);
        assert(len < stride);
        switch (len) {
        [[likely]] case 4:
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
            inner |= 1;
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

    size_t total() const noexcept {
        return static_cast<size_t>(std::popcount(inner));
    }

    void set(uint8_t i) {
        assert(i < 32);
        inner |= 1u << i;
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

inline constexpr size_t max_prefix_len = 16; // bytes

template <class T>
concept UnsignedIntegral = std::unsigned_integral<T>
                        || (std::is_trivial_v<T> && sizeof(T) <= max_prefix_len
                            && requires(T val) {
                                   { val << 1 };
                                   { val >> 1 };
                                   { val& val };
                                   { val - val };
                                   { val == val };
                                   { static_cast<uint64_t>(val) };
                               });

template <UnsignedIntegral T>
class BitsSlice {
public:
    constexpr BitsSlice(T bits, uint8_t start, uint8_t len) noexcept
            : bits_(bits)
            , start_(start)
            , len_(len) {
    }

    uint8_t len() const noexcept {
        return len_;
    }

    explicit operator uint8_t() const noexcept {
        return take_slice(bits_, start_, len_);
    }

    BitsSlice sub(uint8_t start) const noexcept {
        assert(start <= len_);
        BitsSlice ret{*this};
        ret.start_ += start;
        ret.len_ -= start;
        return ret;
    }

    BitsSlice sub(uint8_t start, uint8_t len) const noexcept {
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

} // namespace detail

template <typename T>
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

    /// \return Pointer to the value if it exists, nullptr otherwise
    /// \throw std::bad_alloc
    T* insert(uint32_t bits, uint8_t len, T value) & noexcept(false) {
        detail::Node* node = &root_;
        detail::BitsSlice<uint32_t> prefix{bits, 0, len};
        go_to_leaf(node, prefix);
        extend_leaf(node, prefix);
        return add_value(
                node, prefix.sub(0, std::min(detail::stride_m_1, prefix.len())), value);
    }

    ~Trie() {
        std::vector<detail::Node> stack{{root_}};

        while (stack.size()) {
            // go down
            while (auto const n = stack.back().external_bitmap.total()) {
                auto const i = stack.size();
                stack.resize(i + n);
                std::transform(stack.back().children,
                               stack.back().children + n,
                               stack.begin() + i,
                               [](auto x) { return x.node; });
            }

            // go up
            auto const branches_count = stack.back().external_bitmap.total();
            auto const values_count = stack.back().internal_bitmap.total();
            std::for_each(stack.back().children + branches_count,
                          stack.back().children + branches_count + values_count / 2
                                  + values_count % 2,
                          [](auto x) {
                              delete static_cast<T*>(x.pointers[0]);
                              delete static_cast<T*>(x.pointers[1]);
                          });
            delete[] stack.back().children;
            stack.pop_back();
        }
    }

private:
    static void go_to_leaf(detail::Node*& node, detail::BitsSlice<uint32_t>& prefix) {
        while (prefix.len() >= detail::stride) {
            auto const branch_idx = static_cast<uint8_t>(prefix.sub(0, detail::stride));
            if (node->external_bitmap.exists(branch_idx)) {
                auto const idx = node->external_bitmap.before(branch_idx);
                node = &node->children[idx].node;
            } else {
                break;
            }
            prefix = prefix.sub(detail::stride);
        }
    }

    static void extend_leaf(detail::Node*& node, detail::BitsSlice<uint32_t>& prefix) {
        while (prefix.len() >= detail::stride) {
            auto const branches_count = node->external_bitmap.total();
            auto const values_count = node->internal_bitmap.total();
            auto const n = branches_count + values_count;

            auto const new_children = new detail::ErasedNode[n + 1];

            auto const branch_idx = static_cast<uint8_t>(prefix.sub(0, detail::stride));
            auto const idx = node->external_bitmap.before(branch_idx);

            std::copy_n(node->children, n, new_children);
            delete[] node->children;
            node->children = new_children;

            if (n) [[likely]] {
                std::rotate(std::reverse_iterator(node->children + n),
                            std::reverse_iterator(node->children + n) + 1,
                            std::reverse_iterator(node->children + idx));
            }

            new_children[idx].node = detail::Node{
                    detail::InternalBitMap{0},
                    detail::ExternalBitMap{0},
                    nullptr,
            };
            node->external_bitmap.set(branch_idx);

            node = &node->children[idx].node;
            prefix = prefix.sub(detail::stride);
        }
    }

    T* add_value(detail::Node*& node, detail::BitsSlice<uint32_t> slice, T value) {
        auto const value_idx = static_cast<uint8_t>(slice);

        auto const branches_count = node->external_bitmap.total();

        uint8_t idx;
        auto const idx_has_value =
                node->internal_bitmap.before(idx, value_idx, slice.len());

        if (idx_has_value) {
            auto const child_idx = branches_count + idx / 2;
            return static_cast<T*>(node->children[child_idx].pointers[idx % 2]);
        }

        auto const values_count = node->internal_bitmap.total();
        auto const n = branches_count + values_count / 2;

        if (values_count % 2 == 0) {
            auto const new_children = new detail::ErasedNode[n + 1];
            new_children[n].pointers = detail::TwoPointers{};
            std::copy_n(node->children, n, new_children);
            delete[] node->children;
            node->children = new_children;
        }

        auto const child_idx = branches_count + idx / 2;

        if (values_count) [[likely]] {
            auto const bytes = reinterpret_cast<char*>(node->children);
            std::rotate(std::reverse_iterator(bytes + (n + 1) * 16),
                        std::reverse_iterator(bytes + (n + 1) * 16) + 1 * 8,
                        std::reverse_iterator(bytes + child_idx * 16));
        }

        node->children[child_idx].pointers[0] = new T{value};
        node->internal_bitmap.set(value_idx, slice.len());

        size_ += 1;
        return nullptr;
    }

private:
    detail::Node root_;
    size_t size_{0};
};

} // namespace everload_trie
