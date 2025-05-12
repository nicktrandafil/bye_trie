/*
 * MIT License
 *
 * Copyright (c) 2023 Nicolai Trandafil
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 */

#pragma once

#include "util.h"

#include <bye_trie/bye_trie.h>

#include <algorithm>
#include <variant>

namespace bye_trie {

template <class T>
concept KeyAdaptorC =
        requires {
            typename T::AdapteeType;
            typename T::TargetType;
        } && UnsignedIntegral<typename T::TargetType>
        && requires(Bits<typename T::TargetType> t, typename T::AdapteeType a, uint8_t len) {
               { T::from_target(t) } -> std::convertible_to<typename T::AdapteeType>;
               { T::to_target(a) } -> std::convertible_to<Bits<typename T::TargetType>>;
               { T::truncated(a, len) } -> std::convertible_to<typename T::AdapteeType>;
           };

template <class T>
concept ValueAdapterC = requires {
    typename T::AdapteeType;
    typename T::TargetType;
} && TrivialLittleObject<typename T::TargetType> && requires(typename T::TargetType t, typename T::AdapteeType a) {
    { T::ref(t) } -> std::convertible_to<typename T::AdapteeType&>;
    { T::save(a) } -> std::convertible_to<typename T::TargetType>;
    { T::save(std::move(a)) } -> std::convertible_to<typename T::TargetType>;
    { T::dispose(t) };
};

template <class T, class U, class Z>
concept EitherKeyAdaperC = requires { typename T::AdapteeType; } && requires(typename T::AdapteeType t, U u, Z z) {
    { T::is_first(t) } -> std::convertible_to<bool>;
    { T::as_first(t) } -> std::convertible_to<U>;
    { T::as_second(t) } -> std::convertible_to<Z>;
    { T::from(u) } -> std::convertible_to<typename T::AdapteeType>;
    { T::from(z) } -> std::convertible_to<typename T::AdapteeType>;
};

template <class T>
concept NonTrivialOrBig = !std::is_trivial_v<T> || sizeof(T) > 8;

template <class T>
    requires TrivialLittleObject<T> || NonTrivialOrBig<T>
struct HeapBacked;

template <TrivialLittleObject T>
struct HeapBacked<T> {
    using AdapteeType = T;
    using TargetType = T;

    static AdapteeType& ref(TargetType& x) noexcept {
        return x;
    }

    static TargetType save(AdapteeType x) {
        return x;
    }

    static void dispose(TargetType) {
    }
};

template <NonTrivialOrBig T>
struct HeapBacked<T> {
    using AdapteeType = T;
    using TargetType = T*;

    static AdapteeType& ref(TargetType x) noexcept {
        assert(x);
        return *x;
    }

    static TargetType save(AdapteeType&& x) {
        return new T{std::move(x)};
    }

    static TargetType save(AdapteeType const& x) {
        return new T{x};
    }

    static void dispose(TargetType x) {
        delete x;
    }
};

inline constexpr uint8_t stride = 5;

template <KeyAdaptorC Ka, ValueAdapterC Va>
class NetTrieSubsIterator {
    using Inner = SubsIterator<typename Ka::TargetType, typename Va::TargetType, stride>;

public:
    NetTrieSubsIterator() = default;

    explicit NetTrieSubsIterator(Inner&& x)
            : inner{x} {
    }

    using KeyType = typename Ka::AdapteeType;

    using iterator_category = std::forward_iterator_tag;
    using value_type = Va::AdapteeType;
    using difference_type = std::ptrdiff_t;
    using pointer = value_type*;
    using reference = value_type&;

    KeyType key() const {
        return Ka::from_target(inner.key());
    }

    reference operator*() const {
        return Va::ref(*inner);
    }

    pointer operator->() const {
        return &Va::ref(*inner.operator->());
    }

    NetTrieSubsIterator& operator++() {
        ++inner;
        return *this;
    }

    NetTrieSubsIterator operator++(int) {
        auto ret = *this;
        ++inner;
        return ret;
    }

    bool operator==(NetTrieSubsIterator const& rhs) const = default;

    void go_to_longest(KeyType const& k) {
        inner.go_to_longest(Ka::to_target(k));
    }

private:
    template <KeyAdaptorC, ValueAdapterC, Allocator Alloc>
    friend class NetTrie;

    Inner inner;
};

template <KeyAdaptorC Ka, ValueAdapterC Va>
class NetTrieIterator {
    using Inner = Iterator<typename Ka::TargetType, typename Va::TargetType, stride>;

public:
    NetTrieIterator() = default;

    explicit NetTrieIterator(Inner&& x)
            : inner{std::move(x)} {
    }

    using KeyType = Ka::AdapteeType;

    using iterator_category = std::forward_iterator_tag;
    using value_type = Va::AdapteeType;
    using difference_type = std::ptrdiff_t;
    using pointer = value_type*;
    using reference = value_type&;

    KeyType key() const {
        return Ka::from_target(inner.key());
    }

    reference operator*() const {
        return Va::ref(*inner);
    }

    pointer operator->() const {
        return &Va::ref(*inner.operator->());
    }

    NetTrieIterator& operator++() {
        ++inner;
        return *this;
    }

    NetTrieIterator operator++(int) {
        auto ret = *this;
        ++inner;
        return ret;
    }

    bool operator==(NetTrieIterator const& rhs) const = default;

    bool next_super() {
        return inner.next_super();
    }

private:
    template <KeyAdaptorC, ValueAdapterC, Allocator>
    friend class NetTrie;

    Inner inner;
};

template <KeyAdaptorC Ka, ValueAdapterC Va, Allocator Alloc = SystemAllocator>
class NetTrie {
    using Inner = ByeTrie<typename Ka::TargetType, typename Va::TargetType, Alloc, stride>;

public:
    using KeyType = Ka::AdapteeType;
    using ValueType = Va::AdapteeType;

    using Iterator = NetTrieIterator<Ka, Va>;
    using SubsIterator = NetTrieSubsIterator<Ka, Va>;

    NetTrie() = default;

    NetTrie(NetTrie&&) = default;

    NetTrie& operator=(NetTrie&& rhs) {
        this->~NetTrie();
        new (this) NetTrie(std::move(rhs));
        return *this;
    }

    NetTrie(NetTrie const& rhs) {
        for (auto it = rhs.begin(); it != rhs.end(); ++it) {
            this->insert(it.key(), ValueType{*it});
        }
    }

    NetTrie& operator=(NetTrie const& rhs) {
        NetTrie tmp{rhs};
        return *this = std::move(tmp);
    }

    ~NetTrie() noexcept {
        for (auto x : inner) {
            Va::dispose(x);
        }
    }

    bool operator==(NetTrie const& rhs) const {
        if (this->size() != rhs.size()) {
            return false;
        }

        for (auto it1 = begin(), e1 = end(), it2 = rhs.begin(), e2 = rhs.end(); it1 != e1 && it2 != e2; ++it1, ++it2) {
            if (it1.key() != it2.key() || *it1 != *it2) {
                return false;
            }
        }

        return true;
    }

    NetTrieIterator<Ka, Va> begin() const {
        return NetTrieIterator<Ka, Va>{inner.begin()};
    }

    NetTrieIterator<Ka, Va> end() const {
        return NetTrieIterator<Ka, Va>{inner.end()};
    }

    /// \return A pointer to the value, and a boolean that is `true` if the value was
    /// newly inserted.
    /// \post `value` is moved only if it is inserted
    std::pair<ValueType*, bool> insert(KeyType const& key, ValueType&& value) {
        return insert_impl(key, std::move(value));
    }

    /// \return A pointer to the value, and a boolean that is `true` if the value was
    /// newly inserted.
    std::pair<ValueType*, bool> insert(KeyType const& key, ValueType const& value) {
        return insert_impl(key, value);
    }

    /// \node You must assume, that invalidates all iterators. If you want to iterate and
    /// selectively remove prefixes, use the iterator overload of this function.
    bool erase(KeyType const& key) {
        if (auto const inner = this->inner.erase(Ka::to_target(key))) {
            Va::dispose(*inner);
            return true;
        } else {
            return false;
        }
    }

    /// \pre A valid and not `end()` iterator.
    /// \return Iterator to the element after the removed one.
    /// \post It is unspecified what iterators are invalidated, except that the returned
    /// iterator is valid and points to the next element after the removed.
    NetTrieIterator<Ka, Va> erase(NetTrieIterator<Ka, Va> it) noexcept(false) {
        return NetTrieIterator<Ka, Va>{inner.erase(it.inner)};
    }

    /// \pre A valid and not 'end' iterator.
    /// \return Iterator to the element after the removed one.
    /// \post It is unspecified what iterators are invalidated, except that the returned
    /// iterator is valid and points to the next element after the removed.
    NetTrieSubsIterator<Ka, Va> erase(NetTrieSubsIterator<Ka, Va> it) noexcept(false) {
        return NetTrieSubsIterator<Ka, Va>{inner.erase(it.inner)};
    }

    void clear() noexcept {
        *this = NetTrie{};
    }

    ValueType* match_exact(KeyType const& key) const {
        auto inner = this->inner.match_exact_ptr(Ka::to_target(key));
        return inner ? &Va::ref(*inner) : nullptr;
    }

    NetTrieIterator<Ka, Va> match_exact_iter(KeyType const& key) const {
        return NetTrieIterator<Ka, Va>{inner.match_exact_iter(Ka::to_target(key))};
    }

    std::optional<std::pair<KeyType, ValueType*>> match_longest(KeyType key) const {
        auto res = inner.match_longest_ptr(Ka::to_target(key));
        if (!res) {
            return std::nullopt;
        }
        return std::pair{Ka::truncated(key, res->first), &Va::ref(*res->second)};
    }

    NetTrieIterator<Ka, Va> match_longest_iter(KeyType const& key) const {
        return NetTrieIterator<Ka, Va>{inner.match_longest_iter(Ka::to_target(key))};
    }

    /// Visit super prefixes of `prefix` with `on_super(prefix, T&)` callback in
    /// descending order, first visited the largest super networks.
    template <class F>
        requires requires(KeyType prefix, ValueType& value, F const& cb) {
            { cb(prefix, value) };
        }
    void visit_supers(KeyType const& prefix, F const& on_super) const {
        inner.visit_supers(Ka::to_target(prefix),
                           [&on_super](auto x, auto& y) { on_super(Ka::from_target(x), Va::ref(y)); });
    }

    NetTrieSubsIterator<Ka, Va> subs(KeyType const& prefix) const {
        return NetTrieSubsIterator<Ka, Va>(inner.subs(Ka::to_target(prefix)));
    }

    size_t size() const noexcept {
        return inner.size();
    }

    bool empty() const noexcept {
        return size() == 0;
    }

private:
    /// \post `value` is consumed only and only if `inserted` is true
    template <class Value>
    std::pair<ValueType*, bool> insert_impl(KeyType const& key, Value&& value)
        requires(std::is_convertible_v<Value, ValueType>)
    {
        auto [inner_ptr, inserted] = this->inner.insert_ptr(Ka::to_target(key), {});
        if (inserted) {
            *inner_ptr = Va::save(std::forward<Value>(value));
        }
        return {&Va::ref(*inner_ptr), inserted};
    }

private:
    Inner inner;
};

template <class T>
concept IteratorC = (std::forward_iterator<T> && requires { typename T::KeyType; });

template <class T>
concept NetTrieC = requires {
    typename T::KeyType;
    typename T::ValueType;
};

template <class Ka, class T1, class T2>
    requires(IteratorC<T1> && IteratorC<T2> && EitherKeyAdaperC<Ka, typename T1::KeyType, typename T2::KeyType>)
class EitherNetTrieSubsIterator {
    using Inner = std::variant<T1, T2>;

public:
    EitherNetTrieSubsIterator() = default;

    explicit EitherNetTrieSubsIterator(T1&& x)
            : inner{std::move(x)} {
    }

    explicit EitherNetTrieSubsIterator(T2&& x)
            : inner{std::move(x)} {
    }

    using KeyType = Ka::AdapteeType;

    using iterator_category = std::forward_iterator_tag;
    using value_type = T1::value_type;
    using difference_type = std::ptrdiff_t;
    using pointer = value_type*;
    using reference = value_type&;

    KeyType key() const {
        return std::visit([](auto const& x) { return Ka::from(x.key()); }, inner);
    }

    reference operator*() const {
        return std::visit([](auto& x) -> decltype(auto) { return x.operator*(); }, inner);
    }

    pointer operator->() const {
        return std::visit([](auto const& x) { return x.operator->(); }, inner);
    }

    EitherNetTrieSubsIterator& operator++() {
        std::visit([](auto& x) { ++x; }, inner);
        return *this;
    }

    bool operator==(EitherNetTrieSubsIterator const& rhs) const noexcept {
        return (is_end() && rhs.is_end()) || (inner == rhs.inner);
    }

    /// Match longest prefix, that is not shorter than current.
    /// \see `NetTrie::match_longest`.
    void go_to_longest(KeyType const& k) {
        if (auto const inner = std::get_if<T1>(&this->inner)) {
            inner->go_to_longest(Ka::as_first(k));
        } else if (auto const inner = std::get_if<T2>(&this->inner)) {
            inner->go_to_longest(Ka::as_second(k));
        } else {
            assert(false);
        }
    }

private:
    bool is_end() const noexcept {
        return std::visit([](auto const& x) { return x == std::decay_t<decltype(x)>{}; }, inner);
    }

    template <class Ka_2, class T1_2, class T2_2>
        requires(NetTrieC<T1_2> && NetTrieC<T2_2> && std::is_same_v<typename T1_2::ValueType, typename T2_2::ValueType>
                 && EitherKeyAdaperC<Ka_2, typename T1_2::KeyType, typename T2_2::KeyType>)
    friend class JoinedNetTrie;

    Inner inner;
};

template <class Ka, class T1, class T2>
    requires(IteratorC<T1> && IteratorC<T2> && std::is_same_v<typename T1::value_type, typename T2::value_type>
             && EitherKeyAdaperC<Ka, typename T1::KeyType, typename T2::KeyType>)
class JoinedNetTrieIterator {
public:
    explicit JoinedNetTrieIterator(T1&& first, T1&& first_end, T2&& second)
            : first{std::move(first)}
            , first_end{std::move(first_end)}
            , second{std::move(second)} {
    }

    using KeyType = Ka::AdapteeType;

    using iterator_category = std::forward_iterator_tag;
    using value_type = typename T1::value_type;
    using difference_type = std::ptrdiff_t;
    using pointer = value_type*;
    using reference = value_type&;

    KeyType key() const {
        return first != first_end ? Ka::from(first.key()) : Ka::from(second.key());
    }

    reference operator*() const {
        return first != first_end ? *first : *second;
    }

    pointer operator->() const {
        return first != first_end ? first.operator->() : second.operator->();
    }

    JoinedNetTrieIterator& operator++() {
        if (first != first_end) {
            ++first;
        } else {
            ++second;
        }
        return *this;
    }

    bool operator==(JoinedNetTrieIterator const& rhs) const = default;

    bool next_super() {
        if (first != first_end) {
            return first.next_super();
        } else {
            return second.next_super();
        }
    }

private:
    template <class Ka_2, class T1_2, class T2_2>
        requires(NetTrieC<T1_2> && NetTrieC<T2_2> && std::is_same_v<typename T1_2::ValueType, typename T2_2::ValueType>
                 && EitherKeyAdaperC<Ka_2, typename T1_2::KeyType, typename T2_2::KeyType>)
    friend struct JoinedNetTrie;

    T1 first;
    T1 first_end;
    T2 second;
};

template <class Ka, class T1, class T2>
    requires(NetTrieC<T1> && NetTrieC<T2> && std::is_same_v<typename T1::ValueType, typename T2::ValueType>
             && EitherKeyAdaperC<Ka, typename T1::KeyType, typename T2::KeyType>)
class JoinedNetTrie {
public:
    using KeyType = typename Ka::AdapteeType;
    using ValueType = typename T1::ValueType;
    using Iterator = JoinedNetTrieIterator<Ka, typename T1::Iterator, typename T2::Iterator>;
    using SubsIterator = EitherNetTrieSubsIterator<Ka, typename T1::SubsIterator, typename T2::SubsIterator>;

    T1 first;
    T2 second;

    JoinedNetTrie() = default;

    JoinedNetTrie(JoinedNetTrie const&) = default;

    JoinedNetTrie& operator=(JoinedNetTrie const&) = default;

    JoinedNetTrie(JoinedNetTrie&&) = default;

    JoinedNetTrie& operator=(JoinedNetTrie&&) = default;

    void clear() noexcept {
        *this = JoinedNetTrie{};
    }

    Iterator begin() const {
        return Iterator{first.begin(), first.end(), second.begin()};
    }

    Iterator end() const {
        return Iterator{first.end(), first.end(), second.end()};
    }

    bool operator==(JoinedNetTrie const& rhs) const {
        return first == rhs.first && second == rhs.second;
    }

    /// \return A pointer to the value, and a boolean that is `true` if the value was
    /// newly inserted.
    /// \post `value` is moved only if it is inserted
    std::pair<ValueType*, bool> insert(KeyType const& key, ValueType&& value) {
        return insert_impl(key, std::move(value));
    }

    /// \return A pointer to the value, and a boolean that is `true` if the value was
    /// newly inserted.
    std::pair<ValueType*, bool> insert(KeyType const& key, ValueType const& value) {
        return insert_impl(key, value);
    }

    /// Erase `key`.
    /// \throw Forwards `Alloc::realloc` exception.
    /// \node It is unspecified what iterators are invalidated. If you want to iterate and
    /// selectively remove prefixes, use the iterator overload of this function.
    /// \post The iterator pointing to the erased element remains valid to increment and
    /// call `key()`.
    bool erase(KeyType const& key) noexcept {
        if (Ka::is_first(key)) {
            return first.erase(Ka::as_first(key));
        } else {
            return second.erase(Ka::as_second(key));
        }
    }

    /// \pre A valid and not `end()` iterator.
    /// \return Iterator to the element after the removed one.
    /// \post It is unspecified what iterators are invalidated, except that the returned
    /// iterator is valid and points to the next element after the removed.
    /// \throw std::bad_alloc. Forwards `Alloc::realloc` exception.
    [[nodiscard]] Iterator erase(Iterator it) noexcept(false) {
        if (Ka::is_first(it.key())) {
            it.first = first.erase(it.first);
        } else {
            it.second = second.erase(it.second);
        }
        return it;
    }

    /// \pre A valid and not 'end' iterator.
    /// \return Iterator to the element after the removed one.
    /// \post It is unspecified what iterators are invalidated, except that the returned
    /// iterator is valid and points to the next element after the removed.
    /// \throw std::bad_alloc. Forwards `Alloc::realloc` exception.
    [[nodiscard]] auto erase(SubsIterator it) noexcept(false) {
        if (Ka::is_first(it.key())) {
            it.inner = first.erase(std::get<0>(it.inner));
        } else {
            it.inner = second.erase(std::get<1>(it.inner));
        }
        return it;
    }

    ValueType* match_exact(KeyType const& key) const noexcept {
        if (Ka::is_first(key)) {
            return first.match_exact(Ka::as_first(key));
        } else {
            return second.match_exact(Ka::as_second(key));
        }
    }

    Iterator match_exact_iter(KeyType const& key) const {
        if (Ka::is_first(key)) {
            auto res = first.match_exact_iter(Ka::as_first(key));
            Iterator ret{std::move(res), first.end(), second.end()};
            if (ret.first == ret.first_end) {
                ret.second = second.end();
            }
            return ret;
        } else {
            return Iterator{first.end(), first.end(), second.match_exact_iter(Ka::as_second(key))};
        }
    }

    std::optional<std::pair<KeyType, ValueType*>> match_longest(KeyType const& key) const noexcept {
        if (Ka::is_first(key)) {
            auto res = first.match_longest(Ka::as_first(key));
            if (!res) {
                return std::nullopt;
            }
            return std::pair{Ka::from(res->first), res->second};
        } else {
            auto res = second.match_longest(Ka::as_second(key));
            if (!res) {
                return std::nullopt;
            }
            return std::pair{Ka::from(res->first), res->second};
        }
    }

    Iterator match_longest_iter(KeyType const& key) const {
        if (Ka::is_first(key)) {
            auto res = first.match_longest_iter(Ka::as_first(key));
            Iterator ret{std::move(res), first.end(), second.end()};
            if (ret.first == ret.first_end) {
                ret.second = second.end();
            }
            return ret;
        } else {
            return Iterator{first.end(), first.end(), second.match_longest_iter(Ka::as_second(key))};
        }
    }

    template <class F>
        requires requires(KeyType prefix, ValueType& value, F const& cb) {
            { cb(prefix, value) };
        }
    void visit_supers(KeyType const& key, F const& on_super) const {
        if (Ka::is_first(key)) {
            first.visit_supers(Ka::as_first(key), on_super);
        } else {
            second.visit_supers(Ka::as_second(key), on_super);
        }
    }

    SubsIterator subs(KeyType const& key) const {
        if (Ka::is_first(key)) {
            return SubsIterator{first.subs(Ka::as_first(key))};
        } else {
            return SubsIterator{second.subs(Ka::as_second(key))};
        }
    }

    size_t size() const noexcept {
        return first.size() + second.size();
    }

    bool empty() const noexcept {
        return size() == 0;
    }

private:
    template <std::convertible_to<ValueType> Value>
    std::pair<ValueType*, bool> insert_impl(KeyType const& key, Value&& value) {
        if (Ka::is_first(key)) {
            return first.insert(Ka::as_first(key), std::forward<Value>(value));
        } else {
            return second.insert(Ka::as_second(key), std::forward<Value>(value));
        }
    }
};

} // namespace bye_trie
