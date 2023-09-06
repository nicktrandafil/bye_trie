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

#include <cassert>
#include <cstddef>
#include <cstdint>

namespace everload_trie {

class Uint128 {
public:
    constexpr Uint128() = default;

    constexpr Uint128(__uint128_t x) noexcept
            : inner{x} {
    }

    constexpr bool operator==(Uint128 const& other) const noexcept = default;

    operator __uint128_t() const noexcept {
        return inner;
    }

    Uint128& operator++() noexcept {
        ++inner;
        return *this;
    }

    friend constexpr inline Uint128 take_slice(Uint128 value,
                                               uint8_t start,
                                               uint8_t len) noexcept {
        assert(start < 128);
        assert(start + len <= 128);
        return (len == 128) ? (value.inner >> start)
                            : ((value.inner >> start) & ((__uint128_t(1) << len) - 1));
    }

private:
    __uint128_t inner;
};

} // namespace everload_trie
