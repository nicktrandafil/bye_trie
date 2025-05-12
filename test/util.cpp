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

#include "util.h"

#include <catch2/catch_all.hpp>

using namespace bye_trie;

TEST_CASE("Reversing bits of bytes") {
    SECTION("uint32_t") {
        REQUIRE(bytes_reversed<uint32_t>(0b00000000'00000000'10100000'01010000)
                == 0b00000000'00000000'00000101'00001010);
    }

    SECTION("__uint128_t") {
        REQUIRE(bytes_reversed<__uint128_t>(
                        __uint128_t{0b00000000'00000000'10100000'01010000})
                == __uint128_t{0b00000000'00000000'00000101'00001010});
    }
}
