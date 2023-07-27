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

#include "everload_trie/trie.h"

#include <catch2/catch_all.hpp>

using namespace everload_trie;

TEST_CASE("ExternalBitMap") {
    detail::ExternalBitMap bitmap(0b110);
    REQUIRE(!bitmap.exists(0));
    REQUIRE(bitmap.exists(1));
    REQUIRE(bitmap.before(0) == 0);
    REQUIRE(bitmap.before(1) == 0);
    REQUIRE(bitmap.before(2) == 1);
    REQUIRE(bitmap.before(3) == 2);
    REQUIRE(bitmap.before(4) == 2);
}

TEST_CASE("InternalBitMap") {
    detail::InternalBitMap bitmap(0b0'1000000000001010'10000010'1010'10'1);
    REQUIRE(bitmap.longest_before(15, 4).value() == 8);
    REQUIRE(bitmap.longest_before(3, 4).value() == 7);
    REQUIRE(bitmap.longest_before(7, 3).value() == 5);
    REQUIRE(bitmap.longest_before(3, 2).value() == 3);
    REQUIRE(bitmap.longest_before(1, 1).value() == 1);
    REQUIRE(bitmap.longest_before(0, 0).value() == 0);
}

TEST_CASE("Trie") {
    everload_trie::Trie<int> trie;
    trie.insert(0b0001, 4, 1);
}
