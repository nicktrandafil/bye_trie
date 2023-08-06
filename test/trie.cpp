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

TEST_CASE("", "[ExternalBitMap][exists][before]") {
    detail::ExternalBitMap bitmap(0b110);
    REQUIRE(!bitmap.exists(0));
    REQUIRE(bitmap.exists(1));
    REQUIRE(bitmap.before(0) == 0);
    REQUIRE(bitmap.before(1) == 0);
    REQUIRE(bitmap.before(2) == 1);
    REQUIRE(bitmap.before(3) == 2);
    REQUIRE(bitmap.before(4) == 2);
}

TEST_CASE("", "[InternalBitMap][longest_before]") {
    detail::InternalBitMap bitmap(0b0'1000000000001010'10000010'1001'10'1);
    uint8_t idx;

    SECTION("4") {
        SECTION("match") {
            REQUIRE(bitmap.find_longest(idx, 0b1111, 4).value() == 4);
            REQUIRE(idx == 8);
            REQUIRE(bitmap.find_longest(idx, 0b11, 4).value() == 4);
            REQUIRE(idx == 7);
        }
        SECTION("longest") {
            REQUIRE(bitmap.find_longest(idx, 0b0111, 4).value() == 3);
            REQUIRE(idx == 5);
        }
    }

    SECTION("3") {
        SECTION("match") {
            REQUIRE(bitmap.find_longest(idx, 0b111, 3).value() == 3);
            REQUIRE(idx == 5);
        }
        SECTION("longest") {
            REQUIRE(bitmap.find_longest(idx, 0b011, 3).value() == 2);
            REQUIRE(idx == 3);
        }
    }

    SECTION("2") {
        SECTION("match") {
            REQUIRE(bitmap.find_longest(idx, 0b11, 2).value() == 2);
            REQUIRE(idx == 3);
        }
        SECTION("longest") {
            REQUIRE(bitmap.find_longest(idx, 0b01, 2).value() == 1);
            REQUIRE(idx == 1);
        }
    }

    SECTION("1") {
        SECTION("match") {
            REQUIRE(bitmap.find_longest(idx, 0b1, 1).value() == 1);
            REQUIRE(idx == 1);
        }
        SECTION("longest") {
            REQUIRE(bitmap.find_longest(idx, 0b0, 1).value() == 0);
            REQUIRE(idx == 0);
        }
    }

    SECTION("0") {
        SECTION("match") {
            REQUIRE(bitmap.find_longest(idx, 0b0, 0).value() == 0);
            REQUIRE(idx == 0);
        }
        SECTION("longest") {
            REQUIRE(bitmap.find_longest(idx, 0b1, 0).value() == 0);
            REQUIRE(idx == 0);
        }
    }
}

class MallocResource {
public:
    MallocResource(detail::NodeVec* vec)
            : vec(vec) {
    }

    ~MallocResource() noexcept {
        std::free(vec->data());
    }

private:
    detail::NodeVec* vec;
};

TEST_CASE("Branch manipulation", "[NodeVec][with_new_branch]") {
    detail::NodeVec vec{nullptr, 0, 0};
    MallocResource guard{&vec};
    std::array<detail::ErasedNode, 3> fake;
    SECTION("insert the first branch") {
        vec.insert_branch(0,
                          detail::Node{.internal_bitmap = {},
                                       .external_bitmap = {},
                                       .children = &fake[0]});
        REQUIRE(vec.branches().size() == 1);
        REQUIRE(vec.branches()[0].node.children == &fake[0]);

        SECTION("insert a branch before") {
            vec.insert_branch(0,
                              detail::Node{.internal_bitmap = {},
                                           .external_bitmap = {},
                                           .children = &fake[1]});
            REQUIRE(vec.branches().size() == 2);
            REQUIRE(vec.branches()[0].node.children == &fake[1]);
            REQUIRE(vec.branches()[1].node.children == &fake[0]);
        }

        SECTION("insert a branch after") {
            vec.insert_branch(1,
                              detail::Node{.internal_bitmap = {},
                                           .external_bitmap = {},
                                           .children = &fake[1]});
            REQUIRE(vec.branches().size() == 2);
            REQUIRE(vec.branches()[0].node.children == &fake[0]);
            REQUIRE(vec.branches()[1].node.children == &fake[1]);
        }

        SECTION("insert a branch between") {
            vec.insert_branch(1,
                              detail::Node{.internal_bitmap = {},
                                           .external_bitmap = {},
                                           .children = &fake[1]});
            vec.insert_branch(1,
                              detail::Node{.internal_bitmap = {},
                                           .external_bitmap = {},
                                           .children = &fake[2]});
            REQUIRE(vec.branches().size() == 3);
            REQUIRE(vec.branches()[0].node.children == &fake[0]);
            REQUIRE(vec.branches()[1].node.children == &fake[2]);
            REQUIRE(vec.branches()[2].node.children == &fake[1]);
        }
    }
}

TEST_CASE("Values' array manipulation", "[Trie][insert]") {
    everload_trie::Trie<int> trie;
    SECTION("insert the first value") {
        REQUIRE(trie.insert(1, 4, 1) == nullptr);
        SECTION("value already exists") {
            REQUIRE(*trie.insert(1, 4, 100) == 1);
        }

        SECTION("insert a value before") {
            REQUIRE(trie.insert(0, 4, 2) == nullptr);
            SECTION("value already exists") {
                REQUIRE(*trie.insert(0, 4, 100) == 2);
            }
        }

        SECTION("insert a value after") {
            REQUIRE(trie.insert(2, 4, 2) == nullptr);
            SECTION("value already exists") {
                REQUIRE(*trie.insert(2, 4, 100) == 2);
            }
        }

        SECTION("insert a value between") {
            REQUIRE(trie.insert(4, 4, 2) == nullptr);
            REQUIRE(trie.insert(3, 4, 3) == nullptr);
            SECTION("values already exist") {
                REQUIRE(*trie.insert(4, 4, 100) == 2);
                REQUIRE(*trie.insert(3, 4, 100) == 3);
            }
        }
    }
}

TEST_CASE("Branches' array manipulation", "[Trie][insert]") {
    everload_trie::Trie<int> trie;
    SECTION("insert the first branch") {
        REQUIRE(trie.insert(0b0000'00001, 6, 1) == nullptr);
        SECTION("value already exists") {
            REQUIRE(*trie.insert(0b0000'00001, 6, 100) == 1);
        }

        SECTION("insert a branch before") {
            REQUIRE(trie.insert(0b0000'0000, 6, 2) == nullptr);
            SECTION("value already exists") {
                REQUIRE(*trie.insert(0b0000'0000, 6, 100) == 2);
            }
        }

        SECTION("insert a branch after") {
            REQUIRE(trie.insert(0b0000'00010, 6, 2) == nullptr);
            SECTION("value already exists") {
                REQUIRE(*trie.insert(0b0000'00010, 6, 100) == 2);
            }
        }

        SECTION("insert a branch between") {
            REQUIRE(trie.insert(0b0000'00100, 6, 2) == nullptr);
            REQUIRE(trie.insert(0b0000'00011, 6, 3) == nullptr);
            SECTION("values already exist") {
                REQUIRE(*trie.insert(0b0000'00100, 6, 100) == 2);
                REQUIRE(*trie.insert(0b0000'00011, 6, 100) == 3);
            }
        }
    }
}

TEST_CASE("", "[Trie][match]") {
    everload_trie::Trie<int> trie;

    SECTION("positive") {
        trie.insert(0, 4, 0);
        trie.insert(1, 4, 1);
        trie.insert(2, 4, 2);

        trie.insert(0b0000'00001, 6, 3);
        trie.insert(0b0000'00010, 6, 4);
        trie.insert(0b0000'00100, 6, 5);

        SECTION("level 0") {
            REQUIRE(*trie.match_exact(0, 4) == 0);
            REQUIRE(*trie.match_exact(1, 4) == 1);
            REQUIRE(*trie.match_exact(2, 4) == 2);
        }

        SECTION("level 1") {
            REQUIRE(*trie.match_exact(0b0000'00001, 6) == 3);
            REQUIRE(*trie.match_exact(0b0000'00010, 6) == 4);
            REQUIRE(*trie.match_exact(0b0000'00100, 6) == 5);
        }
    }

    SECTION("negative basic") {
        trie.insert(0, 4, 0);
        REQUIRE(trie.match_exact(0, 5) == nullptr);
        REQUIRE(trie.match_exact(1, 4) == nullptr);
    }
}

TEST_CASE("", "[Trie][match_longest]") {
    everload_trie::Trie<int> trie;
    trie.insert(0b0000, 4, 0);
    trie.insert(0b001, 3, 1);
    trie.insert(0b0000'00001, 6, 2);

    SECTION("positive") {
        SECTION("exact") {
            auto const [len, value] = *trie.match_longest(0b10000, 5);
            REQUIRE(len == 4);
            REQUIRE(*value == 0);
        }

        SECTION("4 longest bits, the same level") {
            auto const [len, value] = *trie.match_longest(0b00000, 5);
            REQUIRE(len == 4);
            REQUIRE(*value == 0);
        }

        SECTION("3 longest bits, previous level") {
            auto const [len, value] = *trie.match_longest(0b00'10001, 7);
            REQUIRE(len == 3);
            REQUIRE(*value == 1);
        }

        SECTION("6 longest bits, the same level") {
            auto const [len, value] = *trie.match_longest(0b10'00001, 7);
            REQUIRE(len == 6);
            REQUIRE(*value == 2);
        }
    }

    SECTION("negative basic") {
        REQUIRE(!trie.match_longest(0b00010, 5));
        REQUIRE(!trie.match_longest(0b11000, 5));
    }
}
