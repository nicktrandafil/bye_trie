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

TEST_CASE("", "[InternalBitMap][set][unset][exists]") {
    detail::InternalBitMap bitmap(0b0'1000000000001010'10000010'1001'10'1);
    SECTION("4 length") {
        uint8_t idx;
        REQUIRE(!bitmap.exists(idx, 14, 4));
        bitmap.set(14, 4);
        REQUIRE(bitmap.exists(idx, 14, 4));
        REQUIRE(idx == 8);
        bitmap.unset(14, 4);
        REQUIRE(!bitmap.exists(idx, 14, 4));
    }

    SECTION("3 length") {
        uint8_t idx;
        REQUIRE(!bitmap.exists(idx, 6, 3));
        bitmap.set(6, 3);
        REQUIRE(bitmap.exists(idx, 6, 3));
        REQUIRE(idx == 5);
        bitmap.unset(6, 3);
        REQUIRE(!bitmap.exists(idx, 6, 3));
    }

    SECTION("2 length") {
        uint8_t idx;
        REQUIRE(!bitmap.exists(idx, 2, 2));
        bitmap.set(2, 2);
        REQUIRE(bitmap.exists(idx, 2, 2));
        REQUIRE(idx == 3);
        bitmap.unset(2, 2);
        REQUIRE(!bitmap.exists(idx, 2, 2));
    }

    SECTION("1 length") {
        uint8_t idx;
        REQUIRE(!bitmap.exists(idx, 0, 1));
        bitmap.set(0, 1);
        REQUIRE(bitmap.exists(idx, 0, 1));
        REQUIRE(idx == 1);
        bitmap.unset(0, 1);
        REQUIRE(!bitmap.exists(idx, 0, 1));
    }

    SECTION("0 length") {
        uint8_t idx;
        REQUIRE(bitmap.exists(idx, 0, 0));
        bitmap.unset(0, 0);
        REQUIRE(!bitmap.exists(idx, 0, 0));
        bitmap.set(0, 0);
        REQUIRE(bitmap.exists(idx, 0, 0));
        REQUIRE(idx == 0);
    }
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
        vec.insert_branch(0, detail::Node{{}, {}, &fake[0]});
        REQUIRE(vec.branches().size() == 1);
        REQUIRE(vec.branches()[0].node.children == &fake[0]);

        SECTION("insert a branch before") {
            vec.insert_branch(0, detail::Node{{}, {}, &fake[1]});
            REQUIRE(vec.branches().size() == 2);
            REQUIRE(vec.branches()[0].node.children == &fake[1]);
            REQUIRE(vec.branches()[1].node.children == &fake[0]);
        }

        SECTION("insert a branch after") {
            vec.insert_branch(1, detail::Node{{}, {}, &fake[1]});
            REQUIRE(vec.branches().size() == 2);
            REQUIRE(vec.branches()[0].node.children == &fake[0]);
            REQUIRE(vec.branches()[1].node.children == &fake[1]);
        }

        SECTION("insert a branch between") {
            vec.insert_branch(1, detail::Node{{}, {}, &fake[1]});
            vec.insert_branch(1, detail::Node{{}, {}, &fake[2]});
            REQUIRE(vec.branches().size() == 3);
            REQUIRE(vec.branches()[0].node.children == &fake[0]);
            REQUIRE(vec.branches()[1].node.children == &fake[2]);
            REQUIRE(vec.branches()[2].node.children == &fake[1]);
        }
    }
}

TEST_CASE("Erase value", "[NodeVec][erase_value]") {
    detail::NodeVec vec{nullptr, 0, 0};
    MallocResource guard{&vec};
    std::array<detail::ErasedNode, 3> fake;
    vec.insert_value(0, &fake[0]);
    vec.insert_value(1, &fake[1]);
    vec.insert_value(2, &fake[2]);
    SECTION("erase first") {
        vec.erase_value(0);
        REQUIRE(vec.values().size() == 2);
        REQUIRE(vec.value(0) == &fake[1]);
        REQUIRE(vec.value(1) == &fake[2]);
    }
    SECTION("erase last") {
        vec.erase_value(2);
        REQUIRE(vec.values().size() == 2);
        REQUIRE(vec.value(0) == &fake[0]);
        REQUIRE(vec.value(1) == &fake[1]);
    }
    SECTION("erase middle") {
        vec.erase_value(1);
        REQUIRE(vec.values().size() == 2);
        REQUIRE(vec.value(0) == &fake[0]);
        REQUIRE(vec.value(1) == &fake[2]);
    }
}

TEST_CASE("Erase branch", "[NodeVec][erase_branch]") {
    detail::NodeVec vec{nullptr, 0, 0};
    MallocResource guard{&vec};
    std::array<detail::ErasedNode, 3> fake;
    vec.insert_branch(0, detail::Node{{}, {}, &fake[0]});
    vec.insert_branch(1, detail::Node{{}, {}, &fake[1]});
    vec.insert_branch(2, detail::Node{{}, {}, &fake[2]});
    SECTION("erase first") {
        vec.erase_branch(0);
        REQUIRE(vec.branches().size() == 2);
        REQUIRE(vec.branches()[0].node.children == &fake[1]);
        REQUIRE(vec.branches()[1].node.children == &fake[2]);
    }
    SECTION("erase last") {
        vec.erase_branch(2);
        REQUIRE(vec.branches().size() == 2);
        REQUIRE(vec.branches()[0].node.children == &fake[0]);
        REQUIRE(vec.branches()[1].node.children == &fake[1]);
    }
    SECTION("erase middle") {
        vec.erase_branch(1);
        REQUIRE(vec.branches().size() == 2);
        REQUIRE(vec.branches()[0].node.children == &fake[0]);
        REQUIRE(vec.branches()[1].node.children == &fake[2]);
    }
}

TEST_CASE("Insert values", "[Trie][insert]") {
    SECTION("No branching") {
        everload_trie::Trie<long> trie;
        SECTION("insert the first value") {
            REQUIRE(trie.insert(1, 4, 1) == std::nullopt);
            SECTION("value already exists") {
                REQUIRE(*trie.insert(1, 4, 100) == 1);
            }

            SECTION("insert a value before") {
                REQUIRE(trie.insert(0, 4, 2) == std::nullopt);
                SECTION("value already exists") {
                    REQUIRE(*trie.insert(0, 4, 100) == 2);
                }
            }

            SECTION("insert a value after") {
                REQUIRE(trie.insert(2, 4, 2) == std::nullopt);
                SECTION("value already exists") {
                    REQUIRE(*trie.insert(2, 4, 100) == 2);
                }
            }

            SECTION("insert a value between") {
                REQUIRE(trie.insert(4, 4, 2) == std::nullopt);
                REQUIRE(trie.insert(3, 4, 3) == std::nullopt);
                SECTION("values already exist") {
                    REQUIRE(*trie.insert(4, 4, 100) == 2);
                    REQUIRE(*trie.insert(3, 4, 100) == 3);
                }
            }
        }
    }

    SECTION("Branching") {
        everload_trie::Trie<long> trie;
        SECTION("insert the first branch") {
            REQUIRE(trie.insert(0b0000'00001, 6, 1) == std::nullopt);
            SECTION("value already exists") {
                REQUIRE(*trie.insert(0b0000'00001, 6, 100) == 1);
            }

            SECTION("insert a branch before") {
                REQUIRE(trie.insert(0b0000'0000, 6, 2) == std::nullopt);
                SECTION("value already exists") {
                    REQUIRE(*trie.insert(0b0000'0000, 6, 100) == 2);
                }
            }

            SECTION("insert a branch after") {
                REQUIRE(trie.insert(0b0000'00010, 6, 2) == std::nullopt);
                SECTION("value already exists") {
                    REQUIRE(*trie.insert(0b0000'00010, 6, 100) == 2);
                }
            }

            SECTION("insert a branch between") {
                REQUIRE(trie.insert(0b0000'00100, 6, 2) == std::nullopt);
                REQUIRE(trie.insert(0b0000'00011, 6, 3) == std::nullopt);
                SECTION("values already exist") {
                    REQUIRE(*trie.insert(0b0000'00100, 6, 100) == 2);
                    REQUIRE(*trie.insert(0b0000'00011, 6, 100) == 3);
                }
            }
        }
    }
}

TEST_CASE("", "[Trie][replace]") {
    everload_trie::Trie<long> trie;
    REQUIRE(trie.replace(0b0'00001, 6, 1) == std::nullopt);
    REQUIRE(trie.replace(0b0'00001, 6, 2) == 1);
    REQUIRE(trie.replace(0b0'00001, 6, 3) == 2);
}

TEST_CASE("Match exact prefixes", "[Trie][match_exact]") {
    everload_trie::Trie<long> trie;

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
        REQUIRE(trie.match_exact(0, 5) == std::nullopt);
        REQUIRE(trie.match_exact(1, 4) == std::nullopt);
    }
}

TEST_CASE("Match longest prefixes", "[Trie][match_longest]") {
    everload_trie::Trie<long> trie;
    trie.insert(0b0000, 4, 0);
    trie.insert(0b001, 3, 1);
    trie.insert(0b0000'00001, 6, 2);

    SECTION("positive") {
        SECTION("exact") {
            auto const [len, value] = *trie.match_longest(0b10000, 5);
            REQUIRE(len == 4);
            REQUIRE(value == 0);
        }

        SECTION("4 longest bits, the same level") {
            auto const [len, value] = *trie.match_longest(0b00000, 5);
            REQUIRE(len == 4);
            REQUIRE(value == 0);
        }

        SECTION("3 longest bits, previous level") {
            auto const [len, value] = *trie.match_longest(0b00'10001, 7);
            REQUIRE(len == 3);
            REQUIRE(value == 1);
        }

        SECTION("6 longest bits, the same level") {
            auto const [len, value] = *trie.match_longest(0b10'00001, 7);
            REQUIRE(len == 6);
            REQUIRE(value == 2);
        }
    }

    SECTION("negative basic") {
        REQUIRE(!trie.match_longest(0b00010, 5));
        REQUIRE(!trie.match_longest(0b11000, 5));
    }
}

TEST_CASE("Erase values", "[Trie][erase_exact]") {
    SECTION("Not found") {
        everload_trie::Trie<long> trie;
        REQUIRE(!trie.erase_exact(0, 5));
        REQUIRE(!trie.erase_exact(0, 4));
    }
    SECTION("No unfold-cleaning") {
        everload_trie::Trie<long> trie;
        trie.insert(0b0'00000'00000, 11, 0);
        trie.insert(0b1'00000'00000, 11, 1);
        REQUIRE(trie.erase_exact(0b0'00000'00000, 11));
        REQUIRE(trie.size() == 1);
        REQUIRE(*trie.match_exact(0b1'00000'00000, 11) == 1);
    }
    SECTION("Unfold-cleaning just the leaf which contains the value") {
        everload_trie::Trie<long> trie;
        trie.insert(0b0'00000'00000, 11, 0);
        trie.insert(0b0'00000, 6, 1);
        REQUIRE(trie.erase_exact(0b0'00000'00000, 11));
        REQUIRE(trie.size() == 1);
        REQUIRE(*trie.match_exact(0b0'00000, 6) == 1);
    }
    SECTION("Unfold-cleaning the branch up to the root") {
        everload_trie::Trie<long> trie;
        trie.insert(0b0'00000'00000, 11, 0);
        REQUIRE(trie.erase_exact(0b0'00000'00000, 11));
        REQUIRE(trie.size() == 0);
    }
    SECTION("Unfold-cleaning the branch in case there is just root node") {
        everload_trie::Trie<long> trie;
        trie.insert(0b0001, 4, 0);
        REQUIRE(trie.erase_exact(0b0001, 4));
        REQUIRE(trie.size() == 0);
    }
}
