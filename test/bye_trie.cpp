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

#include "bye_trie/bye_trie.h"

#include "bye_trie/uint128.h"

#include <catch2/catch_all.hpp>

using namespace bye_trie;

using PrefixTypes = std::tuple<uint32_t, uint64_t>;

TEMPLATE_LIST_TEST_CASE("", "[Bits][concatenated]", PrefixTypes) {
    Bits<TestType> slice(0b1100, 4);
    REQUIRE(slice.concatenated({0, 0}).value() == 0b1100);
    REQUIRE(static_cast<unsigned>(slice.concatenated({1, 1}).value()) == 0b11100);
}

TEST_CASE("", "[Bits][operator+=(T)]") {
    Bits<uint8_t> bits;
    bits += 1;
    REQUIRE(bits == Bits<uint8_t>{0, 1});
    bits += 2;
    REQUIRE(bits == Bits<uint8_t>{0, 2});
    bits += 2;
    REQUIRE(bits == Bits<uint8_t>{2, 2});
    bits += 3;
    REQUIRE(bits == Bits<uint8_t>{0, 3});
}

TEST_CASE("", "[ExternalBitmap][exists][before]") {
    detail::ExternalBitmap bitmap(0b110);
    REQUIRE(!bitmap.exists(Bits{0, 5}));
    REQUIRE(bitmap.exists(Bits{1, 5}));
    REQUIRE(bitmap.before(Bits{0, 5}) == 0);
    REQUIRE(bitmap.before(Bits{1, 5}) == 0);
    REQUIRE(bitmap.before(Bits{2, 5}) == 1);
    REQUIRE(bitmap.before(Bits{3, 5}) == 2);
    REQUIRE(bitmap.before(Bits{4, 5}) == 2);
}

TEST_CASE("", "[InternalBitmap][set][unset][exists]") {
    detail::InternalBitmap bitmap(0b0'1000000000001010'10000010'1001'10'1);
    SECTION("4 length") {
        uint8_t idx;
        REQUIRE(!bitmap.exists(idx, Bits{14, 4}));
        bitmap.set(Bits{14, 4});
        REQUIRE(bitmap.exists(idx, Bits{14, 4}));
        REQUIRE(idx == 8);
        bitmap.unset(Bits{14, 4});
        REQUIRE(!bitmap.exists(idx, Bits{14, 4}));
    }

    SECTION("3 length") {
        uint8_t idx;
        REQUIRE(!bitmap.exists(idx, Bits{6, 3}));
        bitmap.set(Bits{6, 3});
        REQUIRE(bitmap.exists(idx, Bits{6, 3}));
        REQUIRE(idx == 5);
        bitmap.unset(Bits{6, 3});
        REQUIRE(!bitmap.exists(idx, Bits{6, 3}));
    }

    SECTION("2 length") {
        uint8_t idx;
        REQUIRE(!bitmap.exists(idx, Bits{2, 2}));
        bitmap.set(Bits{2, 2});
        REQUIRE(bitmap.exists(idx, Bits{2, 2}));
        REQUIRE(idx == 3);
        bitmap.unset(Bits{2, 2});
        REQUIRE(!bitmap.exists(idx, Bits{2, 2}));
    }

    SECTION("1 length") {
        uint8_t idx;
        REQUIRE(!bitmap.exists(idx, Bits{0, 1}));
        bitmap.set(Bits{0, 1});
        REQUIRE(bitmap.exists(idx, Bits{0, 1}));
        REQUIRE(idx == 1);
        bitmap.unset(Bits{0, 1});
        REQUIRE(!bitmap.exists(idx, Bits{0, 1}));
    }

    SECTION("0 length") {
        uint8_t idx;
        REQUIRE(bitmap.exists(idx, Bits{0, 0}));
        bitmap.unset(Bits{0, 0});
        REQUIRE(!bitmap.exists(idx, Bits{0, 0}));
        bitmap.set(Bits{0, 0});
        REQUIRE(bitmap.exists(idx, Bits{0, 0}));
        REQUIRE(idx == 0);
    }
}

TEST_CASE("", "[InternalBitmap][longest_before]") {
    detail::InternalBitmap bitmap(0b0'1000000000001010'10000010'1001'10'1);
    uint8_t idx;

    SECTION("4") {
        SECTION("match") {
            REQUIRE(bitmap.find_longest(idx, Bits{0b1111u, 4}).value() == 4);
            REQUIRE(idx == 8);
            REQUIRE(bitmap.find_longest(idx, Bits{0b11, 4}).value() == 4);
            REQUIRE(idx == 7);
        }
        SECTION("longest") {
            REQUIRE(bitmap.find_longest(idx, Bits{0b0111, 4}).value() == 3);
            REQUIRE(idx == 5);
        }
    }

    SECTION("3") {
        SECTION("match") {
            REQUIRE(bitmap.find_longest(idx, Bits{0b111, 3}).value() == 3);
            REQUIRE(idx == 5);
        }
        SECTION("longest") {
            REQUIRE(bitmap.find_longest(idx, Bits{0b011, 3}).value() == 2);
            REQUIRE(idx == 3);
        }
    }

    SECTION("2") {
        SECTION("match") {
            REQUIRE(bitmap.find_longest(idx, Bits{0b11, 2}).value() == 2);
            REQUIRE(idx == 3);
        }
        SECTION("longest") {
            REQUIRE(bitmap.find_longest(idx, Bits{0b01, 2}).value() == 1);
            REQUIRE(idx == 1);
        }
    }

    SECTION("1") {
        SECTION("match") {
            REQUIRE(bitmap.find_longest(idx, Bits{0b1, 1}).value() == 1);
            REQUIRE(idx == 1);
        }
        SECTION("longest") {
            REQUIRE(bitmap.find_longest(idx, Bits{0b0, 1}).value() == 0);
            REQUIRE(idx == 0);
        }
    }

    SECTION("0") {
        SECTION("match") {
            REQUIRE(bitmap.find_longest(idx, Bits{0b0, 0}).value() == 0);
            REQUIRE(idx == 0);
        }
        SECTION("longest") {
            REQUIRE(bitmap.find_longest(idx, Bits{0b1, 0}).value() == 0);
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
        alloc.dealloc(MemBlk{vec->data(), 0});
    }

    SystemAllocator alloc;

private:
    detail::NodeVec* vec;
};

TEST_CASE("Branch manipulation", "[NodeVec][with_new_branch]") {
    detail::NodeVec vec{nullptr, 0, 0};
    MallocResource guard{&vec};
    std::array<detail::ErasedNode, 3> fake;
    SECTION("insert the first branch") {
        vec.insert_branch(0, detail::Node{{}, {}, &fake[0]}, guard.alloc);
        REQUIRE(vec.branches().size() == 1);
        REQUIRE(vec.branches()[0].node.children == &fake[0]);

        SECTION("insert a branch before") {
            vec.insert_branch(0, detail::Node{{}, {}, &fake[1]}, guard.alloc);
            REQUIRE(vec.branches().size() == 2);
            REQUIRE(vec.branches()[0].node.children == &fake[1]);
            REQUIRE(vec.branches()[1].node.children == &fake[0]);
        }

        SECTION("insert a branch after") {
            vec.insert_branch(1, detail::Node{{}, {}, &fake[1]}, guard.alloc);
            REQUIRE(vec.branches().size() == 2);
            REQUIRE(vec.branches()[0].node.children == &fake[0]);
            REQUIRE(vec.branches()[1].node.children == &fake[1]);
        }

        SECTION("insert a branch between") {
            vec.insert_branch(1, detail::Node{{}, {}, &fake[1]}, guard.alloc);
            vec.insert_branch(1, detail::Node{{}, {}, &fake[2]}, guard.alloc);
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
    vec.insert_value(0, &fake[0], guard.alloc);
    vec.insert_value(1, &fake[1], guard.alloc);
    vec.insert_value(2, &fake[2], guard.alloc);
    SECTION("erase first") {
        vec.erase_value(0, guard.alloc);
        REQUIRE(vec.values().size() == 2);
        REQUIRE(vec.value(0) == &fake[1]);
        REQUIRE(vec.value(1) == &fake[2]);
    }
    SECTION("erase last") {
        vec.erase_value(2, guard.alloc);
        REQUIRE(vec.values().size() == 2);
        REQUIRE(vec.value(0) == &fake[0]);
        REQUIRE(vec.value(1) == &fake[1]);
    }
    SECTION("erase middle") {
        vec.erase_value(1, guard.alloc);
        REQUIRE(vec.values().size() == 2);
        REQUIRE(vec.value(0) == &fake[0]);
        REQUIRE(vec.value(1) == &fake[2]);
    }
}

TEST_CASE("Erase branch", "[NodeVec][erase_branch]") {
    detail::NodeVec vec{nullptr, 0, 0};
    MallocResource guard{&vec};
    std::array<detail::ErasedNode, 3> fake;
    vec.insert_branch(0, detail::Node{{}, {}, &fake[0]}, guard.alloc);
    vec.insert_branch(1, detail::Node{{}, {}, &fake[1]}, guard.alloc);
    vec.insert_branch(2, detail::Node{{}, {}, &fake[2]}, guard.alloc);
    SECTION("erase first") {
        vec.erase_branch(0, guard.alloc);
        REQUIRE(vec.branches().size() == 2);
        REQUIRE(vec.branches()[0].node.children == &fake[1]);
        REQUIRE(vec.branches()[1].node.children == &fake[2]);
    }
    SECTION("erase last") {
        vec.erase_branch(2, guard.alloc);
        REQUIRE(vec.branches().size() == 2);
        REQUIRE(vec.branches()[0].node.children == &fake[0]);
        REQUIRE(vec.branches()[1].node.children == &fake[1]);
    }
    SECTION("erase middle") {
        vec.erase_branch(1, guard.alloc);
        REQUIRE(vec.branches().size() == 2);
        REQUIRE(vec.branches()[0].node.children == &fake[0]);
        REQUIRE(vec.branches()[1].node.children == &fake[2]);
    }
}

TEST_CASE("Insert values", "[ByeTrie][insert]") {
    bye_trie::ByeTrie<uint32_t, long> trie;

    SECTION("No branching") {
        SECTION("insert the first value") {
            REQUIRE(trie.insert(Bits{1u, 4}, 1) == std::nullopt);
            SECTION("value already exists") {
                REQUIRE(*trie.insert(Bits{1u, 4}, 100) == 1);
            }

            SECTION("insert a value before") {
                REQUIRE(trie.insert(Bits{0u, 4}, 2) == std::nullopt);
                SECTION("value already exists") {
                    REQUIRE(*trie.insert(Bits{0u, 4}, 100) == 2);
                }
            }

            SECTION("insert a value after") {
                REQUIRE(trie.insert(Bits{2u, 4}, 2) == std::nullopt);
                SECTION("value already exists") {
                    REQUIRE(*trie.insert(Bits{2u, 4}, 100) == 2);
                }
            }

            SECTION("insert a value between") {
                REQUIRE(trie.insert(Bits{4u, 4}, 2) == std::nullopt);
                REQUIRE(trie.insert(Bits{3u, 4}, 3) == std::nullopt);
                SECTION("values already exist") {
                    REQUIRE(*trie.insert(Bits{4u, 4}, 100) == 2);
                    REQUIRE(*trie.insert(Bits{3u, 4}, 100) == 3);
                }
            }
        }
    }

    SECTION("Branching") {
        SECTION("insert the first branch") {
            REQUIRE(trie.insert(Bits{0b0000'00001u, 6}, 1) == std::nullopt);
            SECTION("value already exists") {
                REQUIRE(*trie.insert(Bits{0b0000'00001u, 6}, 100) == 1);
            }

            SECTION("insert a branch before") {
                REQUIRE(trie.insert(Bits{0b0000'0000u, 6}, 2) == std::nullopt);
                SECTION("value already exists") {
                    REQUIRE(*trie.insert(Bits{0b0000'0000u, 6}, 100) == 2);
                }
            }

            SECTION("insert a branch after") {
                REQUIRE(trie.insert(Bits{0b0000'00010u, 6}, 2) == std::nullopt);
                SECTION("value already exists") {
                    REQUIRE(*trie.insert(Bits{0b0000'00010u, 6}, 100) == 2);
                }
            }

            SECTION("insert a branch between") {
                REQUIRE(trie.insert(Bits{0b0000'00100u, 6}, 2) == std::nullopt);
                REQUIRE(trie.insert(Bits{0b0000'00011u, 6}, 3) == std::nullopt);
                SECTION("values already exist") {
                    REQUIRE(*trie.insert(Bits{0b0000'00100u, 6}, 100) == 2);
                    REQUIRE(*trie.insert(Bits{0b0000'00011u, 6}, 100) == 3);
                }
            }
        }
    }

    SECTION("Longest") {
        REQUIRE(trie.insert(Bits{0xffffffffu, 32}, 0) == std::nullopt);
        REQUIRE(trie.match_exact(Bits{0xffffffffu, 32}) == 0);
    }
}

TEST_CASE("", "[ByeTrie][replace]") {
    bye_trie::ByeTrie<uint32_t, long> trie;
    REQUIRE(trie.replace(Bits{0b0'00001u, 6}, 1) == std::nullopt);
    REQUIRE(trie.replace(Bits{0b0'00001u, 6}, 2) == 1);
    REQUIRE(trie.replace(Bits{0b0'00001u, 6}, 3) == 2);
}

TEST_CASE("Match exact prefixes", "[ByeTrie][match_exact]") {
    bye_trie::ByeTrie<uint32_t, long> trie;

    SECTION("positive") {
        trie.insert(Bits{0u, 4}, 0);
        trie.insert(Bits{1u, 4}, 1);
        trie.insert(Bits{2u, 4}, 2);

        trie.insert(Bits{0b0000'00001u, 6}, 3);
        trie.insert(Bits{0b0000'00010u, 6}, 4);
        trie.insert(Bits{0b0000'00100u, 6}, 5);

        SECTION("level 0") {
            REQUIRE(*trie.match_exact(Bits{0u, 4}) == 0);
            REQUIRE(*trie.match_exact(Bits{1u, 4}) == 1);
            REQUIRE(*trie.match_exact(Bits{2u, 4}) == 2);
        }

        SECTION("level 1") {
            REQUIRE(*trie.match_exact(Bits{0b0000'00001u, 6}) == 3);
            REQUIRE(*trie.match_exact(Bits{0b0000'00010u, 6}) == 4);
            REQUIRE(*trie.match_exact(Bits{0b0000'00100u, 6}) == 5);
        }
    }

    SECTION("negative basic") {
        trie.insert(Bits{0u, 4}, 0);
        REQUIRE(trie.match_exact(Bits{0u, 5}) == std::nullopt);
        REQUIRE(trie.match_exact(Bits{1u, 4}) == std::nullopt);
    }
}

TEST_CASE("Match longest prefixes", "[ByeTrie][match_longest]", ) {
    bye_trie::ByeTrie<uint32_t, long> trie;
    trie.insert(Bits{0b0000u, 4}, 0);
    trie.insert(Bits{0b001u, 3}, 1);
    trie.insert(Bits{0b0000'00001u, 6}, 2);

    SECTION("positive") {
        SECTION("exact") {
            auto const [len, value] = *trie.match_longest(Bits{0b10000u, 5});
            REQUIRE(len == 4);
            REQUIRE(value == 0);
        }

        SECTION("4 longest bits, the same level") {
            auto const [len, value] = *trie.match_longest(Bits{0b00000u, 5});
            REQUIRE(len == 4);
            REQUIRE(value == 0);
        }

        SECTION("3 longest bits, previous level") {
            auto const [len, value] = *trie.match_longest(Bits{0b00'10001u, 7});
            REQUIRE(len == 3);
            REQUIRE(value == 1);
        }

        SECTION("6 longest bits, the same level") {
            auto const [len, value] = *trie.match_longest(Bits{0b10'00001u, 7});
            REQUIRE(len == 6);
            REQUIRE(value == 2);
        }
    }

    SECTION("negative basic") {
        REQUIRE(!trie.match_longest(Bits{0b00010u, 5}));
        REQUIRE(!trie.match_longest(Bits{0b11000u, 5}));
    }
}

TEST_CASE("Erase values", "[ByeTrie][erase_exact]") {
    SECTION("Not found") {
        bye_trie::ByeTrie<uint32_t, long> trie;
        REQUIRE(!trie.erase_exact(Bits{0u, 5}));
        REQUIRE(!trie.erase_exact(Bits{0u, 4}));
    }
    SECTION("No unfold-cleaning") {
        bye_trie::ByeTrie<uint32_t, long> trie;
        trie.insert(Bits{0b0'00000'00000u, 11}, 0);
        trie.insert(Bits{0b1'00000'00000u, 11}, 1);
        REQUIRE(trie.erase_exact(Bits{0b0'00000'00000u, 11}));
        REQUIRE(trie.size() == 1);
        REQUIRE(*trie.match_exact(Bits{0b1'00000'00000u, 11}) == 1);
    }
    SECTION("Unfold-cleaning just the leaf which contains the value") {
        bye_trie::ByeTrie<uint32_t, long> trie;
        trie.insert(Bits{0b0'00000'00000u, 11}, 0);
        trie.insert(Bits{0b0'00000u, 6}, 1);
        REQUIRE(trie.erase_exact(Bits{0b0'00000'00000u, 11}));
        REQUIRE(trie.size() == 1);
        REQUIRE(*trie.match_exact(Bits{0b0'00000u, 6}) == 1);
    }
    SECTION("bug case of confusion of external bitmap index in unfold-cleaning") {
        bye_trie::ByeTrie<uint32_t, long> trie;
        trie.insert(Bits{0b0'00001'00000u, 11}, 0);
        trie.insert(Bits{0b0'00000u, 6}, 1);
        REQUIRE(trie.erase_exact(Bits{0b0'00001'00000u, 11}));
        REQUIRE(trie.size() == 1);
        REQUIRE(*trie.match_exact(Bits{0b0'00000u, 6}) == 1);
    }
    SECTION("Unfold-cleaning the branch up to the root") {
        bye_trie::ByeTrie<uint32_t, long> trie;
        trie.insert(Bits{0b0'00000'00000u, 11}, 0);
        REQUIRE(trie.erase_exact(Bits{0b0'00000'00000u, 11}));
        REQUIRE(trie.size() == 0);
    }
    SECTION("Unfold-cleaning the branch in case there is just root node") {
        bye_trie::ByeTrie<uint32_t, long> trie;
        trie.insert(Bits{0b0001u, 4}, 0);
        REQUIRE(trie.erase_exact(Bits{0b0001u, 4}));
        REQUIRE(trie.size() == 0);
    }
    SECTION("node vec index is not equal to stride_m_1") {
        bye_trie::ByeTrie<uint32_t, long> trie;
        trie.insert(Bits{1u, 2}, 0);
        trie.insert(Bits{2u, 2}, 1);
        trie.erase_exact(Bits{2u, 2});
        REQUIRE(trie.size() == 1);
        REQUIRE(trie.match_exact(Bits{1u, 2}) == 0);
    }
}

TEST_CASE("", "[RecyclingStack]") {
    SECTION("useless") {
        std::array<detail::ErasedNode, 1> storage;
        detail::RecyclingStack stack;
        stack.recycle(std::span(storage));
        int i = 0;
        stack.for_each_useless([&storage, &i](auto blk) {
            REQUIRE(blk == MemBlk{storage.data(), 16});
            i += 1;
        });
        REQUIRE(i == 1);
    }
    SECTION("free") {
        std::array<detail::ErasedNode, 2> storage;
        detail::RecyclingStack stack;
        stack.recycle(std::span(storage));
        int i = 0;
        stack.for_each_free([&storage, &i](auto blk) {
            REQUIRE(blk == MemBlk{storage.data(), 32});
            i += 1;
        });
        REQUIRE(i == 1);
    }
    SECTION("push then pop on resident memory") {
        detail::RecyclingStack stack;
        for (auto i = 0u; i < 32; ++i) {
            stack.push(detail::Node{detail::InternalBitmap{i}, {}, nullptr});
        }
        for (auto i = 32u; i != 0; --i) {
            REQUIRE(stack.pop().internal_bitmap.get_inner() == i - 1);
        }
        REQUIRE(stack.empty());
    }
    SECTION("push then pop on resident memory") {
        detail::RecyclingStack stack;
        std::array<detail::ErasedNode, 2> storage;
        stack.recycle(std::span(storage));
        for (auto i = 0u; i < 33; ++i) {
            stack.push(detail::Node{detail::InternalBitmap{i}, {}, nullptr});
        }
        for (auto i = 33u; i != 0; --i) {
            REQUIRE(stack.pop().internal_bitmap.get_inner() == i - 1);
        }
        REQUIRE(stack.empty());
        int i = 0;
        stack.for_each_free([&storage, &i](auto blk) {
            REQUIRE(blk == MemBlk{storage.data(), 32});
            i += 1;
        });
        REQUIRE(i == 1);
    }
}

TEST_CASE("Exception guarantee", "[ByeTrie][insert]") {
    struct Alloc {
        MemBlk realloc(MemBlk blk, size_t size) noexcept(false) {
            if (tickets-- == 0) {
                throw std::bad_alloc();
            } else {
                return MemBlk{std::realloc(blk.ptr, size), size};
            }
        }

        void dealloc(MemBlk blk) noexcept {
            std::free(blk.ptr);
        }

        uint32_t tickets = 0;
    };

    SECTION("useless branches get freed") {
        ByeTrie<uint32_t, long, Alloc> trie(Alloc{2});
        REQUIRE_THROWS_AS(trie.insert(Bits{0b0'00000'00000u, 11}, 0), std::bad_alloc);
    }

    SECTION("can insert on a useless branch") {
        ByeTrie<uint32_t, long, Alloc> trie(Alloc{2});
        REQUIRE_THROWS_AS(trie.insert(Bits{0b0'00000'00000u, 11}, 0), std::bad_alloc);
        REQUIRE(trie.insert(Bits{0b0'00000'00000u, 11}, 0) == std::nullopt);
        REQUIRE(trie.match_exact(Bits{0b0'00000'00000u, 11}) == 0);
    }

    SECTION("try overflow RecyclingVec") {
        ByeTrie<uint32_t, long, Alloc> trie(Alloc{});
        for (auto i = 0u; i < 32; ++i) {
            trie.alloc().tickets = 6;
            REQUIRE_THROWS_AS(trie.insert(Bits{i, 32}, 0), std::bad_alloc);
        }
        for (auto i = 0u; i < 32; ++i) {
            trie.insert(Bits{i << 5, 27}, 0);
        }
    }
}

TEST_CASE("Iteration", "[ByeTrie]") {
    using ByeTrie = ByeTrie<uint32_t, long>;
    using Value = ByeTrie::ValueType;
    ByeTrie trie;

    SECTION("0/0 exists, begin() doesn't seek the first prefix") {
        trie.insert(Bits{0u, 0}, 1);
        REQUIRE((*trie.begin() == Value{Bits{0u, 0}, 1}));
    }

    SECTION("0/0 doesn't exist, begin() seeks the first prefix") {
        trie.insert(Bits{0u, 1}, 1);
        REQUIRE((*trie.begin() == Value{Bits{0u, 1}, 1}));
    }

    SECTION("empty ByeTrie, begin() == end()") {
        REQUIRE((trie.begin() == trie.end()));
    }

    SECTION("not empty, begin() != end()") {
        trie.insert(Bits{0u, 1}, 1);
        REQUIRE((trie.begin() != trie.end()));
    }

    SECTION("increment reaches next element") {
        trie.insert(Bits{0u, 0}, 1);
        trie.insert(Bits{0u, 1}, 2);
        REQUIRE((*++trie.begin() == Value{Bits{0u, 1}, 2}));
    }

    SECTION("increment reaches end") {
        trie.insert(Bits{0u, 0}, 1);
        REQUIRE(++trie.begin() == trie.end());
    }

    SECTION("iterate within node") {
        trie.insert(Bits{0u, 1}, 1);
        trie.insert(Bits{0u, 2}, 2);
        trie.insert(Bits{0u, 3}, 3);
        trie.insert(Bits{0u, 4}, 4);
        std::vector<Value> values;
        for (auto const x : trie) {
            values.push_back(x);
        }
        std::vector<Value> const expected{Value{Bits{0u, 1}, 1},
                                          Value{Bits{0u, 2}, 2},
                                          Value{Bits{0u, 3}, 3},
                                          Value{Bits{0u, 4}, 4}};
        REQUIRE(values == expected);
    }

    SECTION("node does not have prefixes, but the next node has") {
        trie.insert(Bits{0u, 5}, 1);
        trie.insert(Bits{0u, 6}, 2);
        REQUIRE((*trie.begin() == Value{Bits{0u, 5}, 1}));
        REQUIRE((*++trie.begin() == Value{Bits{0u, 6}, 2}));
        REQUIRE((++ ++trie.begin() == trie.end()));
    }

    SECTION("iterator comparison") {
        trie.insert(Bits{0xfffffff0u, 32}, 1);
        trie.insert(Bits{0xfffffff1u, 32}, 2);
        REQUIRE(++trie.begin() == ++trie.begin());
    }

    SECTION("iterate a subnet") {
        trie.insert(Bits{0x00ffffffu, 24}, 1);
        trie.insert(Bits{0x01ffffffu, 32}, 2);
        trie.insert(Bits{0x03ffffffu, 32}, 3);
        trie.insert(Bits{0x040fffffu, 32}, 4);
        auto it = trie.find_longest(Bits{0xffffffffu, 32});
        std::vector<Value> values;
        while (it != trie.end()) {
            values.push_back(*it);
            ++it;
        }
        std::vector<Value> const expected{Value{Bits{0x00ffffffu, 24}, 1},
                                          Value{Bits{0x01ffffffu, 32}, 2},
                                          Value{Bits{0x03ffffffu, 32}, 3}};
        REQUIRE(values == expected);
    }
}

TEST_CASE("Iterator interface", "[ByeTrie][find_exact][find_longest]") {
    using ByeTrie = ByeTrie<uint32_t, long>;
    using Value = ByeTrie::ValueType;
    ByeTrie trie;

    SECTION("find_exact") {
        SECTION("empty ByeTrie, find_exact() == end()") {
            REQUIRE((trie.find_exact(Bits{0u, 0}) == trie.end()));
        }

        SECTION("not empty, find_exact() != end()") {
            trie.insert(Bits{0u, 1}, 1);
            REQUIRE((trie.find_exact(Bits{0u, 1}) != trie.end()));
        }

        SECTION("match an element") {
            trie.insert(Bits{0u, 0}, 1);
            REQUIRE(trie.find_exact(Bits{0u, 0}) == trie.begin());
            REQUIRE(*trie.find_exact(Bits{0u, 0}) == Value{Bits{0u, 0}, 1});
        }

        SECTION("don't match an element") {
            trie.insert(Bits{0u, 0}, 1);
            REQUIRE(trie.find_exact(Bits{0u, 1}) == trie.end());
            REQUIRE(trie.find_exact(Bits{0u, 5}) == trie.end());
        }
    }

    SECTION("find_longest") {
        SECTION("empty ByeTrie, find_longest() == end()") {
            REQUIRE((trie.find_longest(Bits{0u, 0}) == trie.end()));
        }

        SECTION("not empty, find_longest() != end()") {
            trie.insert(Bits{0u, 1}, 1);
            REQUIRE((trie.find_longest(Bits{0u, 2}) != trie.end()));
        }

        SECTION("find an element") {
            trie.insert(Bits{1u, 1}, 1);
            REQUIRE(trie.find_longest(Bits{1u, 2}) == trie.begin());
            REQUIRE(*trie.find_longest(Bits{1u, 2}) == Value{Bits{1u, 1}, 1});
        }

        SECTION("don't find an element") {
            trie.insert(Bits{1u, 1}, 1);
            REQUIRE(trie.find_longest(Bits{0u, 1}) == trie.end());
        }
    }
}

TEST_CASE("Move assignment", "[ByeTrie]") {
    ByeTrie<uint32_t, long> trie;
    trie.insert(Bits{0u, 32}, 1);

    ByeTrie<uint32_t, long> trie2;
    trie2.insert(Bits{1u, 32}, 2);

    trie = std::move(trie2);
    REQUIRE(trie.match_exact(Bits{1u, 32}) == 2);
}

TEST_CASE(
        "Call every function of the interface with 128 bit prefix type just to ensure "
        "compilation",
        "[ByeTrie]") {
    using ByeTrie = ByeTrie<Uint128, long>;

    ByeTrie trie;
    trie.insert(Bits<Uint128>{0u, 0}, 1);
    trie.replace(Bits<Uint128>{0u, 0}, 1);
    trie.match_exact(Bits<Uint128>{0u, 0});
    trie.match_longest(Bits<Uint128>{0u, 0});
    trie.find_longest(Bits<Uint128>{0u, 0});
    trie.begin();
    trie.end();
}

TEST_CASE("Initial array optimization", "[ByeTrie][Iar]") {
    using ByeTrie = ByeTrie<uint32_t, long, SystemAllocator, Iar16>;

    ByeTrie trie;
    trie.insert(Bits{0u, 16}, 1);
    REQUIRE(trie.size() == 1);
    REQUIRE(trie.match_exact(Bits{0u, 16}) == 1);
    REQUIRE(trie.match_longest(Bits{0u, 16}) == std::pair{uint8_t(16), 1L});
    trie.replace(Bits{0u, 16}, 2);
    REQUIRE(trie.match_exact(Bits{0u, 16}) == 2);
    trie.insert(Bits{0u, 24}, 3);
    REQUIRE(trie.match_exact(Bits{0u, 24}) == 3);
    REQUIRE(trie.match_exact(Bits{1u, 24}) == std::nullopt);
}
