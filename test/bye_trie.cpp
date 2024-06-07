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
    SECTION("6") {
        detail::ExternalBitmap<6> bitmap(0b110);
        REQUIRE(!bitmap.exists(Bits{0, 6}));
        REQUIRE(bitmap.exists(Bits{1, 6}));
        REQUIRE(bitmap.before(Bits{0, 6}) == 0);
        REQUIRE(bitmap.before(Bits{2, 6}) == 1);
    }

    SECTION("5") {
        detail::ExternalBitmap<5> bitmap(0b110);
        REQUIRE(!bitmap.exists(Bits{0, 5}));
        REQUIRE(bitmap.exists(Bits{1, 5}));
        REQUIRE(bitmap.before(Bits{0, 5}) == 0);
        REQUIRE(bitmap.before(Bits{1, 5}) == 0);
        REQUIRE(bitmap.before(Bits{2, 5}) == 1);
        REQUIRE(bitmap.before(Bits{3, 5}) == 2);
        REQUIRE(bitmap.before(Bits{4, 5}) == 2);
    }
}

TEST_CASE("", "[InternalBitmap][set][unset][exists]") {
    uint8_t idx;

    SECTION("7") {
        detail::InternalBitmap<7> bitmap(
                0b0000000000000000000000000000000000000000000000000000000000000001'00000000000000000000000000000000'0000000000000000'00000000'0000'00'0);
        REQUIRE(!bitmap.exists(idx, Bits{3, 6}));
        bitmap.set(Bits{3, 6});
        REQUIRE(bitmap.exists(idx, Bits{3, 6}));
        REQUIRE(idx == 1);
        bitmap.unset(Bits{3, 6});
        REQUIRE(!bitmap.exists(idx, Bits{3, 6}));
    }

    SECTION("6") {
        detail::InternalBitmap<6> bitmap(
                0b00000000000000000000000000000001'0000000000000000'00000000'0000'00'0);
        REQUIRE(!bitmap.exists(idx, Bits{3, 5}));
        bitmap.set(Bits{3, 5});
        REQUIRE(bitmap.exists(idx, Bits{3, 5}));
        REQUIRE(idx == 1);
        bitmap.unset(Bits{3, 5});
        REQUIRE(!bitmap.exists(idx, Bits{3, 5}));
    }

    SECTION("5") {
        detail::InternalBitmap<5> bitmap(0b0'1000000000001010'10000010'1001'10'1);
        SECTION("4 length") {
            REQUIRE(!bitmap.exists(idx, Bits{14, 4}));
            bitmap.set(Bits{14, 4});
            REQUIRE(bitmap.exists(idx, Bits{14, 4}));
            REQUIRE(idx == 8);
            bitmap.unset(Bits{14, 4});
            REQUIRE(!bitmap.exists(idx, Bits{14, 4}));
        }

        SECTION("3 length") {
            REQUIRE(!bitmap.exists(idx, Bits{6, 3}));
            bitmap.set(Bits{6, 3});
            REQUIRE(bitmap.exists(idx, Bits{6, 3}));
            REQUIRE(idx == 5);
            bitmap.unset(Bits{6, 3});
            REQUIRE(!bitmap.exists(idx, Bits{6, 3}));
        }

        SECTION("2 length") {
            REQUIRE(!bitmap.exists(idx, Bits{2, 2}));
            bitmap.set(Bits{2, 2});
            REQUIRE(bitmap.exists(idx, Bits{2, 2}));
            REQUIRE(idx == 3);
            bitmap.unset(Bits{2, 2});
            REQUIRE(!bitmap.exists(idx, Bits{2, 2}));
        }

        SECTION("1 length") {
            REQUIRE(!bitmap.exists(idx, Bits{0, 1}));
            bitmap.set(Bits{0, 1});
            REQUIRE(bitmap.exists(idx, Bits{0, 1}));
            REQUIRE(idx == 1);
            bitmap.unset(Bits{0, 1});
            REQUIRE(!bitmap.exists(idx, Bits{0, 1}));
        }

        SECTION("0 length") {
            REQUIRE(bitmap.exists(idx, Bits{0, 0}));
            bitmap.unset(Bits{0, 0});
            REQUIRE(!bitmap.exists(idx, Bits{0, 0}));
            bitmap.set(Bits{0, 0});
            REQUIRE(bitmap.exists(idx, Bits{0, 0}));
            REQUIRE(idx == 0);
        }
    }
}

TEST_CASE("", "[InternalBitmap][longest_before]") {
    uint8_t idx;

    SECTION("6") {
        detail::InternalBitmap<6> bitmap(
                0b10000000000000000000000000000010'0000000000001000'00000000'0000'00'0);
        SECTION("5") {
            SECTION("match") {
                REQUIRE(bitmap.find_longest(idx, Bits{0b11111u, 5}).value() == 5);
                REQUIRE(idx == 2);
                REQUIRE(bitmap.find_longest(idx, Bits{0b1, 5}).value() == 5);
                REQUIRE(idx == 1);
            }
            SECTION("longest") {
                REQUIRE(bitmap.find_longest(idx, Bits{0b011, 5}).value() == 4);
                REQUIRE(idx == 0);
            }
        }
    }

    SECTION("5") {
        detail::InternalBitmap<5> bitmap(0b0'1000000000001010'10000010'1001'10'1);
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
}

template <uint8_t N>
class MallocResource {
public:
    MallocResource(detail::NodeVec<N>* vec)
            : vec(vec) {
    }

    ~MallocResource() noexcept {
        alloc.dealloc(MemBlk{vec->data(), 0});
    }

    SystemAllocator alloc;

private:
    detail::NodeVec<N>* vec;
};

using Ns = std::tuple<std::integral_constant<uint8_t, 3>,
                      std::integral_constant<uint8_t, 4>,
                      std::integral_constant<uint8_t, 5>,
                      std::integral_constant<uint8_t, 6>,
                      std::integral_constant<uint8_t, 7>>;

TEMPLATE_LIST_TEST_CASE("Branch manipulation", "[NodeVec][with_new_branch]", Ns) {
    constexpr auto N = TestType{};
    detail::NodeVec<N> vec{nullptr, 0, 0};
    MallocResource guard{&vec};
    std::array<detail::ErasedNode<N>, 3> fake;
    SECTION("insert the first branch") {
        vec.insert_branch(0, detail::Node<N>{{}, {}, &fake[0]}, guard.alloc);
        REQUIRE(vec.branches().size() == 1);
        REQUIRE(vec.branches()[0].node.children == &fake[0]);

        SECTION("insert a branch before") {
            vec.insert_branch(0, detail::Node<N>{{}, {}, &fake[1]}, guard.alloc);
            REQUIRE(vec.branches().size() == 2);
            REQUIRE(vec.branches()[0].node.children == &fake[1]);
            REQUIRE(vec.branches()[1].node.children == &fake[0]);
        }

        SECTION("insert a branch after") {
            vec.insert_branch(1, detail::Node<N>{{}, {}, &fake[1]}, guard.alloc);
            REQUIRE(vec.branches().size() == 2);
            REQUIRE(vec.branches()[0].node.children == &fake[0]);
            REQUIRE(vec.branches()[1].node.children == &fake[1]);
        }

        SECTION("insert a branch between") {
            vec.insert_branch(1, detail::Node<N>{{}, {}, &fake[1]}, guard.alloc);
            vec.insert_branch(1, detail::Node<N>{{}, {}, &fake[2]}, guard.alloc);
            REQUIRE(vec.branches().size() == 3);
            REQUIRE(vec.branches()[0].node.children == &fake[0]);
            REQUIRE(vec.branches()[1].node.children == &fake[2]);
            REQUIRE(vec.branches()[2].node.children == &fake[1]);
        }
    }
}

TEMPLATE_LIST_TEST_CASE("Erase value", "[NodeVec][erase_value]", Ns) {
    constexpr auto N = TestType{};
    detail::NodeVec<N> vec{nullptr, 0, 0};
    MallocResource guard{&vec};
    std::array<detail::ErasedNode<N>, 3> fake;
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

TEMPLATE_LIST_TEST_CASE("Erase branch", "[NodeVec][erase_branch]", Ns) {
    constexpr auto N = TestType{};
    detail::NodeVec<N> vec{nullptr, 0, 0};
    MallocResource guard{&vec};
    std::array<detail::ErasedNode<N>, 3> fake;
    vec.insert_branch(0, detail::Node<N>{{}, {}, &fake[0]}, guard.alloc);
    vec.insert_branch(1, detail::Node<N>{{}, {}, &fake[1]}, guard.alloc);
    vec.insert_branch(2, detail::Node<N>{{}, {}, &fake[2]}, guard.alloc);
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

TEMPLATE_LIST_TEST_CASE("Insert values", "[ByeTrie][insert]", Ns) {
    bye_trie::ByeTrie<uint32_t, long, SystemAllocator, TestType{}> trie;

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

TEMPLATE_LIST_TEST_CASE("", "[ByeTrie][insert_ref]", Ns) {
    bye_trie::ByeTrie<uint32_t, long> trie;

    SECTION("basic") {
        auto x = trie.insert_ref(Bits{0u, 4}, 0);
        REQUIRE(x.second);
        REQUIRE(*x.first == 0);

        *x.first = 1;
        REQUIRE(*trie.match_exact(Bits{0u, 4}) == 1);

        x = trie.insert_ref(Bits{0u, 4}, 2);
        REQUIRE(!x.second);
        REQUIRE(*x.first == 1);

        *x.first = 3;
        REQUIRE(*trie.match_exact(Bits{0u, 4}) == 3);
    }
}

TEMPLATE_LIST_TEST_CASE("", "[ByeTrie][replace]", Ns) {
    bye_trie::ByeTrie<uint32_t, long, SystemAllocator, TestType{}> trie;
    REQUIRE(trie.replace(Bits{0b0'00001u, 6}, 1) == std::nullopt);
    REQUIRE(trie.replace(Bits{0b0'00001u, 6}, 2) == 1);
    REQUIRE(trie.replace(Bits{0b0'00001u, 6}, 3) == 2);
}

TEMPLATE_LIST_TEST_CASE("Match exact prefixes", "[ByeTrie][match_exact]", Ns) {
    bye_trie::ByeTrie<uint32_t, long, SystemAllocator, TestType{}> trie;

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

TEST_CASE("", "[ByeTrie][match_exact_ref]") {
    bye_trie::ByeTrie<uint32_t, long> trie;

    SECTION("basic") {
        trie.insert(Bits{0u, 4}, 0);
        *trie.match_exact_ref(Bits{0u, 4}) = 1;
        REQUIRE(*trie.match_exact(Bits{0u, 4}) == 1);
    }
}

TEMPLATE_LIST_TEST_CASE("", "[ByeTrie][match_longest]", Ns) {
    bye_trie::ByeTrie<uint32_t, long, SystemAllocator, TestType{}> trie;
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

TEST_CASE("", "[ByeTrie][match_longest_ref]") {
    bye_trie::ByeTrie<uint32_t, long> trie;

    SECTION("basic") {
        trie.insert(Bits{0u, 4}, 0);
        *trie.match_longest_ref(Bits{0u, 5})->second = 1;
        REQUIRE(trie.match_longest(Bits{0u, 5})->second == 1);
    }
}

TEMPLATE_LIST_TEST_CASE("Erase values", "[ByeTrie][erase_exact]", Ns) {
    constexpr auto N = TestType{};
    SECTION("Not found") {
        bye_trie::ByeTrie<uint32_t, long, SystemAllocator, N> trie;
        REQUIRE(!trie.erase_exact(Bits{0u, 5}));
        REQUIRE(!trie.erase_exact(Bits{0u, 4}));
    }
    SECTION("No unfold-cleaning") {
        bye_trie::ByeTrie<uint32_t, long, SystemAllocator, N> trie;
        trie.insert(Bits{0b0'00000'00000u, 11}, 0);
        trie.insert(Bits{0b1'00000'00000u, 11}, 1);
        REQUIRE(trie.erase_exact(Bits{0b0'00000'00000u, 11}));
        REQUIRE(trie.size() == 1);
        REQUIRE(*trie.match_exact(Bits{0b1'00000'00000u, 11}) == 1);
    }
    SECTION("Unfold-cleaning just the leaf which contains the value") {
        bye_trie::ByeTrie<uint32_t, long, SystemAllocator, N> trie;
        trie.insert(Bits{0b0'00000'00000u, 11}, 0);
        trie.insert(Bits{0b0'00000u, 6}, 1);
        REQUIRE(trie.erase_exact(Bits{0b0'00000'00000u, 11}));
        REQUIRE(trie.size() == 1);
        REQUIRE(*trie.match_exact(Bits{0b0'00000u, 6}) == 1);
    }
    SECTION("Bug case of confusion of external bitmap index in unfold-cleaning") {
        bye_trie::ByeTrie<uint32_t, long, SystemAllocator, N> trie;
        trie.insert(Bits{0b0'00001'00000u, 11}, 0);
        trie.insert(Bits{0b0'00000u, 6}, 1);
        REQUIRE(trie.erase_exact(Bits{0b0'00001'00000u, 11}));
        REQUIRE(trie.size() == 1);
        REQUIRE(*trie.match_exact(Bits{0b0'00000u, 6}) == 1);
    }
    SECTION("Unfold-cleaning the branch up to the root") {
        bye_trie::ByeTrie<uint32_t, long, SystemAllocator, N> trie;
        trie.insert(Bits{0b0'00000'00000u, 11}, 0);
        REQUIRE(trie.erase_exact(Bits{0b0'00000'00000u, 11}));
        REQUIRE(trie.size() == 0);
    }
    SECTION("Unfold-cleaning the branch in case there is just root node") {
        bye_trie::ByeTrie<uint32_t, long, SystemAllocator, N> trie;
        trie.insert(Bits{0b0001u, 4}, 0);
        REQUIRE(trie.erase_exact(Bits{0b0001u, 4}));
        REQUIRE(trie.size() == 0);
    }
    SECTION("Node vec index is not equal to stride_m_1") {
        bye_trie::ByeTrie<uint32_t, long, SystemAllocator, N> trie;
        trie.insert(Bits{1u, 2}, 0);
        trie.insert(Bits{2u, 2}, 1);
        trie.erase_exact(Bits{2u, 2});
        REQUIRE(trie.size() == 1);
        REQUIRE(trie.match_exact(Bits{1u, 2}) == 0);
    }
}

TEMPLATE_LIST_TEST_CASE("", "[RecyclingStack]", Ns) {
    constexpr auto N = TestType::value;

    SECTION("useless") {
        std::array<detail::ErasedNode<TestType{}>, 1> storage;
        detail::RecyclingStack<N> stack;
        stack.recycle(std::span(storage));
        int i = 0;
        stack.for_each_useless([&storage, &i](auto blk) {
            REQUIRE(blk == MemBlk{storage.data(), sizeof(detail::Node<N>)});
            i += 1;
        });
        REQUIRE(i == 1);
    }
    SECTION("free") {
        std::array<detail::ErasedNode<N>, 2> storage;
        detail::RecyclingStack<N> stack;
        stack.recycle(std::span(storage));
        int i = 0;
        stack.for_each_free([&storage, &i](auto blk) {
            REQUIRE(blk == MemBlk{storage.data(), sizeof(detail::Node<N>) * 2});
            i += 1;
        });
        REQUIRE(i == 1);
    }
    SECTION("push then pop on resident memory") {
        detail::RecyclingStack<N> stack;
        for (auto i = 0u; i < detail::Stride<N>::external_bitmap_index_count; ++i) {
            stack.push(detail::Node<N>{detail::InternalBitmap<N>{i}, {}, nullptr});
        }
        for (auto i = detail::Stride<N>::external_bitmap_index_count; i != 0; --i) {
            REQUIRE(stack.pop().internal_bitmap.get_inner() == i - 1);
        }
        REQUIRE(stack.empty());
    }
    SECTION("push then pop on resident memory") {
        detail::RecyclingStack<N> stack;
        std::array<detail::ErasedNode<N>, 2> storage;
        stack.recycle(std::span(storage));
        for (auto i = 0u; i < detail::Stride<N>::external_bitmap_index_count + 1; ++i) {
            stack.push(detail::Node<N>{detail::InternalBitmap<N>{i}, {}, nullptr});
        }
        for (auto i = detail::Stride<N>::external_bitmap_index_count + 1; i != 0; --i) {
            REQUIRE(stack.pop().internal_bitmap.get_inner() == i - 1);
        }
        REQUIRE(stack.empty());
        int i = 0;
        stack.for_each_free([&storage, &i](auto blk) {
            REQUIRE(blk == MemBlk{storage.data(), sizeof(detail::Node<N>) * 2});
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

TEMPLATE_LIST_TEST_CASE("", "[ByeTrie][SubsIterator]", Ns) {
    using ByeTrie = ByeTrie<uint32_t, long, SystemAllocator, TestType{}>;

    ByeTrie trie;

    SECTION("0/0 exists, begin() doesn't seek the first prefix") {
        trie.insert(Bits{0u, 0}, 1);
        REQUIRE(trie.subs(Bits{0u, 0}).begin().key() == Bits{0u, 0});
        REQUIRE(*trie.subs(Bits{0u, 0}).begin() == 1);
    }

    SECTION("0/0 doesn't exist, begin() seeks the first prefix") {
        trie.insert(Bits{0u, 1}, 1);
        REQUIRE(trie.subs(Bits{0u, 0}).begin().key() == Bits{0u, 1});
        REQUIRE(*trie.subs(Bits{0u, 0}).begin() == 1);
    }

    SECTION("empty ByeTrie, begin() == end()") {
        auto const subs = trie.subs(Bits{0u, 0});
        REQUIRE(subs.begin() == subs.end());
    }

    SECTION("not empty, begin() != end()") {
        trie.insert(Bits{0u, 1}, 1);
        auto const subs = trie.subs(Bits{0u, 0});
        REQUIRE(subs.begin() != subs.end());
    }

    SECTION("increment reaches next element") {
        trie.insert(Bits{0u, 0}, 1);
        trie.insert(Bits{0u, 1}, 2);
        auto const subs = trie.subs(Bits{0u, 0});
        REQUIRE((++subs.begin()).key() == Bits{0u, 1});
        REQUIRE(*++subs.begin() == 2);
    }

    SECTION("increment reaches end") {
        trie.insert(Bits{0u, 0}, 1);
        auto const subs = trie.subs(Bits{0u, 0});
        REQUIRE(++subs.begin() == subs.end());
    }

    SECTION("iterate within node") {
        trie.insert(Bits{0u, 1}, 1);
        trie.insert(Bits{0u, 2}, 2);
        trie.insert(Bits{0u, 3}, 3);
        trie.insert(Bits{0u, 4}, 4);
        std::vector<std::pair<Bits<unsigned>, long>> values;
        auto const subs = trie.subs(Bits{0u, 0});
        for (auto it = subs.begin(); it != subs.end(); ++it) {
            values.emplace_back(it.key(), *it);
        }
        std::vector<std::pair<Bits<unsigned>, long>> const expected{
                std::pair{Bits{0u, 1}, 1},
                std::pair{Bits{0u, 2}, 2},
                std::pair{Bits{0u, 3}, 3},
                std::pair{Bits{0u, 4}, 4}};
        REQUIRE(values == expected);
    }

    SECTION("node does not have prefixes, but the next node has") {
        trie.insert(Bits{0u, 5}, 1);
        trie.insert(Bits{0u, 6}, 2);
        auto const subs = trie.subs(Bits{0u, 0});
        REQUIRE((subs.begin().key() == Bits{0u, 5}));
        REQUIRE((*subs.begin() == 1));
        REQUIRE(((++subs.begin()).key() == Bits{0u, 6}));
        REQUIRE((*++subs.begin() == 2));
        REQUIRE((++ ++subs.begin() == subs.end()));
    }

    SECTION("iterator comparison") {
        trie.insert(Bits{0xfffffff0u, 32}, 1);
        trie.insert(Bits{0xfffffff1u, 32}, 2);
        auto const subs = trie.subs(Bits{0u, 0});
        REQUIRE(++subs.begin() == ++subs.begin());
    }

    SECTION("iterate a subnet") {
        trie.insert(Bits{0x00ffffffu, 24}, 1);
        trie.insert(Bits{0x01ffffffu, 32}, 2);
        trie.insert(Bits{0x03ffffffu, 32}, 3);
        trie.insert(Bits{0x040fffffu, 32}, 4);
        auto const subs = trie.subs(Bits{0x00ffffffu, 24});
        std::vector<std::pair<Bits<unsigned>, long>> values;
        for (auto it = subs.begin(); it != subs.end(); ++it) {
            values.emplace_back(it.key(), *it);
        }
        std::vector<std::pair<Bits<unsigned>, long>> const expected{
                {Bits{0x00ffffffu, 24}, 1},
                {Bits{0x01ffffffu, 32}, 2},
                {Bits{0x03ffffffu, 32}, 3}};
        REQUIRE(values == expected);
    }

    SECTION("zero net") {
        trie.insert(Bits{0x00000000u, 0}, 1);
        trie.insert(Bits{0x01ffffffu, 32}, 2);
        trie.insert(Bits{0x03ffffffu, 32}, 3);
        trie.insert(Bits{0x040fffffu, 32}, 4);
        auto const subs = trie.subs(Bits{0x00000000u, 0});
        std::vector<std::pair<Bits<unsigned>, long>> values;
        for (auto it = subs.begin(); it != subs.end(); ++it) {
            values.emplace_back(it.key(), *it);
        }
        std::vector<std::pair<Bits<unsigned>, long>> const expected{
                {Bits{0x00000000u, 0}, 1},
                {Bits{0x040fffffu, 32}, 4},
                {Bits{0x01ffffffu, 32}, 2},
                {Bits{0x03ffffffu, 32}, 3},
        };
        REQUIRE(values == expected);
    }

    SECTION("zero net doesn't exist") {
        trie.insert(Bits{0x01ffffffu, 32}, 2);
        trie.insert(Bits{0x03ffffffu, 32}, 3);
        trie.insert(Bits{0x040fffffu, 32}, 4);
        auto const subs = trie.subs(Bits{0x00000000u, 0});
        std::vector<std::pair<Bits<unsigned>, long>> values;
        for (auto it = subs.begin(); it != subs.end(); ++it) {
            values.emplace_back(it.key(), *it);
        }
        std::vector<std::pair<Bits<unsigned>, long>> const expected{
                {Bits{0x040fffffu, 32}, 4},
                {Bits{0x01ffffffu, 32}, 2},
                {Bits{0x03ffffffu, 32}, 3},
        };
        REQUIRE(values == expected);
    }
}

TEMPLATE_LIST_TEST_CASE("", "[ByeTrie][ByeTrieIterator]", Ns) {
    using ByeTrie = ByeTrie<uint32_t, long, SystemAllocator, TestType{}>;

    ByeTrie trie;

    SECTION("empty") {
        REQUIRE((trie.begin() == trie.end()));
    }

    SECTION("one 0/0") {
        trie.insert(Bits{0u, 0}, 1);
        REQUIRE((trie.begin() != trie.end()));
        REQUIRE((trie.begin().key() == Bits{0u, 0}));
        REQUIRE(*trie.begin() == 1);
        REQUIRE(++trie.begin() == trie.end());
    }

    SECTION("iter node, then go to first child, iter it, then go to back and then to the "
            "second child") {
        trie.insert(Bits{0u, 0}, 1);
        trie.insert(Bits{11u, 2}, 2);
        trie.insert(Bits{000u, 3}, 3);
        trie.insert(Bits{001u, 3}, 4);

        std::vector<std::pair<Bits<unsigned>, long>> actual;
        for (auto it = trie.begin(); it != trie.end(); ++it) {
            actual.emplace_back(it.key(), *it);
        }
        std::vector<std::pair<Bits<unsigned>, long>> const expected{{Bits{0u, 0}, 1},
                                                                    {Bits{11u, 2}, 2},
                                                                    {Bits{000u, 3}, 3},
                                                                    {Bits{001u, 3}, 4}};
        REQUIRE(actual == expected);

        SECTION("supers") {
            trie.insert(Bits{0000u, 5}, 5);
            auto it = trie.match_longest_iter(Bits{0000u, 5});
            std::vector<std::pair<Bits<unsigned>, long>> range1;
            do {
                range1.emplace_back(it.key(), *it);
            } while (it.next_super());
            std::vector<std::pair<Bits<unsigned>, long>> const expected{
                    {Bits{0000u, 5}, 5}, {Bits{000u, 3}, 3}, {Bits{0u, 0}, 1}};
            REQUIRE(range1 == expected);
        }
    }
}

TEMPLATE_LIST_TEST_CASE("", "[ByeTrie][match_exact_iter]", Ns) {
    using ByeTrie = ByeTrie<uint32_t, long, SystemAllocator, TestType{}>;

    ByeTrie trie;

    trie.insert(Bits{0u, 0}, 1);
    trie.insert(Bits{11u, 2}, 2);
    trie.insert(Bits{000u, 3}, 3);
    trie.insert(Bits{001u, 3}, 4);

    SECTION("total ordering") {
        auto mid = trie.match_exact_iter(Bits{000u, 3});
        std::vector<std::pair<Bits<unsigned>, long>> range1;
        // todo: use subrange
        for (auto it = trie.begin(); it != mid; ++it) {
            range1.emplace_back(it.key(), *it);
        }
        REQUIRE(range1
                == (std::vector<std::pair<Bits<unsigned>, long>>{{Bits{0u, 0}, 1},
                                                                 {Bits{11u, 2}, 2}}));

        std::vector<std::pair<Bits<unsigned>, long>> range2;
        // todo: use subrange
        for (auto it = mid; it != trie.end(); ++it) {
            range2.emplace_back(it.key(), *it);
        }
        REQUIRE(range2
                == (std::vector<std::pair<Bits<unsigned>, long>>{{Bits{000u, 3}, 3},
                                                                 {Bits{001u, 3}, 4}}));
    }

    SECTION("no match") {
        REQUIRE(trie.match_exact_iter(Bits{0u, 1}) == trie.end());
    }
}

TEMPLATE_LIST_TEST_CASE("", "[ByeTrie][match_longest_iter]", Ns) {
    using ByeTrie = ByeTrie<uint32_t, long, SystemAllocator, TestType{}>;

    ByeTrie trie;

    trie.insert(Bits{0u, 0}, 1);
    trie.insert(Bits{11u, 2}, 2);
    trie.insert(Bits{000u, 3}, 3);
    trie.insert(Bits{001u, 3}, 4);
    trie.insert(Bits{0000u, 5}, 5);

    SECTION("total ordering") {
        auto mid = trie.match_longest_iter(Bits{0000u, 4});
        std::vector<std::pair<Bits<unsigned>, long>> range1;
        // todo: use subrange
        for (auto it = trie.begin(); it != mid; ++it) {
            range1.emplace_back(it.key(), *it);
        }
        REQUIRE(range1
                == (std::vector<std::pair<Bits<unsigned>, long>>{{Bits{0u, 0}, 1},
                                                                 {Bits{11u, 2}, 2}}));
        std::vector<std::pair<Bits<unsigned>, long>> range2;
        // todo: use subrange
        for (auto it = mid; it != trie.end(); ++it) {
            range2.emplace_back(it.key(), *it);
        }
        if constexpr (TestType{} == 3) {
            REQUIRE(range2
                    == (std::vector<std::pair<Bits<unsigned>, long>>{
                            {Bits{000u, 3}, 3},
                            {Bits{00000u, 5}, 5},
                            {Bits{001u, 3}, 4}}));
        } else {
            REQUIRE(range2
                    == (std::vector<std::pair<Bits<unsigned>, long>>{
                            {Bits{000u, 3}, 3},
                            {Bits{001u, 3}, 4},
                            {Bits{00000u, 5}, 5}}));
        }
    }

    SECTION("0/0 last resort") {
        auto it = trie.match_longest_iter(Bits{0u, 1});
        REQUIRE(it == trie.begin());
        REQUIRE(it.key() == Bits{0u, 0});
        REQUIRE(*it == 1);
    }

    SECTION("no match") {
        trie.erase_exact(Bits{0u, 0});
        REQUIRE(trie.match_longest_iter(Bits{1u, 1}) == trie.end());
    }
}

TEST_CASE("", "[ByeTrie][visit_supers]") {
    using ByeTrie = ByeTrie<uint32_t, long>;
    ByeTrie trie;
    trie.insert(Bits{0x00'00'00'00u, 0}, 0);
    trie.insert(Bits{0x00'00'00'01u, 1}, 1);
    trie.insert(Bits{0x00'00'00'02u, 2}, 2);
    trie.insert(Bits{0x00'00'01'02u, 10}, 3);
    trie.insert(Bits{0x00'00'02'02u, 10}, 4);
    std::vector<std::pair<Bits<unsigned>, long>> expected{{Bits{0x00'00'00'00u, 0}, 0},
                                                          {Bits{0x00'00'00'02u, 2}, 2},
                                                          {Bits{0x00'00'01'02u, 10}, 3}};
    decltype(expected) actual;
    trie.visit_supers(Bits{0x00'00'01'02u, 10},
                      [&actual](auto p, auto v) { actual.emplace_back(p, v); });
    REQUIRE(actual == expected);
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
    trie.subs(Bits<Uint128>{0u, 0});
    trie.visit_supers(Bits<Uint128>{0u, 0}, [](auto, auto) {});
}

TEST_CASE("Initial array optimization", "[ByeTrie][Iar]") {
    using ByeTrie = ByeTrie<uint32_t, long, SystemAllocator, 5, Iar16<5>>;

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

    int n = 0;
    trie.visit_supers(Bits{0u, 16}, [&n](auto p, auto v) {
        CHECK(p == Bits{0u, 16});
        CHECK(v == 2);
        ++n;
    });
    REQUIRE(n == 1);
}

TEST_CASE("", "[playground]") {
    using ByeTrie = ByeTrie<uint32_t, long, SystemAllocator, 3>;
    ByeTrie trie;
    trie.insert(Bits<uint32_t>{0u, 0}, 1);
    trie.replace(Bits<uint32_t>{0u, 0}, 1);
    trie.match_exact(Bits<uint32_t>{0u, 0});
    trie.match_longest(Bits<uint32_t>{0u, 0});
    trie.subs(Bits<uint32_t>{0u, 0});
}

TEMPLATE_LIST_TEST_CASE("Little objects", "[ByeTrie]", Ns) {
    ByeTrie<uint32_t, char, SystemAllocator, TestType{}> trie;

    SECTION("insert") {
        trie.insert(Bits{0u, 8}, 1);
        trie.insert(Bits{0u, 16}, 2);

        REQUIRE(*trie.match_exact(Bits{0u, 8}) == 1);
        REQUIRE(*trie.match_exact(Bits{0u, 16}) == 2);

        *trie.match_exact_ref(Bits{0u, 8}) = 3;
        REQUIRE(*trie.match_exact(Bits{0u, 8}) == 3);

        *trie.match_exact_ref(Bits{0u, 16}) = 4;
        REQUIRE(*trie.match_exact(Bits{0u, 16}) == 4);
    }
}