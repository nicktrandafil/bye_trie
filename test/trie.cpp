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

TEST_CASE("", "[Bits][concatenated]") {
    detail::Bits<uint32_t> slice(0b1100, 4);
    REQUIRE(slice.concatenated({0, 0}).value() == 0b1100);
    REQUIRE(static_cast<unsigned>(slice.concatenated({1, 1}).value()) == 0b11100);
}

TEST_CASE("", "[ExternalBitMap][exists][before]") {
    detail::ExternalBitMap bitmap(0b110);
    using detail::Bits;
    REQUIRE(!bitmap.exists(Bits{0, 5}));
    REQUIRE(bitmap.exists(Bits{1, 5}));
    REQUIRE(bitmap.before(Bits{0, 5}) == 0);
    REQUIRE(bitmap.before(Bits{1, 5}) == 0);
    REQUIRE(bitmap.before(Bits{2, 5}) == 1);
    REQUIRE(bitmap.before(Bits{3, 5}) == 2);
    REQUIRE(bitmap.before(Bits{4, 5}) == 2);
}

TEST_CASE("", "[InternalBitMap][set][unset][exists]") {
    detail::InternalBitMap bitmap(0b0'1000000000001010'10000010'1001'10'1);
    using detail::Bits;
    SECTION("4 length") {
        uint8_t idx;
        REQUIRE(!bitmap.exists(idx, detail::Bits{14, 4}));
        bitmap.set(Bits{14, 4});
        REQUIRE(bitmap.exists(idx, detail::Bits{14, 4}));
        REQUIRE(idx == 8);
        bitmap.unset(Bits{14, 4});
        REQUIRE(!bitmap.exists(idx, detail::Bits{14, 4}));
    }

    SECTION("3 length") {
        uint8_t idx;
        REQUIRE(!bitmap.exists(idx, detail::Bits{6, 3}));
        bitmap.set(Bits{6, 3});
        REQUIRE(bitmap.exists(idx, detail::Bits{6, 3}));
        REQUIRE(idx == 5);
        bitmap.unset(Bits{6, 3});
        REQUIRE(!bitmap.exists(idx, detail::Bits{6, 3}));
    }

    SECTION("2 length") {
        uint8_t idx;
        REQUIRE(!bitmap.exists(idx, detail::Bits{2, 2}));
        bitmap.set(Bits{2, 2});
        REQUIRE(bitmap.exists(idx, detail::Bits{2, 2}));
        REQUIRE(idx == 3);
        bitmap.unset(Bits{2, 2});
        REQUIRE(!bitmap.exists(idx, detail::Bits{2, 2}));
    }

    SECTION("1 length") {
        uint8_t idx;
        REQUIRE(!bitmap.exists(idx, detail::Bits{0, 1}));
        bitmap.set(Bits{0, 1});
        REQUIRE(bitmap.exists(idx, detail::Bits{0, 1}));
        REQUIRE(idx == 1);
        bitmap.unset(Bits{0, 1});
        REQUIRE(!bitmap.exists(idx, detail::Bits{0, 1}));
    }

    SECTION("0 length") {
        uint8_t idx;
        REQUIRE(bitmap.exists(idx, detail::Bits{0, 0}));
        bitmap.unset(Bits{0, 0});
        REQUIRE(!bitmap.exists(idx, detail::Bits{0, 0}));
        bitmap.set(Bits{0, 0});
        REQUIRE(bitmap.exists(idx, detail::Bits{0, 0}));
        REQUIRE(idx == 0);
    }
}

TEST_CASE("", "[InternalBitMap][longest_before]") {
    detail::InternalBitMap bitmap(0b0'1000000000001010'10000010'1001'10'1);
    uint8_t idx;
    using detail::Bits;

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
        alloc.dealloc(vec->data());
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
    vec.insert_branch(0, detail::Node{{}, {}, &fake[0]}, guard.alloc);
    vec.insert_branch(1, detail::Node{{}, {}, &fake[1]}, guard.alloc);
    vec.insert_branch(2, detail::Node{{}, {}, &fake[2]}, guard.alloc);
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
        everload_trie::Trie<uint32_t, long> trie;
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
        everload_trie::Trie<uint32_t, long> trie;
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

    SECTION("Longest") {
        everload_trie::Trie<uint32_t, long> trie;
        REQUIRE(trie.insert(0xffffffff, 32, 0) == std::nullopt);
        REQUIRE(trie.match_exact(0xffffffff, 32) == 0);
    }
}

TEST_CASE("", "[Trie][replace]") {
    everload_trie::Trie<uint32_t, long> trie;
    REQUIRE(trie.replace(0b0'00001, 6, 1) == std::nullopt);
    REQUIRE(trie.replace(0b0'00001, 6, 2) == 1);
    REQUIRE(trie.replace(0b0'00001, 6, 3) == 2);
}

TEST_CASE("Match exact prefixes", "[Trie][match_exact]") {
    everload_trie::Trie<uint32_t, long> trie;

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
    everload_trie::Trie<uint32_t, long> trie;
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
        everload_trie::Trie<uint32_t, long> trie;
        REQUIRE(!trie.erase_exact(0, 5));
        REQUIRE(!trie.erase_exact(0, 4));
    }
    SECTION("No unfold-cleaning") {
        everload_trie::Trie<uint32_t, long> trie;
        trie.insert(0b0'00000'00000, 11, 0);
        trie.insert(0b1'00000'00000, 11, 1);
        REQUIRE(trie.erase_exact(0b0'00000'00000, 11));
        REQUIRE(trie.size() == 1);
        REQUIRE(*trie.match_exact(0b1'00000'00000, 11) == 1);
    }
    SECTION("Unfold-cleaning just the leaf which contains the value") {
        everload_trie::Trie<uint32_t, long> trie;
        trie.insert(0b0'00000'00000, 11, 0);
        trie.insert(0b0'00000, 6, 1);
        REQUIRE(trie.erase_exact(0b0'00000'00000, 11));
        REQUIRE(trie.size() == 1);
        REQUIRE(*trie.match_exact(0b0'00000, 6) == 1);
    }
    SECTION("bug case of confusion of external bitmap index in unfold-cleaning") {
        everload_trie::Trie<uint32_t, long> trie;
        trie.insert(0b0'00001'00000, 11, 0);
        trie.insert(0b0'00000, 6, 1);
        REQUIRE(trie.erase_exact(0b0'00001'00000, 11));
        REQUIRE(trie.size() == 1);
        REQUIRE(*trie.match_exact(0b0'00000, 6) == 1);
    }
    SECTION("Unfold-cleaning the branch up to the root") {
        everload_trie::Trie<uint32_t, long> trie;
        trie.insert(0b0'00000'00000, 11, 0);
        REQUIRE(trie.erase_exact(0b0'00000'00000, 11));
        REQUIRE(trie.size() == 0);
    }
    SECTION("Unfold-cleaning the branch in case there is just root node") {
        everload_trie::Trie<uint32_t, long> trie;
        trie.insert(0b0001, 4, 0);
        REQUIRE(trie.erase_exact(0b0001, 4));
        REQUIRE(trie.size() == 0);
    }
    SECTION("node vec index is not equal to stride_m_1") {
        everload_trie::Trie<uint32_t, long> trie;
        trie.insert(1, 2, 0);
        trie.insert(2, 2, 1);
        trie.erase_exact(2, 2);
        REQUIRE(trie.size() == 1);
        REQUIRE(trie.match_exact(1, 2) == 0);
    }
}

TEST_CASE("", "[RecyclingStack]") {
    SECTION("useless") {
        std::array<detail::ErasedNode, 1> storage;
        detail::RecyclingStack stack;
        stack.recycle(std::span(storage));
        int i = 0;
        stack.for_each_useless([&storage, &i](auto ptr) {
            REQUIRE(ptr == storage.data());
            i += 1;
        });
        REQUIRE(i == 1);
    }
    SECTION("free") {
        std::array<detail::ErasedNode, 2> storage;
        detail::RecyclingStack stack;
        stack.recycle(std::span(storage));
        int i = 0;
        stack.for_each_free([&storage, &i](auto ptr) {
            REQUIRE(ptr == storage.data());
            i += 1;
        });
        REQUIRE(i == 1);
    }
    SECTION("push then pop on resident memory") {
        detail::RecyclingStack stack;
        for (auto i = 0u; i < 32; ++i) {
            stack.push(detail::Node{detail::InternalBitMap{i}, {}, nullptr});
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
            stack.push(detail::Node{detail::InternalBitMap{i}, {}, nullptr});
        }
        for (auto i = 33u; i != 0; --i) {
            REQUIRE(stack.pop().internal_bitmap.get_inner() == i - 1);
        }
        REQUIRE(stack.empty());
        int i = 0;
        stack.for_each_free([&storage, &i](auto ptr) {
            REQUIRE(ptr == storage.data());
            i += 1;
        });
        REQUIRE(i == 1);
    }
}

TEST_CASE("Exception guarantee", "[Trie][insert]") {
    struct Alloc {
        void* realloc(void* ptr, size_t size) noexcept(false) {
            if (tickets-- == 0) {
                throw std::bad_alloc();
            } else {
                return std::realloc(ptr, size);
            }
        }

        void dealloc(void* ptr) noexcept {
            std::free(ptr);
        }

        uint32_t tickets = 0;
    };

    SECTION("useless branches get freed") {
        Trie<uint32_t, long, Alloc> trie(Alloc{2});
        REQUIRE_THROWS_AS(trie.insert(0b0'00000'00000, 11, 0), std::bad_alloc);
    }

    SECTION("can insert on a useless branch") {
        Trie<uint32_t, long, Alloc> trie(Alloc{2});
        REQUIRE_THROWS_AS(trie.insert(0b0'00000'00000, 11, 0), std::bad_alloc);
        REQUIRE(trie.insert(0b0'00000'00000, 11, 0) == std::nullopt);
        REQUIRE(trie.match_exact(0b0'00000'00000, 11) == 0);
    }

    SECTION("try overflow RecyclingVec") {
        Trie<uint32_t, long, Alloc> trie(Alloc{});
        for (auto i = 0u; i < 32; ++i) {
            trie.alloc().tickets = 6;
            REQUIRE_THROWS_AS(trie.insert(i, 32, 0), std::bad_alloc);
        }
        for (auto i = 0u; i < 32; ++i) {
            trie.insert(i << 5, 27, 0);
        }
    }
}

TEST_CASE("Iteration", "[Trie]") {
    using Trie = Trie<uint32_t, long>;
    using Value = Trie::ValueType;
    Trie trie;

    SECTION("0/0 exists, begin() doesn't seek the first prefix") {
        trie.insert(0, 0, 1);
        REQUIRE((*trie.begin() == Value{0, 0, 1}));
    }

    SECTION("0/0 doesn't exist, begin() seeks the first prefix") {
        trie.insert(0, 1, 1);
        REQUIRE((*trie.begin() == Value{0, 1, 1}));
    }

    SECTION("empty Trie, begin() == end()") {
        REQUIRE((trie.begin() == trie.end()));
    }

    SECTION("not empty, begin() != end()") {
        trie.insert(0, 1, 1);
        REQUIRE((trie.begin() != trie.end()));
    }

    SECTION("increment reaches next element") {
        trie.insert(0, 0, 1);
        trie.insert(0, 1, 2);
        REQUIRE((*++trie.begin() == Value{0, 1, 2}));
    }

    SECTION("increment reaches end") {
        trie.insert(0, 0, 1);
        REQUIRE(++trie.begin() == trie.end());
    }

    SECTION("iterate within node") {
        trie.insert(0, 1, 1);
        trie.insert(0, 2, 2);
        trie.insert(0, 3, 3);
        trie.insert(0, 4, 4);
        std::vector<Value> values;
        for (auto const x : trie) {
            values.push_back(x);
        }
        std::vector<Value> const expected{
                Value{0, 1, 1}, Value{0, 2, 2}, Value{0, 3, 3}, Value{0, 4, 4}};
        REQUIRE(values == expected);
    }

    SECTION("node does not have prefixes, but the next node has") {
        trie.insert(0, 5, 1);
        trie.insert(0, 6, 2);
        REQUIRE((*trie.begin() == Value{0, 5, 1}));
        REQUIRE((*++trie.begin() == Value{0, 6, 2}));
        REQUIRE((++ ++trie.begin() == trie.end()));
    }

    SECTION("iterator comparison") {
        trie.insert(0xfffffff0, 32, 1);
        trie.insert(0xfffffff1, 32, 2);
        REQUIRE(++trie.begin() == ++trie.begin());
    }

    SECTION("iterate a subnet") {
        trie.insert(0x00ffffff, 24, 1);
        trie.insert(0x01ffffff, 32, 2);
        trie.insert(0x03ffffff, 32, 3);
        trie.insert(0x040fffff, 32, 4);
        auto it = trie.find_longest(0xffffffff, 32);
        std::vector<Value> values;
        while (it != trie.end()) {
            values.push_back(*it);
            ++it;
        }
        std::vector<Value> const expected{Value{0x00ffffff, 24, 1},
                                          Value{0x01ffffff, 32, 2},
                                          Value{0x03ffffff, 32, 3}};
        REQUIRE(values == expected);
    }
}

TEST_CASE("Iterator interface", "[Trie][find_exact][find_longest]") {
    using Trie = Trie<uint32_t, long>;
    using Value = Trie::ValueType;
    Trie trie;

    SECTION("find_exact") {
        SECTION("empty Trie, find_exact() == end()") {
            REQUIRE((trie.find_exact(0, 0) == trie.end()));
        }

        SECTION("not empty, find_exact() != end()") {
            trie.insert(0, 1, 1);
            REQUIRE((trie.find_exact(0, 1) != trie.end()));
        }

        SECTION("match an element") {
            trie.insert(0, 0, 1);
            REQUIRE(trie.find_exact(0, 0) == trie.begin());
            REQUIRE(*trie.find_exact(0, 0) == Value{0, 0, 1});
        }

        SECTION("don't match an element") {
            trie.insert(0, 0, 1);
            REQUIRE(trie.find_exact(0, 1) == trie.end());
        }
    }

    SECTION("find_longest") {
        SECTION("empty Trie, find_longest() == end()") {
            REQUIRE((trie.find_longest(0, 0) == trie.end()));
        }

        SECTION("not empty, find_longest() != end()") {
            trie.insert(0, 1, 1);
            REQUIRE((trie.find_longest(0, 2) != trie.end()));
        }

        SECTION("find an element") {
            trie.insert(1, 1, 1);
            REQUIRE(trie.find_longest(1, 2) == trie.begin());
            REQUIRE(*trie.find_longest(1, 2) == Value{1, 1, 1});
        }

        SECTION("don't find an element") {
            trie.insert(1, 1, 1);
            REQUIRE(trie.find_longest(0, 1) == trie.end());
        }
    }
}
