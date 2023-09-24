[![Build Status](https://github.com/nicktrandafil/bye_trie/actions/workflows/main_ci.yml/badge.svg?branch=master)](https://github.com/nicktrandafil/bye_trie/actions/workflows/main_ci.yml)
[![codecov](https://codecov.io/gh/nicktrandafil/bye_trie/branch/master/graph/badge.svg)](https://codecov.io/gh/nicktrandafil/bye_trie)
[![Documentation](https://img.shields.io/badge/docs-doxygen-blue.svg)](https://nicktrandafil.github.io/bye_trie)

# ByeTrie is bits trie data structure

ByeTrie is a trie data structure where keys are bit strings. It is based on the [Tree Bitmap : Hardware/Software IP Lookups with
Incremental Updates](https://cseweb.ucsd.edu/~varghese/PAPERS/ccr2004.pdf) paper by W. Eatherton, Z. Dittia, G. Varghese.

The goal of this implementation is to be space and time efficient as much as possible.

# Benchmarks

Internet's IPv4 prefixes and ASNs (about 893k) are used to benchmark times. The results are:

* peak memory consumption: 6MB
* average insert time: 72ns
* average match_longest time of 32bit prefixes: 25ns
* average match_exact time of 32bit prefixes: 9ns

The trie is filled with all prefixes up to length 23. Then on top of that 10M more 24 bit
prefixes inserted. Then 10M prefixes inserted and searched. The results are:

* average insert throughput of 32bit prefixes: 6MB/s
* average insert throughput of 32bit prefixes with IAR16 optimization: 8MB/s
* average match_longest throughput of 32bit prefixes: 10MB/s
* average match_longest throughput of 32bit prefixes with IAR16 optimization: 25MB/s
* average match_exact throughput of 32bit prefixes: 35MB/s
* average match_exact throughput of 32bit prefixes with IAR16 optimization: 58MB/s

where IAR optimization stands for Initial Array Optimization. In this particular case the array of size 2^16 is used.
All 16bit prefixes are stored in the contiguous array rather than organized in the trie. This reduces by 16/5 memory accesses giving away the
ability to store prefixes with lengths less than 16 bit and consuming a bit more memory.

The tests are done on i7-1185G7 @ 3.00GHz laptop CPU.

The data is taken from [Storing and retrieving IP prefixes efficiently](https://blog.apnic.net/2021/06/04/storing-and-retrieving-ip-prefixes-efficiently/) blog pot.

# Design decisions

The data structure intentionally supports only 8-byte trivial values. For larger value types, users must store and manage values themselves, with the trie storing only pointers to the values. It might be better to think of the data structure as an index rather than a container. This simplifies the implementation without sacrificing any functionality.

Allocator has different (incompatible) interface than the standard library's allocator. The trie requires [`realloc`](https://en.cppreference.com/w/cpp/memory/c/realloc) operations, which is not supported by the standard library's allocator.
