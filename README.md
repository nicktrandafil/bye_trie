# ByeTrie is bits trie data structure

ByeTrie is a trie data structure where keys are bit strings. It is based on the [Tree Bitmap : Hardware/Software IP Lookups with
Incremental Updates](https://cseweb.ucsd.edu/~varghese/PAPERS/ccr2004.pdf) paper by W. Eatherton, Z. Dittia, G. Varghese.

The goal of this implementation is to be space and time efficient as much as possible.

# Benchmarks

Internet's IPv4 prefixes and ASNs (about 893k) are used as test data. The results are:

* Peak memory consumption 6MB.
* Average longest prefix lookup search time 13ns.
* Average insert time 78ns.

The tests are done on i7-1185G7 @ 3.00GHz laptop CPU.

The data is taken from [Storing and retrieving IP prefixes efficiently](https://blog.apnic.net/2021/06/04/storing-and-retrieving-ip-prefixes-efficiently/) blog pot.

# Design decisions

The data structure intentionally supports only 8-byte trivial values. For larger value types, users must store and manage values themselves, with the trie storing only pointers to the values. It might be better to think of the data structure as an index rather than a container. This simplifies the implementation without sacrificing any functionality.

Allocator has different (incompatible) interface than the standard library's allocator. The trie requires [`realloc`](https://en.cppreference.com/w/cpp/memory/c/realloc) operations, which is not supported by the standard library's allocator.
