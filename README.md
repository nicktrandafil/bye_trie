# Bits Trie data structure

Trie data structure where keys are bit strings. Based on the [Tree Bitmap : Hardware/Software IP Lookups with
Incremental Updates](https://cseweb.ucsd.edu/~varghese/PAPERS/ccr2004.pdf) paper by W. Eatherton, Z. Dittia, G. Varghese.

The goal of this implementation is to be space and time efficient as much as possible.

# Benchmarks

Internet's IPv4 prefixes and ASNs (about 800k) are used as test data. 
Peak memory consumption 6MB.
Average longest prefix lookup search time 13ns.
Average insert time 78ns.

The tests are done on i7-1185G7 @ 3.00GHz laptop CPU.

The data is taken from [Team Cymru](https://blog.apnic.net/2021/06/04/storing-and-retrieving-ip-prefixes-efficiently/).
