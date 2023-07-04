# Verified asymmetric numeral systems (vANS)
This repository contains a proof-of-concept Flipper implementation of asymmetric numeral systems
compression. Implementing vANS in the reversible language
[Flipper](https://github.com/j-towns/flipper)
means a proof is automatically generated showing that vANS is truly lossless, and this proof is checked by
Agda.
See the [short LAFI workshop paper](https://arxiv.org/abs/2211.09676) for more details on Flipper.
I plan to write up a longer paper on Flipper and vANS soon.

It is possible to compile the files `src/MainEnc.agda` and `src/MainDec.agda` into binaries, using
`agda --compile`, and to use them to compress and decompress ASCII text. The encoder and decoder run at roughly
100kB/s on my computer.

Everything is tested with Agda version 2.6.3. The dependencies are [Flipper](https://github.com/j-towns/flipper) and
Ulf Norell's [adga-prelude](https://github.com/UlfNorell/agda-prelude).
