# Type-based Information-Flow Control

Type systems are not just for types they can ensure that secret data does not
leak explicitly, implicitly, and even through covert channels. This repository
defines a simple language that does it and uses GADTs to make data leakage a
compile time error.

All the source code is in `src/VolpanoSmith.hs`.

The type system is based on Chapter 9 of "[Concrete
Semantics](http://concrete-semantics.org)" by Tobis Nipkow and Gerwin Klein.
This in turn is based on the following papers:

- [A sound type system for secure flow
  analysis](https://core.ac.uk/download/pdf/36700757.pdf) by Volpano, Irvine,
  and Smith
- [Eliminating covert flows with minimum
  typings](https://ieeexplore.ieee.org/document/596807) by Volpano and Smith
