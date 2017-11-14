This is an attempt to use [Lean](https://leanprover.github.io/) to implement a
proof of [Alpha-conversion is
easy](http://www.cs.nott.ac.uk/~psztxa/publ/alpha-draft.pdf) by Thorsten
Altenkirch.

## Get

Clone the repository and initialize and clone the submodules:

```
$ git clone --recurse-submodules https://github.com/spl/alpha-conversion-is-easy.git acie
```

## Build

*Normal build*

```
$ make
```

This will build a “release” version of `lean`. See the relevant
[instructions](https://github.com/leanprover/lean) for building on your
platform.

It will then build the repository code.

*Debug build*

```
$ make CMAKE_BUILD_TYPE=DEBUG
```

The only difference from the normal build is that a “debug” version of `lean` is
built.
