This is an attempt — so far unsuccessful — to implement a proof of
[Alpha-conversion is easy](./doc/alpha-conversion-is-easy.pdf) by Thorsten
Altenkirch in [Lean](https://leanprover.github.io/).

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
