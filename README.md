# NeoProlog

A Prolog-inspired logic programming language implemented in Haskell.

## Usage

```prolog
neoprolog <file.nprolog>      # load a file and drop into the REPL
neoprolog reg <file.nprolog>  # register a module in ./neoprolog.conf
```

## Modules

Register a file as a module:

```prolog
neoprolog reg examples/mymod.nprolog
# → Registered mymod#<sha1> -> /absolute/path/mymod.nprolog
```

Import it in another file:

```prolog
<- import "mymod#<sha1>".

main <- mymod:greet "world".
```

The module's clause heads (and intra-module calls) are all prefixed with `mymod:`.

-----

neoprolog.conf needs to be added to support in LSP.

Install Simple ASM extension for Neo Prolog Support.
