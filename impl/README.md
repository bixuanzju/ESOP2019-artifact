# SEDEL---A Source Language Built on Fi+

## Build and Run

This project can be built with
[cabal](https://www.haskell.org/cabal/download.html) or
[stack](https://docs.haskellstack.org/en/stable/README/).

* cabal
```
cabal sandbox init
cabal install --only-dependencies
cabal build
cabal exec sedel-exe
```

* stack
```
stack build
stack exec sedel-exe
```

## REPL

The REPL prompt is `>`:
- type `:q` to quit
- type `:load` to load a file
- type `:?` for usage

```
> :load examples/case_study.sl 
Typing result
: String

Evaluation result
=> "add1(var x = 3.0; var y = 4.0; (if (x < y) then (x + 2.0) else (y + 3.0))) = 6.0"
```

## Quick Reference

A program consists of list of declarations (separated by `;`), ended with a `main` declaration.
Like Haskell, a line comment starts with `--` and a comment block is wrapped by
`{-` and `-}`. 

* Primitive type: `Int`, `Bool`, `Double`, `String`
* Top type/value: `() : Top`
* Bottom type: `Bot`
* Type annotation: `2 : Int`
* Merge: `true ,, 3`
* Intersection type: `Bool & (Int -> Int)`
* If: `if x == 0 then true else false`
* λ term: `\(x : Int) -> x+1`
* Λ term: `/\ (A * Int) . \(x : A) -> x`
* Disjoint quantification: `forall (A*Int) . A -> A`
* Term declaration: `id A (x : A) = x`
* Type declaration: `type Person = {name : String, male : Bool}`
* Traits: `trait [self : Person] => { age = 42 }`


## Examples 

See the [examples/](./examples/) directory. All examples can be tested:

```
stack test
```
