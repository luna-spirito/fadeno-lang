# Fadeno

A declarative/functional dependently-typed programming language, inspired by [Cedille](https://github.com/cedille/cedille)/[Dhall](https://github.com/dhall-lang/dhall-lang).
Designed to be a simple, minimalistic yet powerful language for [Dentrado Functional-Reactive DBMS](https://github.com/luna-spirito/dentrado-poc).

## Running type-checker

```sh
nix develop .#
cabal v2-test
```

Sample source code files are listed in [fad/](./fad/). Types inferred for them are provided in [test/golden/](./test/golden/).

## Key features
Fadeno is an experimental language focusing on simplicity, declarativity and expressivity.
* **Extrinsic typing**: Type system is entirely isolated from the language execution core. There is a set of erased constructs (erased bindings `@=`, erased arguments `\@`, type annotations `/:` for constants, type-level rewrites `rewrite`) that exist solely for type-checking and formal verification and get erased at runtime.
* **Dependent typing**: Supports Π-types and Σ-types (via row concatenation construct).
* **Row types and row polymorphism**: Supports row types, records, experimental dependent row concatenation to mirror dependent intersection.
* **Totality-oriented**: Core constructs are designed to be total. Recursion is implemented via measure-based builtins. Girard paradox is averted by using type universes. Totality is not formally proven as of now.
* **Everything is an expression**: The language has no statements. Functions, types, modules and primitives are all first-class expressions. 
* **Gradual typing escape hatch**: The language is statically typed, but allows developers to omit types/proofs and write code seamlessly.

The language uses instensional equality.
Structural typing is used by default, with nominative typing as opt-in.

The compiler is written in Haskell and uses [bidirectional type-checking](https://www.cl.cam.ac.uk/~nk480/bidir.pdf), being capable of both checking expressions against type annotations and inferring types for expressions. Language uses subtyping.

After extrinsic type erasure, normalized AST is compiled into a custom stack-based bytecode.

## Fadeno in Y minutes

(Taken from [fad/in_y_minutes.fad](./fad/in_y_minutes.fad))

```
// Comments

// Unpacks Int, Type^, List, if... from built-in "fadeno" library into current context
unpack fadeno. Int Type^ List if Eq refl Bool

// Constants
x = true

// Assigning lambda to constant
add =
  // Lamba of arguments "a" and "b"
  \a b.
  // Call to the builtin function `fadeno.int_add`, savin the result to constant `result`
  result = fadeno.int_add a b
  in result

// Type annotations for constants, checked
// If no annotation is provided, it's infered automatically
/: Int
y = 4

// Type of functions is `Fun (A) (B) (C) -> Z`

// Function of two Int's that returns Int.
/: Fun (Int) (Int) -> Int
constf = \arg1 arg2.
  arg2 // returns the second argument passed

// Lists
/: List Int
list = [1 | 3 | 5 | 4 | -1]

// Records and row types
/: {( .field1 = Int | .field2 = Fun (Int) (Int) -> Int | .zer = List Int )}
record =
  { .field1 = 4
  | .field2 = constf
  | .zer = [ 1 | 3 ]
  }

// Accesing fields of records
accessedField1 = record.field1

// Type aliases
/: Type^ 0
MyRecord = {( .a = List Int )}

/: MyRecord
my_record = { .a = [] }

// Type universes
/: Type^ 1
Type = Type^ 0
/: Type^ 2
Kind = Type^ 1

// Polymorphism
/: Fun {A} (A) -> A
id = \@A x.
  x

// Theorem proving capabilities
/: Fun {a} {b} {c} (Eq a b) (Eq b c) -> Eq a c
proof = \ab bc.
  rewrite ab
  in bc

// Dependent types
/: Fun (x : Bool) -> if x (Int) (List (List Int))
cond = \x.
  if x
  (\@x_is_true. rewrite x_is_true in 3)
  (\@x_is_false. rewrite x_is_false in [[3]])

// Importing other files
other_file = ./test/myif

in {}
```

Work-in-progress standard library module is located at [fad/std.fad](./fad/std.fad).

## Constructs
* Number literals: `1`, `2`, `-10`
* Tag/label literals, prefixed with `.`: `.my-tag`, `.value`, `.has`
* Bool literals: `true`, `false`
* List literals: `[1 | 2 | 3]`, `[false | 2 | .tag ]`
* Record literals: `{ .key = 3 | .value = 4 }`, `{ (my-tag-variable) = 5 | .value = 4 }`
* Row type literals: `{( .key = Int | .value = Int )}`, `{( (my-tag-variable) = Int | .value = Int )}`
* Builtins literal `fadeno` — a globally available record with all built-in definitions, such as `Int`
* Lambdas & Π types:
  * `\a b. a + b` : `Fun (Int) (Int) -> Int`
  * `\x. x` (or `\@A x. x`) : `Fun {A : Any} (A) -> A`
  * `@` is used to denote erased (implicit) arguments.
* Applications: `f a` (non-erased) or `f @a` (erased)
* Type holes (`SORRY`)
* Existential quantification (erased):
  * `@|Int| 4` : `@|A : Type^ 0| A`
* Refinement types: 
  * `4 @|refl|` : `Int @|non0 : Where (. >= 0)`
* Dependent row concatenation:
  * `{ .has = true } \/ { .b = 4 }`
    * : `{( .has = Bool )} \meta/ if meta {( .b = Int )} {()}`

## Future work

* Proper integration into [Dentrado Functional-Reactive DBMS](https://github.com/luna-spirito/dentrado-poc).
* Research into implementation of Call-By-Push-Value evaluation strategy.
* Research into implementation of inductive types via Mendler-Style lambda encoding and dependent intersection.

## Known limitations

* **No soundness proof**: The type system has not been formally verified. The language should be considered experimental.
* **`SORRY` escape hatch**: The `SORRY` construct allows bypassing the type checker. Programs using it provide no totality guarantees.
* **Signature validation**: Type annotations are not fully validated — e.g. passing a negative integer as a universe level is not caught.
* **Undecidable type checking**: As expected for a dependently typed language, type checking may diverge or fail on valid programs.
* **No I/O or FFI**: The language is purely computational. No mechanism for side effects, external communication, or interfacing with other languages exists yet.

## Related work

* **[Cedille](https://github.com/cedille/cedille)**: Primary inspiration. Cedille is an extrinsically typed language using a Curry-style type theory with erased annotations, dependent intersection types, and equality proofs. Fadeno's extrinsic approach is directly influenced by Cedille.
* **[Dhall](https://github.com/dhall-lang/dhall-lang)**: Inspiration for the declarative configuration-oriented style and total-by-design philosophy.
* **[PureScript](https://github.com/purescript/purescript)**: Row polymorphism and extensible records. Fadeno extends this with dependent row concatenation.

## Deep dive
For a detailed, beginner-friendly language tour, check out [language-tour](./language-tour.md).
