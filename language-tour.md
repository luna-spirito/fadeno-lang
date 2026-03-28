This is plain-language overview of Fadeno with thorough explanations of concepts behind it.

Fadeno is a declarative/functional programming language featuring extrinsic, gradual, dependent typing.

Shallow overview (in-depth later):
* **Declarative**: The language and its components are designed to facilitate high-level descriptions. Instead of forcing users to write complicated imperative code, most logic is defined via high-level constructs and utilities.
* **Functional**: The language incorporates so-called "lambdas" (functions or templates). We'll discuss these later.
* **Typing**: The language has "type checking" — a sophisticated compiler check that prevents mismanagement of available resources. For example, attempting to sum an integer with a string like `"1" + 1` would be caught instantly by the compiler in a typed language.
* **Extrinsic typing**: Languages can have either "intrinsic" or "extrinsic" typing. Intrinsically typed languages embed the type system directly into the language core, mixing it with runtime behavior. Changing a function's type in such languages alters how it compiles. Extrinsically typed languages have the type system layered on top, meaning typing doesn't interfere with how language normally operations.
* **Gradual typing** (made possible since we're extrinsic): While the language is statically typed, this isn't rigorously enforced. Programmers can ignore the type system entirely and write code uninterrupted.They'll pay for this with extensive debugging. At least they're not forced to learn type theory.
* **Dependent typing**: One of the most powerful type system features, allowing "context-aware" types that **depend** on existing values.

For simplicity, we'll assume throughout that `+`, `*`, and other operations are imported from the standard library — these are NOT inherent parts of the language.

# Erasure
Since Fadeno is extrinsic, much code gets "erased" from runtime and exists only to satisfy the type checker. If you see `/: ...` (type annotation), `... @= ...` (erased binding), `@(...)` (erased argument), or `rewrite ...` (type-level rewrite), you can safely ignore these — they're merely hints for the type checker.

# Everything is an expression

Every Fadeno program is a single expression. The complete list of possible expressions:

* **Numbers**: `4`, `-21`
* **Tags**: `.ohoho`, `.just-any-label-you-want-after-a-dot`
* **Booleans**: `true`, `false`
* **Lists** of other expressions:
  * `[1 | 2 | 3]`, `["Hello, world!"]`, `[.ohoho | 41 | true | "blah"]`
  * (the last example is ill-advised)
* **Records** (or objects, like in JavaScript/JSON):
  * `{ .k = 4 | .v = "Hello, world!" }`
  * `{ .name = "John Doe" | .age = 42 }`
  * `{ .a = { .b = 2 | .c = 3 } | .b = true }`
  * (keys must be tags; values can be any expressions)
  * Records can serve as "libraries" of functions and types ("modules").
* **Lambdas/anonymous functions/templates**:
  * `\x. x + 1` (accepts a number, returns its increment)
  * `\banana y. banana + y` (accepts two numbers, returns their sum)
  * `\uwu. [uwu, uwu, uwu]` (accepts any object, returns a list of three copies)
* **Binding blocks** (convenience syntax):
  ```fadeno
  x = 3
  y = 4
  z = 5
  in x + y + z
  ```
  This is still a single expression — a "block". It contains any number of bindings (`x`, `y`, `z`), followed by `in` and an expression using those bindings (`x + y + z`). This convenience syntax splits expressions into manageable parts and recombines them. Note that `x`, `y`, and `z` are constants, not variables.

  Bindings can be annotated with an expression denoting type:
  ```fadeno
  /: type expression here
  binding-name = binding-value
  ```

  Besides introducing constants, you can use `rewrite (expression)` to perfomm type-rewrites for type-level theorem proving.
* **Lambda application**:
  * `(\x. x + 1) 3` ⇒ `4`
  * `(\banana y. banana + y) 3 4` ⇒ `7`
  * `(\uwu. [uwu, uwu, uwu]) "Hello, world!"` ⇒ `["Hello, world!", "Hello, world!", "Hello, world!"]`
  *
    ```fadeno
    f = \x. x
    in f 4
    ```
    ⇒ 4
  * Application is written as `function argument`. The `function` being any expression that evaluates to a lambda, and the `argument` being any expression that gets substituted as the lambda's argument.
  * There's also *erased* application: `function @argument`.
* **Bindings**: As you might have noticed, bindings introduced by lambdas or blocks are expressions. Thus, `blablah` in `\blahblah. ...` is an expression.
* **Built-in value `fadeno`**: Evaluates to a record containing core functions and types; used extensively by the standard library; probably shouldn't be used directly.
* **Types**, including:
  * Pi ("Π") types (i. e. types of functions, typically look like `Fun (a : B) -> C`)
  * Dependent concatenation (used to build type-level descriptions of records, typically look like `a : A \/ B`)
* **Special `SORRY` expression**: Acts as a placeholder for unwritten code.

Remember: everything listed is an expression. Lambdas are expressions; types are expressions. You can store a lambda or type in a constant, or you can process it with another lambda.

```fadeno
apply4 = \f. f 4
in apply4 (\x. x * 2)
```
Here, `apply4` holds the lambda `\f. f 4` — it accepts some `f` and returns the application of `4` onto `f`. We pass `\x. x * 2` as `f`, yielding `4 * 2 = 8`.

# What you can and can't do

All you can do is define new expressions and combine them indefinitely.

You can use Fadeno for configuration files (using records, constants, and even embedded lambdas).

However, you cannot perform typical imperative operations: no interaction with the outside world, no updating constants or their values, no multiple separate statements.

# Naming convention

Dependently typed languages routinely blur values and types (both are expressions, after all), so Fadeno lacks a rigid naming convention — creating one is probably impossible.

But, in general:
* Almost ANY character sequence is valid for operators or constants:
  * `Int+`
  * `int_>=0`
  * `~i++1`
  * `~+_eq_++`
  * `~int+>=0`
* Regular functions and values typically use `snake_case`:
  * `record_get`
  * `inv_index`
  * `list_indexl`
* Types and type-level functions typically use `CamelCase`:
  * `List`
  * `Int`
  * `Int+`
  * `Record`
  * `Row^`
  * (though you might see `snake_case` at the type level)
* When a type name appears in a regular value name, use `snake_case` with the type in `lowerCamelCase` at the start:
  * `list_indexl`
  * `int+_add`
  * `myType_do_something`
  * (prefer proper module structure via records to avoid this)
* Theorem proofs and type-checker observations typically prefix with `~`.

# Records
Record keys are any tag-expressions; values can be any expressions: types, lambdas, other records, etc.

```fadeno
// `if` — unimplemented syntactic sugar for the builtin `if` from `fadeno`.

/: (type omitted)
get_company_info = \friday_evening.
  my_tag = if friday_evening .workers .zombies

  in
    { .name = "Tute nesuspektinda kompanio"
    | .age = { .years = 0 | .months = 0 | .days = -1 }
    | .area_of_work = "Work"
    | (my_tag) =
      [ { .name = "Sébastien‑Chrysostome de la Fontaine‑Montblanc‑Astérophile"
        | .job = "Quantum Cartographer" }
      | { .name = "Dr. Rajanikanth Venkata Ratnamacharya IV Nageswara‑Raman"
        | .job = "Interdimensional Botanist" }
      | { .name = "Ekaterina Vladimirovna Petrovskaya‑Kozlovskikh"
        | .job = "Subterranean Sound Designer" }
      | { .name = "John", .job = "John" }
      ]
    }

// Returns a record with fields `.name`, `.age`, `.area_of_work`, and `.zombies`.
in get_company_info true
```
(Note: actually typing this requires dependent types, discussed later.)

You can access specific fields with `.`: `(get_company_info true).name`. This is a syntactic sugar to the call to the builtin `record_get` from `fadeno`.

Internally, records act as "lists" of tagged values. Records can theoretically have multiple fields with the same name.

# Typing

Each binding in a block can be type-annotated:

```fadeno
// `List` and `Int` are imported
// By the way, `List` is a function accepting a type and returning a type

/: Int
x = 4

/: List Int
y = [5 | 8 | x]

in y
```
The type checker will try to verify that each value matches its specified type.

If the type is not provided, the type checker will try to infer it.

There are no guarantees the type checker will succeed, as type checking is undecidable. And so you either spend your times proving theorems to please the type checker, which I'm not recommending you to do, or you just ignore his cries and go on with your day, which is absolutely the best thing to do in this situation.

When `x` has type `Y`, we write `x : Y`.

## Totality

If a program type-checks without errors and avoids `SORRY` or other unsafe operations, it's "total".
"Total" means it terminates in finite time for all inputs without errors — no panics, exceptions, division-by-zero, out-of-bounds errors, etc.

Ensuring totality is, well, hard.

## Types of lambdas

If input `x` has type `X` and output `y` has type `Y` (i.e., `x : X`, `y : Y`), then lambda `\x. y` has type `Fun (X) -> Y` (that's non-dependent Π type).

Example:
```fadeno
/: Fun (Int) -> Int
id = \x. x

in ...
```
Here, `id` accepts a number and returns a number.

However, this is suboptimal — the same lambda `\x. x` could accept `List Int` and return `List Int`, but we've restricted it to numbers.

Fortunately, Fadeno is ~~gradually typed and we needn't care~~ dependently typed, which lets us to write such a type for `id` that will adjust itself based of the context.

But first, step back. A cool thing about Π types is that they let the output **type** depend on the input **value**. Consider:

```fadeno
// `Bool` and `Int` imported; `if` is unimplemented syntactic sugar over the `if` builtin.

/: Fun (x : Bool) -> if x (Int) (List Bool)
screwed_up = \a. if a
  (4)
  ([true, true, true, false, false, false, true, true, true])

in screwed_up true // ⇒ 4
```
Function `screwed_up` accepts a bool but returns either an integer or a list of bools. Yet it's well-typed! That's because we used dependent Π: `Fun (x : Bool) -> if x (Int) (List Bool)`.

This reads: the function accepts some boolean, let's call it `x`; the output of a function then has type `if x (Int) (List Bool)`.

Thus, `screwed_up true` has type `if true (Int) (List Bool)`, which simplifies to just `Int`.

Meanwhile, `screwed_up false` has type `if false (Int) (List Bool)`, which simplifies to `List Bool`.

This demonstrates how a function's output type **depends!** on its input value.

Dependent typing enables:
1. Functions whose output type depends on the input argument.
2. Records whose structure depends on previous fields.

Getting back to `id`, we can make it accept a type as one of the inputs:

```fadeno
/: Fun (A : Type) (A) -> A
id = \X x. x

in id Bool true
```
Here, `id` accepts `A : Type` and returns `Fun (A) -> A`.
* `id Bool` has type `Fun (Bool) -> Bool`
* `id (List Int) : Fun (List Int) -> List Int`
* `id WhateverTypeYouHave : Fun (WhateverTypeYouHave) -> WhateverTypeYouHave`

Writing the type explicitly on each `id` call is tedious, so we have *erased* arguments:

```fadeno
/: Fun {A : Type} (A) -> A
id = \@X x. x

in id @Int 4
```
Nothing changed; we merely replaced normal arguments with erased arguments in `{}`. This requires erased lambda `\@X.` and erased application `@Bool`.

However, Fadeno's type checker can sometimes infer erased arguments automatically:

```fadeno
/: Fun {A : Type} (A) -> A
id = \x. x

in id 4
```
This is equivalent to the previous code; the type checker infers `Int` from context. It's not always that clever, so you might need to explicitly specify eased arguments in complex scenarios.

## Type universes

What is the type of a type?

Types (e.g., `Int`) are expressions in Fadeno. So, what's the type of such an expression? We could call it `Type`: `Int : Type`. But then what's `Type`'s type?

A tempting answer: `Type : Type`. However, Girard's paradox shows this causes type system inconsistency.

To avoid this, we, unfortunately, use indexed type universes. Instead of a builtin `Type`, we have a builtin function `Type^`:
* All types have type `Type^ 0` (application of `0` to `Type^`). Example:
  * `Int : Type^ 0`
  * `Type^ 0 : Type^ 1`
  * `Type^ 1 : Type^ 2`
  * ...
* `Type^ i : Type^ (i + 1)`
* ...

The standard library defines `Type` as `fadeno.Type^ 0`.

This resolves the paradox, but means our `id` function isn't as general as desired:

```fadeno
/: Fun {A : Type} (A) -> A
id = \x. x

// Type error!
in id @Type Bool
```

Here we pass `Type` as `A : Type^ 0`, but `Type : Type^ 0` is false. To fix this, we can parameterize `id` over universe level:

```fadeno
/: Fun {u : Int+} {A : Type^ u} (A) -> A
id = \x. x

in id @1 @Type Bool
// or just `id Bool`
```

By the way, this code is identical to:

```fadeno
id = \x. x

in id Bool
```
...since the compiler is clever enough to infer the aforementioned type automatically.

Moral: If you see `{u : Int+} ...` in a standard library function's type, it's a type universe artifact. Most of the time, you're safe with just using `Type` everywhere.

## Records

The record `{ .x = true | .y = "Hello, world!" | .z = [1, 1, 1, 0, 0, 0, 1, 1, 1] }` has type `{( .x = Bool | .y = Text | .z = List Int )}`.

Two rows can be dependently concatenated: `a : Row1 \/ Row2`, where `Row2` depends on `Row1`'s fields.

Example: `meta : { .yes = Bool } \/ (if meta.yes { .v = Int } {})`. Such a record has field `.v` only if `.yes` is true.

```fadeno
Option = \V. Record (meta : { .has_value = Bool } \/ (if meta.has_value { .v = V } {}))

/: Fun {u : Int+} {A : Type^ u} -> Option A
none = { .has_value = false }

/: Fun {u : Int+} {A : Type^ u} (A) -> Option A
some = \a. { .has_value = true | .v = a }

/: Fun {u : Int+} {A : Type^ u} (Option A) (A) -> A
unwrap_or = \option default. if option.has_value
  option.v
  default

in unwrap_or none 4
```
⇒ 4
