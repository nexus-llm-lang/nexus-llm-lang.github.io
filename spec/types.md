---
layout: default
title: Types
---

# Types

Nexus has a strict type system. The core pieces are Hindley-Milner inference, structural records, ADTs, and linear types for tracking resources.

## Primitive Types

| Type | Description |
|---|---|
| `i32` | 32-bit signed integer |
| `i64` | 64-bit signed integer |
| `f32` | 32-bit floating-point |
| `f64` | 64-bit floating-point |
| `float` | Alias of `f64` |
| `bool` | Boolean (`true` / `false`) |
| `char` | Single Unicode character (`'a'`, `'\n'`, `'\x41'`, `'\u{1F600}'`) |
| `string` | Immutable UTF-8 string |
| `unit` | The unit type, written `()` as a value |

Numeric literals default to `i64` (integers) and `f64` (floats) unless constrained by type annotations.

## Compound Types

### Records

Records are structural. You can define one with `type` or use it inline:

```nexus
export type User = { id: i64, name: string }

let u = { id: 1, name: "Alice" }
```

### ADTs (sum types)

ADTs use labeled constructor arguments:

```nexus
export type Result<T, E> = Ok(val: T) | Err(err: E)
export type Option<T> = Some(val: T) | None
```

### Opaque Types

The `opaque` modifier hides constructors from importers. The type name shows up, yet you can only build or match the value inside the defining module.

```nexus
export opaque type Set = Set(id: i64)
```

Importers see `Set` as a type. The constructor form is off-limits for both building and pattern matching from the outside. The defining module has to expose functions for creation and access.

### Lists

Immutable singly-linked lists:

```nexus
let xs: [i64] = [1, 2, 3]
```

Lists cannot contain mutable references.

### Arrays

Arrays are linear and mutable. Linearity ensures one owner at a time:

```nexus
let %arr: [| i64 |] = [| 1, 2, 3 |]
%arr[0] <- 42
let val = (&%arr)[0]
```

Arrays cannot contain mutable references.

### Generics

User-defined types can be parameterized:

```nexus
export type Pair<A, B> = Pair(left: A, right: B)
```

## Linear Types (`%`)

Linear types put resource lifecycle in the syntax (see [Design](../../design#linear-types-as-literal-resource-tracking)). The `%` sigil marks a binding that must be used **exactly once**.

### Rules

| Rule | Enforcement |
|---|---|
| Must consume exactly once | Compile error if unused or used twice |
| Cannot discard with `_` | Wildcard on composite linear value is rejected |
| Branch consistency | All branches must consume the same linear bindings |
| Closure capture | Capturing `%x` makes the closure itself linear |
| No mutable ref | `~` binding cannot hold a linear type |

### Primitive Auto-Drop

Primitive linear values (`i64`, `f64`, `bool`, `string`, `unit`) are automatically released at scope end. Using `%` on primitives is valid but unnecessary.

### Composite Consumption

A composite linear value (record, ADT, or array) needs an explicit consume. The three channels are:
- A function call. Pass the linear binding as an argument.
- A pattern match. The destructure pulls out the value.
- A return. Ownership moves to the caller.

Field projection (`r.field`) is **not** a consume for a linear record. A single field read would expose one field while quietly dropping the other linear obligations on the value. The type system rejects projection on any record whose type is structurally linear. Use pattern matching to pull out fields.

### Linearity Weakening

A plain `T` value can be passed to a function expecting `%T`. The value is then treated as linear while the call runs.

### Linear Closures

When a closure captures a linear binding, the closure becomes linear too. You can call it once:

```nexus
let %resource = acquire()
let f = fn () -> unit do
  consume(r: %resource)
  return ()
end
f()  // ok -- consumes the closure
f()  // error -- closure already consumed
```

## Borrowing (`&`)

The `&` sigil creates an immutable, non-consuming view of a value (see [Design](../../design#borrowing-puts-aliasing-on-the-page)).

### Syntax

`&` works as a prefix operator and as a let-binding sigil:

```nexus
let borrowed = &arr  // prefix operator on immutable binding
let &b = ~x          // let-binding sigil
let b2 = &%resource  // prefix operator on linear binding
```

### Coercion

`&T` coerces to `T` for reading. The original binding remains live and unconsumed.

### Patterns

Borrow patterns bind without consuming:

```nexus
fn peek(x: &i64) -> unit do
  // x is &i64, original not consumed
  return ()
end
```

### Properties

- You can take many borrows of the same binding at once
- A borrow lives only as long as the source binding's scope
- A borrow of a linear value does not consume it

## Mutable References (`~`)

The `~` sigil creates a stack-confined mutable binding:

```nexus
let ~count = 0
~count <- ~count + 1
```

### Gravity Rule

Mutable references cannot escape the defining function:

- Cannot be returned from functions
- Cannot be stored in heap-allocated structures (records, ADTs, lists)
- Cannot be captured by closures or `@` thunks (which may evaluate in parallel)

So mutation stays local and easy to follow.

### Restrictions

- Cannot hold linear types (`~` on `%T` is forbidden)
- Cannot be captured by lambdas
- Cannot be captured into a `@` thunk (which may evaluate on another thread — see [lazy.md](./lazy))

## Sigil Compatibility Matrix

| Operation | Immutable | `~` Mutable | `%` Linear | `&` Borrow |
|---|---|---|---|---|
| Read | yes | yes (deref) | yes (consumes) | yes |
| Assign (`<-`) | no | yes | no | no |
| Pass to function | yes (copy) | snapshot value only | yes (move) | yes (view) |
| Return from function | yes | no | yes | no |
| Store in record/ADT | yes | no | yes | yes |
| Capture in closure | yes | no | yes (makes closure linear) | yes |
| Borrow with `&` | yes | yes (`&~r`) | yes | yes |
| Discard with `_` | yes | yes | no (composites) | yes |

The "Pass to function" row for `~` cells reads **the current value out of the cell**. The storage stays in the defining function. Writing `f(arg: ~r)` at a call site reads `r` and passes that value. The inner type `T` shows up at the callee, in place of `~T`. So the callee gets a plain `T` and has no path back to the caller's storage.

To let a callee read or update the cell, take a borrow. Pass `&~r` and have the callee accept a `&T` (read-only) parameter. The borrow stays stack-confined under the gravity rules above; it cannot outlive its source.

Passing the storage *itself* as a `~T` parameter is rejected. Either two frames would hold the same backing slot, or the no-escape rule would break.

## Function Types

Functions are first-class values. Each parameter has a label. The throws and cap annotations are optional.

```nexus
(label: T) -> R                                 // pure function
(a: i64, b: i64) -> i64                         // multiple params
() -> unit throws { Exn }                       // with throws
() -> string require { Net }                    // with capability
(x: T) -> R require { C | r } throws { E | e }  // open rows
```

### Closures

A lambda captures immutable bindings from its lexical scope:

```nexus
let f = fn (x: i64) -> i64 do
  return x + 1
end
```

Closure constraints:
- Cannot capture mutable (`~`) bindings
- Capturing a linear (`%`) binding makes the closure linear
- A recursive local lambda requires an immutable `let` binding with an explicit type annotation

## Row Types

Row types back the effect and cap annotations:

```nexus
{ Exn }          // single entry
{ Net, Fs }      // multiple entries
{ Console | e }  // open row with tail variable
```

An empty row, written `{}` or just omitted, means no effects and no requirements.
