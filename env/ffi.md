---
layout: default
title: Foreign Function Interface (FFI)
---

# Foreign Function Interface (FFI)

Nexus calls out to WebAssembly modules. So you can extend a program with functions written in Rust, C, or any language that targets WASM.

## Importing WASM Modules

Load a WASM module with `import external`:

```nexus
import external "math.wasm"
```

The module's exports become available for binding.

## External Bindings

Bind a WASM export to a Nexus name:

```nexus
export external add_ints = "add" : (a: i64, b: i64) -> i64
external internal_helper = "helper" : (x: i64) -> unit
```

- `export` makes the binding visible to other modules
- The string literal after `=` is the WASM export name
- The type after `:` must be an arrow type

## Generic External Bindings

A polymorphic external needs explicit type parameters:

```nexus
export external length = "array_length" : <T>(arr: &[| T |]) -> i64
```

Using an undeclared type variable (`T` without `<T>`) is a type error. The check stops a typo from quietly turning into a type variable.

## Type Mapping

| Nexus Type | WASM Type | Notes |
|---|---|---|
| `i64` | `i64` | Direct |
| `float` / `f64` | `f64` | Direct |
| `i32` | `i32` | Via `i64` casting |
| `f32` | `f32` | Via `float` casting |
| `bool` | `i32` | 0 = false, 1 = true |
| `string` | `i64` | Packed as (offset, length) pair |
| `unit` | (none) | No WASM parameter generated |
| Records | `i64` | Heap pointer |

## Example

```nexus
import external "utils.wasm"

external process_data = "process" : (val: float) -> float

let main = fn () -> unit require { PermConsole } do
  inject stdio.system_handler do
    let result = process_data(val: 42.0)
    Console.println(val: string.from_float(val: result))
  end
  return ()
end
```

---

## How to Write Bindings

A WASM module that exports functions with the right signatures can be used from Nexus through `external` declarations. This section spells out the ABI contract the WASM module has to meet, the Nexus-side declaration patterns, and how the compiler transforms types at the boundary.

### FFI Parameter Encoding

The compiler transforms a few Nexus types when crossing the FFI boundary. Internal calls use packed forms; external calls unpack them:

| Nexus Type | WASM Signature (external) | Notes |
|---|---|---|
| `i64` | 1x `i64` | Direct |
| `i32` | 1x `i32` | Direct |
| `float` / `f64` | 1x `f64` | Direct |
| `f32` | 1x `f32` | Direct |
| `bool` | 1x `i32` | 0 = false, 1 = true |
| `string` | 2x `i32` (ptr, len) | Unpacked from internal `i64` |
| `unit` | (none) | No parameter generated |

**String parameters** are the critical case. Internally, Nexus stores a string as a packed `i64` (`(offset << 32) | length`). At the FFI boundary, the compiler unpacks that into two `i32` arguments: a pointer into linear memory and a byte length. The WASM export must accept these two `i32`s in place of a single `i64`.

**String return values** go the other way. The WASM export returns a packed `i64` with the same `(offset << 32) | length` encoding. The caller has to allocate memory and write the UTF-8 bytes into linear memory before packing the result.

**Bool values** are encoded as `i32` in both directions, with `0` for false and `1` for true.

### Labeled Argument Reordering

Nexus uses labeled args, but WASM functions are positional. The compiler turns labeled args into positional parameters **sorted by label name** in lexicographic order. The order matters when the WASM export's parameter order has to line up.

For example:

```nexus
external write = "write_buf" : (content: string, offset: i64) -> i64
```

The WASM signature for `write_buf` is `(i32, i32, i64) -> i64`. The `content` string (unpacked to ptr and len) comes before `offset`, since `"content" < "offset"` lexicographically.

If you declare:

```nexus
external send = "send_msg" : (to: i64, msg: string) -> bool
```

The WASM signature is `(i32, i32, i64) -> i32`; `msg` (→ ptr, len) comes before `to`, since `"msg" < "to"`.

When you write a WASM module, sort the export's parameters alphabetically by the label names used in the Nexus decl.

### WASM Module Requirements

A WASM module used over FFI must do all of the following:

1. **Export named functions** matching the WASM names in the `external` decls.
2. **Use the right parameter encoding** as described above; in particular, do the string split.
3. **Share linear memory** with the Nexus caller. String pointers are offsets in this shared memory.
4. **Export `allocate(i32) -> i32`** when the module returns strings or allocates memory that the caller reads. The Nexus runtime calls this to make room for data that crosses the boundary.

### Declaring Bindings

#### Primitive Functions

When the WASM export uses only numeric types, the decl is plain:

```nexus
import external "mylib.wasm"

export external clamp = "clamp_i64" : (val: i64, lo: i64, hi: i64) -> i64
export external is_even = "is_even" : (val: i64) -> bool
```

The Nexus name (left of `=`) and the WASM export name (string literal) are independent.

#### String Functions

Declare `string` on the Nexus side — the compiler generates the two-parameter split:

```nexus
import external "mylib.wasm"

external char_count = "char_count" : (s: string) -> i64
external repeat = "str_repeat" : (s: string, n: i64) -> string
```

The WASM export for `char_count` must have signature `(i32, i32) -> i64`. The export for `str_repeat` must have `(i32, i32, i64) -> i64`. You never write the split by hand.

#### Wrapping with Opaque Types

For a stateful resource backed by a handle, wrap the raw `i64` in an `opaque type` with linear ownership:

```nexus
import external "mylib.wasm"

export opaque type Counter = Counter(id: i64)

external __counter_new = "counter_new" : (initial: i64) -> i64
external __counter_inc = "counter_inc" : (id: i64) -> i64
external __counter_free = "counter_free" : (id: i64) -> bool

/// Creates a new counter with the given initial value.
export let new = fn (initial: i64) -> %Counter do
  let id = __counter_new(initial: initial)
  let c = Counter(id: id)
  let %lc = c
  return %lc
end

/// Increments the counter. Consumes and returns the handle.
export let inc = fn (counter: %Counter) -> { value: i64, counter: %Counter } do
  let Counter(id: id) = counter
  let val = __counter_inc(id: id)
  let c = Counter(id: id)
  let %lc = c
  return { value: val, counter: %lc }
end

/// Reads the current value without consuming the handle.
export let value = fn (counter: &Counter) -> i64 do
  let Counter(id: id) = counter
  return __counter_inc(id: id)
end

/// Frees the counter. Consumes the linear handle.
export let free = fn (counter: %Counter) -> unit do
  let Counter(id: id) = counter
  let _ = __counter_free(id: id)
  return ()
end
```

The patterns at work:

- **`opaque type`** — hides the constructor from importers. Only this module can build or destructure `Counter`.
- **`%Counter`** (linear) — the type system makes sure every counter is freed in the end. You cannot drop it on the floor.
- **`&Counter`** (borrow) — read-only access without consuming the handle.
- **Consume-and-return** — a mutating op destructures the handle, calls the FFI function, then builds and returns a fresh handle. So linear ownership is preserved across the boundary.

The WASM module manages the real state behind the handle, say an ID-keyed table. Nexus only sees the `i64` handle value.

### Organizing Bindings — One Wrapper File per WASM Module

**Pin every `import external "foo.wasm"` and its `external` decls to a single `.nx` file** — a thin wrapper module. Other code should depend on the wrapper rather than redeclare the bindings.

```
nxlib/stdlib/                        // root of the `std` package
  hashmap.nx                         // import external "nexus:intrinsic" + typed wrappers
  str.nx                             // import external "nexus:intrinsic" + typed wrappers
  ...
app/
  main.nx                            // import * as hm from "std:hashmap"  — no `external` here
```

Why this matters:

- **One source of truth for the ABI.** Parameter order, encoding, and WASM export names are fragile (see [Labeled Argument Reordering](#labeled-argument-reordering)). When the same binding is declared in two files, the two copies tend to drift.
- **Linear/borrow discipline lives in the wrapper.** Raw `external` functions deal in plain `i64` handles. The wrapper layer puts `%T`, `&T`, and opaque types back in. A caller should never see the raw external form.
- **`wasm-merge` inlining is per-module.** One wrapper file means one place where the `.wasm` blob is linked, so the build avoids duplicate symbol work.

Rule of thumb. When a non-wrapper `.nx` file uses the `external` keyword, that is a smell. Move the bindings into a dedicated wrapper module.

### Linking

The compiler resolves `import external "mylib.wasm"` at build time through `wasm-merge`. The `.wasm` path is taken relative to the importing `.nx` file. After the merge, the final binary has no unresolved imports; every external function is inlined.

See [WASM and WASI](wasm.md) for details on memory layout, the allocator protocol, and the full ABI specification.
