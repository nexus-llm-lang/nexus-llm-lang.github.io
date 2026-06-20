---
layout: default
title: WASM and WASI
---

# WASM and WASI

Nexus compiles to the WebAssembly Component Model and uses WASI for system interfaces. The cap system maps to WASI caps one-to-one. Every `require { PermX }` in the program lines up with a concrete WASI interface grant.

## Perm-to-cap mapping

A program's required perms live in `main`'s `require` clause. When you run a compiled program with `wasmtime`, you pass a flag for each perm that needs a runtime grant. `nexus build --explain-capabilities=wasmtime` prints the exact `wasmtime` command for the program. Only `Fs` and `Net` need a runtime flag today; the rest are checked statically. The underlying WASI calls always succeed under the default `-Scli` profile.

| Nexus Permission | Runtime mapping (wasmtime flag) |
|---|---|
| `PermConsole` | (none — stdio is available under `-Scli`) |
| `PermFs` | `--dir .` (preopen the current directory) |
| `PermNet` | `--wasi inherit-network` (preview1 sockets; HTTP is currently stub-only) |
| `PermRandom` | (none — statically checked) |
| `PermClock` | (none — statically checked) |
| `PermProc` | (none — statically checked) |
| `PermEnv` | (none — statically checked) |

The mapping is defined by `cap_wasmtime_flags` in `src/cli/format.nx`.

## Cap enforcement

### Static check

The type checker ensures the following:
1. Any function that calls a cap-requiring cap must itself `require` that cap, or have it satisfied via `inject`.
2. `main`'s `require` clause is the source of truth for the program's cap surface.

### Reporting required perms

Caps are not stored in the compiled binary. The compiler enforces them at compile time, and the build can report the program's cap surface via `nexus build --explain-capabilities` (see [Inspect Capabilities](#inspect-capabilities)).

### Runtime enforcement

Only `Fs` and `Net` have a runtime mapping; you grant them with wasmtime flags when you run the program:

- **Filesystem isolation**: `Fs` maps to `--dir .` (preopen the current directory). With no `PermFs`, you preopen no directory.
- **Network isolation**: `Net` maps to `--wasi inherit-network`. With no `PermNet`, network interfaces are not inherited.

The remaining caps (`Console`, `Random`, `Clock`, `Proc`, `Env`) have no runtime wasmtime mapping — they are enforced by the compile-time static check only.

## ABI

This section spells out how Nexus values are stored in WebAssembly. You'll need this to write FFI bindings or to debug compiled output.

### Type Mapping

Every Nexus type maps to a WASM value type:

| Nexus Type | WASM Type | Representation |
|---|---|---|
| `i32` | `i32` | Direct |
| `i64` | `i64` | Direct |
| `f32` | `f32` | Direct |
| `f64` / `float` | `f64` | Direct |
| `bool` | `i32` | 0 = false, 1 = true |
| `char` | `i32` | Unicode scalar value |
| `unit` | (none) | No runtime value |
| `string` | `i64` | Packed pointer + length |
| `[T]` (list) | `i64` | Heap pointer |
| `[| T |]` (array) | `i64` | Heap pointer |
| `{ ... }` (record) | `i64` | Heap pointer |
| ADT variant | `i64` | Heap pointer |
| closure / `fn(...)` | `i64` | Heap pointer |

Every heap-allocated value (record, ADT, list, array, or closure) is an `i64` pointer into linear memory. Primitives smaller than 64 bits — `bool`, `char`, `i32`, `f32` — use their native WASM types.

### String Encoding

Strings are packed into a single `i64`:

```
bits 63-32: offset (u32, pointer into linear memory)
bits 31-0:  length (u32, byte count)
```

Pack: `(offset << 32) | length`
Unpack: `offset = value >>> 32`, `length = value & 0xFFFFFFFF`

String literal bytes are written to the WASM data section starting at offset 16. Literals are deduped by value. The heap base is aligned to 8 bytes after all string data.

### Memory Layout

```
Offset 0-15:     Reserved (WASM header)
Offset 16-N:     String literals (data section)
Offset align8(N): Heap base — objects grow upward
```

**Allocation strategy:**

- **With stdlib.wasm**: Calls `allocate(bytes: i32) -> i32` from the stdlib module. The impl uses dlmalloc.
- **Without stdlib**: Bump allocator that uses WASM global 0 as the heap pointer. Memory grows on demand via `memory.grow`.

Every heap object lives in 8-byte words.

### Heap Object Layout

#### Constructor (ADT variant)

```
Word 0:  i64  tag
Word 1:  i64  field[0]
Word 2:  i64  field[1]
...
```

The tag is computed via FNV-1a, with the formula `hash(name) ^ arity * FNV_PRIME`. Pattern matching compares tags with `i64.eq`.

**Field ordering**: Fields are stored in **lexicographic order by field name**. When a constructor is built with labeled arguments (such as `Cons(v: x, rest: xs)`), the args are sorted before storage. Field extraction via pattern matching uses the same sorted index. The list literal `[a, b, c]` desugars to `Cons` with positional args in that sorted order.

#### Record

Same layout as constructors:

```
Word 0:  i64  tag
Word 1:  i64  field[0]  (sorted by field name)
Word 2:  i64  field[1]
...
```

The tag is `fnv1a("rec" + sorted_field_names) ^ field_count * FNV_PRIME`. Fields are stored in **lexicographic order** by field name.

#### Closure

```
Word 0:  i64  funcref table index
Word 1:  i64  captured value[0]
Word 2:  i64  captured value[1]
...
```

Closures are called via `call_indirect`. The closure pointer goes in as the first argument, named `__env` and typed `i64`. The callee then loads captured values from `__env` at the right offsets.

### Value Packing

When a value gets stored in a heap object, it's first normalized to `i64`:

| Source Type | Pack to i64 | Unpack from i64 |
|---|---|---|
| `i64` | (no-op) | (no-op) |
| `i32` | `i64.extend_i32_s` | `i32.wrap_i64` |
| `f64` | `i64.reinterpret_f64` | `f64.reinterpret_i64` |
| `f32` | `i32.reinterpret_f32` then `i64.extend_i32_u` | `i32.wrap_i64` then `f32.reinterpret_i32` |
| `unit` | `i64.const 0` | (error) |

### Calling Convention

- **Internal functions**: Every labeled parameter and argument is sorted **lexicographically by label**. The function signature and the call sites use the same sorted order.
- **External functions (FFI)**: Parameters stay in **source (definition) order** to match the stdlib WASM ABI. Call arguments are matched to external parameters **by label**, with order ignored.
- A `unit` parameter generates no WASM parameter.
- A `unit`-returning function has an empty WASM result type.
- Tail calls use WASM `return_call`, except inside a `try` block.

### Indirect Calls (Closures)

Closure calls use `call_indirect` with an extended signature. The first parameter is always `__env: i64`, the closure heap pointer:

```
// Nexus: let f = fn (x: i64) -> i64 do ... end
// WASM type: (param i64 i64) (result i64)
//                   ^env ^x
```

The caller pushes `__env` first, then the normal args, and finally the table index as `i32` for `call_indirect`.

### Exception Model

Exceptions use two WASM globals (not WASM exception handling):

```wasm
(global $exn_flag  (mut i32) (i32.const 0))   ;; 0 = no exception
(global $exn_value (mut i64) (i64.const 0))   ;; exception object pointer
```

**Raise**: store the exception value, set the flag to 1, and return a dummy value.
**Catch**: after each statement, check `$exn_flag`. If set, jump to the catch handler, clear the flag, and bind `$exn_value` to the catch parameter.

### FFI Boundary

External functions use a different parameter encoding for strings and arrays. The packed `i64` form is split into a pointer and a length:

| Nexus Type | WASM Params (FFI) | Notes |
|---|---|---|
| `i32`, `bool`, `char` | 1x `i32` | Direct |
| `i64` | 1x `i64` | Direct |
| `f32` | 1x `f32` | Direct |
| `f64` | 1x `f64` | Direct |
| `string` | 2x `i32` (ptr, len) | Unpacked from packed i64 at boundary |
| `[| T |]` (array) | 2x `i32` (ptr, len) | Same unpacking as string |
| `%ByteBuffer`, opaque | 1x `i64` | Handle passed directly |
| `unit` | (none) | No parameter generated |

Parameter order: external function parameters keep **source (definition) order** rather than lexicographic order. The WASM function type signature has to match the stdlib export exactly. Call-site args are reordered to match by looking up each external parameter's label.

Return values use the same types as internal functions; strings return as packed `i64`.

### Module Structure

#### Exports

| Name | Kind | Condition |
|---|---|---|
| `main` | function | Always (entry point) |
| `wasi:cli/run@0.2.6#run` | function | Always (WASI run command) |
| `memory` | memory | If memory is defined or imported |

#### Imports

| Module | Name | Condition |
|---|---|---|
| `<module>.wasm` | `<wasm_name>` | Each `external` binding |
| stdlib module | `allocate` | If objects + stdlib present |

#### Custom Sections

| Section Name | Format | Purpose |
|---|---|---|
| `name` | WASM name section | Function/local names for debugging |
| `coverage` | Nexus coverage map | Source coverage instrumentation |
| `nx.bt.symbols` | Nexus symbol table | Backtrace symbol resolution |

#### Funcref Table

When the program uses closures or function references, a funcref table is emitted:

- Element type: `funcref`
- Size: number of unique function references
- Active initialization at offset 0
- Used by `call_indirect` for closure dispatch

## Building and Running

### Compile to WASM

```bash
nexus build program.nx                  # outputs out.wasm
nexus build program.nx -o output.wasm   # custom output path
```

The build step bundles deps automatically; `wasm-merge` must be available on `PATH`.

### Run with wasmtime

```bash
# Minimal (no capabilities)
wasmtime run -Scli out.wasm

# With network
wasmtime run -Scli -Shttp -Sinherit-network -Sallow-ip-name-lookup -Stcp out.wasm

# With filesystem preopens
wasmtime run -Scli --dir ./data out.wasm
```

### Inspect Capabilities

```bash
nexus build program.nx --explain-capabilities              # list capability names (default)
nexus build program.nx --explain-capabilities=wasmtime     # show wasmtime run command with flags
nexus build program.nx --explain-capabilities=none         # suppress output
nexus build program.nx --explain-capabilities-format=json  # machine-readable JSON
```
