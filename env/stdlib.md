---
layout: default
title: Standard Library
---

# Standard Library

The standard library is the `std` package, rooted at `nxlib/stdlib/`. Import its modules with the `std:<name>` form:

```nexus
import { Console }, * as stdio from "std:stdio"
```

Bare paths (no colon) remain relative file imports. Each `std:<name>` resolves to `nxlib/stdlib/<name>.nx`; the WIT interface name is `nexus:std/<name>` (with `_` rewritten to `-`, e.g. `std:str` ↔ `nexus:std/string-ops`).

## I/O Caps

I/O is capability-gated via caps. Each cap has a `system_handler` that declares `require { PermX }`, propagating the permission to the caller when injected. Mock handlers without `require` need no runtime permissions.

### Console (`std:stdio`)

Requires `PermConsole`.

```nexus
cap Console do
  fn print(val: string) -> unit
  fn println(val: string) -> unit
  fn eprint(val: string) -> unit
  fn eprintln(val: string) -> unit
  fn read_line() -> string
  fn getchar() -> string
  fn read_bytes(n: i64) -> %ByteBuffer
end
```

```nexus
let main = fn () -> unit require { PermConsole } do
  inject stdio.system_handler do
    Console.println(val: "Hello")
  end
  return ()
end
```

### File System (`std:fs`)

Requires `PermFs`.

**Exception types:** `FileNotFound(path)`, `WriteError(path)`, `RemoveError(path)`. Exception group: `FsThrow = FileNotFound | WriteError | RemoveError`.

**Value types:**

```nexus
type Handle      = Handle(id: i64)                                   // linear file handle
type ReadResult  = ReadResult(content: string, handle: %Handle)
type WriteResult = WriteResult(ok: bool, handle: %Handle)
type PathResult  = PathResult(path: string, handle: %Handle)
```

**Direct-call helpers** (the two operations exported as plain functions; the rest live on the `Fs` cap):

```nexus
fn list_dir(path: string) -> [ string ] throws { FileNotFound }
fn is_file(path: string) -> bool
```

**Cap methods** (every other operation; reached via `inject`):

```nexus
cap Fs do
  // Query
  fn exists(path: string) -> bool
  fn is_file(path: string) -> bool
  fn list_dir(path: string) -> [ string ] throws { FileNotFound }
  fn read_to_string(path: string) -> string throws { FileNotFound }

  // Mutating
  fn write_string(path: string, content: string) -> unit throws { WriteError }
  fn append_string(path: string, content: string) -> unit throws { WriteError }
  fn remove_file(path: string) -> unit throws { RemoveError }
  fn create_dir_all(path: string) -> unit throws { WriteError }
  fn read_dir(path: string) -> %[ Handle ] throws { FileNotFound }

  // File-descriptor operations (consume-and-return pattern)
  fn open_read(path: string) -> %Handle throws { FileNotFound }
  fn open_write(path: string) -> %Handle throws { WriteError }
  fn open_append(path: string) -> %Handle throws { WriteError }
  fn read(handle: %Handle) -> ReadResult
  fn write(handle: %Handle, content: string) -> WriteResult
  fn handle_path(handle: %Handle) -> PathResult
  fn close(handle: %Handle) -> unit
end
```

The fd operations use a **consume-and-return** pattern: the linear handle is consumed and a fresh handle is returned in the result record, enabling stateless handlers.

```nexus
let %h = Fs.open_read(path: "data.txt")
let ReadResult(content: c, handle: %h2) = Fs.read(handle: %h)
Fs.close(handle: %h2)
```

### Network (`std:network`)

Requires `PermNet`.

**Exception types:** `RequestError(url)`, `BindError(addr)`, `ResponseError(msg)`. Exception group: `NetError = RequestError | BindError | ResponseError`.

**Value types:**

```nexus
type Header = Header(name: string, value: string)
type Response = Response(status: i64, headers: string, body: string)
opaque type Server = Server(id: i64)               // linear server handle
opaque type Request = Request(...)                 // linear request handle
opaque type RespondStream = RespondStream(...)     // linear streaming response handle
```

**Helper:**

```nexus
fn header(name: string, value: string) -> Header
```

**Cap methods:** all HTTP client and server operations are reached through the `Net` cap (no direct-call API is exported — code must `inject` a handler).

```nexus
cap Net do
  // HTTP client
  fn get(url: string) -> string throws { RequestError }
  fn request(method: string, url: string, headers: [ Header ], body: string)
    -> Response throws { RequestError }
  fn request_with_timeout(method: string, url: string, headers: [ Header ], body: string,
                          timeout_ms: i64) -> Response throws { RequestError }

  // HTTP server
  fn listen(addr: string) -> %Server throws { BindError }
  fn accept(server: &Server) -> %Request
  fn cancel_accept(server: &Server) -> bool
  fn respond(req: %Request, status: i64, body: string) -> unit throws { ResponseError }
  fn respond_with_headers(req: %Request, status: i64, headers: [ Header ], body: string)
    -> unit throws { ResponseError }

  // Streaming response
  fn respond_streaming_start(req: %Request, status: i64, headers: [ Header ])
    -> %RespondStream throws { ResponseError }
  fn respond_streaming_write(stream: &RespondStream, chunk: string) -> bool
  fn respond_streaming_finish(stream: %RespondStream) -> unit throws { ResponseError }

  fn stop(server: %Server) -> unit
end
```

### Random (`std:rand`)

Requires `PermRandom`.

```nexus
cap Random do
  fn next_i64() -> i64
  fn range(min: i64, max: i64) -> i64
  fn next_bool() -> bool
end
```

### Clock (`std:clock`)

Requires `PermClock`.

```nexus
cap Clock do
  fn sleep(ms: i64) -> unit
  fn now() -> i64
end
```

### Process (`std:proc`)

Requires `PermProc`.

**Types:**

```nexus
type ExecResult = ExecResult(exit_code: i64, stdout: string, stderr: string)
```

**Direct-call API:**

```nexus
fn argv() -> [ string ] require { PermProc }
```

**Cap methods:**

```nexus
cap Proc do
  fn exit(status: i64) -> unit
  fn argv() -> [ string ]
  fn exec(cmd: string, args: [ string ]) -> ExecResult
end
```

### Environment (`std:env`)

Requires `PermEnv`.

```nexus
cap Env do
  fn get(key: string) -> Option<string>
  fn set(key: string, value: string) -> unit
end
```

`Env.get` returns `None` when the variable is not set, avoiding exceptions for simple absence.

## Data Structures

### Option (`std:option`)

```nexus
type Option<T> = Some(val: T) | None

fn is_some<T>(opt: Option<T>) -> bool
fn is_none<T>(opt: Option<T>) -> bool
fn unwrap_or<T>(opt: Option<T>, default: T) -> T
fn map<T, U>(opt: Option<T>, f: (val: T) -> U) -> Option<U>
fn and_then<T, U>(opt: Option<T>, f: (val: T) -> Option<U>) -> Option<U>
fn or_else<T>(opt: Option<T>, other: Option<T>) -> Option<T>
fn unwrap<T>(opt: Option<T>) -> T throws { Exn }
fn expect<T>(opt: Option<T>, msg: string) -> T throws { Exn }
```

### List (`std:list`)

Immutable singly-linked list: `type List<T> = Nil | Cons(v: T, rest: List<T>)`.
`[ T ]` is an alias for `List<T>` with literal syntax sugar.

```nexus
type Partition<T> = Partition(matched: [ T ], rest: [ T ])

fn empty<T>() -> [ T ]
fn cons<T>(x: T, xs: [ T ]) -> [ T ]
fn is_empty<T>(xs: [ T ]) -> bool
fn length<T>(xs: [ T ]) -> i64
fn head<T>(xs: [ T ]) -> T
fn tail<T>(xs: [ T ]) -> [ T ]
fn last<T>(xs: [ T ]) -> T
fn reverse<T>(xs: [ T ]) -> [ T ]
fn concat<T>(xs: [ T ], ys: [ T ]) -> [ T ]
fn take<T>(xs: [ T ], n: i64) -> [ T ]
fn drop_n<T>(xs: [ T ], n: i64) -> [ T ]
fn nth<T>(xs: [ T ], n: i64) -> T
fn contains(xs: [ i64 ], val: i64) -> bool
fn fold_left<T, U>(xs: [ T ], init: U, f: (acc: U, val: T) -> U) -> U
fn map<T, U>(xs: [ T ], f: (val: T) -> U) -> [ U ]
fn map_rev<T, U>(xs: [ T ], f: (val: T) -> U) -> [ U ]
```

### Tuple (`std:tuple`)

```nexus
type Pair<A, B> = Pair(left: A, right: B)

fn fst<A, B>(p: Pair<A, B>) -> A
fn snd<A, B>(p: Pair<A, B>) -> B
```

Arrays use the built-in linear type `[| T |]`. Construction and indexing are language primitives (`[| e1, e2 |]`, `arr[i]`); there is no `std:array` module.

### HashMap (`std:hashmap`)

Open-addressed (linear-probing) hash map from `i64` keys to `i64` values, implemented over `std:runtime/collection`. The map is an opaque linear handle and must be `free`d.

```nexus
opaque type HashMap = HashMap(id: i64)  // linear -- must be freed
type Lookup = Found(value: i64) | Missing

fn empty() -> %HashMap
fn put(map: %HashMap, key: i64, value: i64) -> %HashMap
fn get(map: &HashMap, key: i64) -> Lookup
fn get_or(map: &HashMap, key: i64, default: i64) -> i64
fn contains_key(map: &HashMap, key: i64) -> bool
fn remove(map: %HashMap, key: i64) -> %HashMap
fn size(map: &HashMap) -> i64
fn keys(map: &HashMap) -> [ i64 ]
fn values(map: &HashMap) -> [ i64 ]
fn free(map: %HashMap) -> unit
```

### StringMap (`std:stringmap`)

Open-addressed (linear-probing) hash map from `string` keys to `i64` values, implemented over `std:runtime/collection`. The map is an opaque linear handle and must be `free`d.

```nexus
opaque type StringMap = StringMap(id: i64)  // linear -- must be freed
type Lookup = Found(value: i64) | Missing

fn empty() -> %StringMap
fn put(map: %StringMap, key: string, value: i64) -> %StringMap
fn get(map: &StringMap, key: string) -> Lookup
fn get_or(map: &StringMap, key: string, default: i64) -> i64
fn contains_key(map: &StringMap, key: string) -> bool
fn remove(map: %StringMap, key: string) -> %StringMap
fn size(map: &StringMap) -> i64
fn keys(map: &StringMap) -> [ string ]
fn values(map: &StringMap) -> [ i64 ]
fn free(map: %StringMap) -> unit
```

### ByteBuffer (`std:bytebuffer`)

Mutable byte buffer for binary data construction, implemented over a bump-arena-allocated header in linear memory. Uses opaque linear handles. Provides LEB128 encoding, little-endian integer writes, and raw byte/string/buffer append operations.

```nexus
opaque type ByteBuffer = ByteBuffer(id: i64)  // linear -- must be freed

fn empty() -> %ByteBuffer
fn push_byte(buf: %ByteBuffer, byte: i64) -> %ByteBuffer
fn push_i32_le(buf: %ByteBuffer, val: i64) -> %ByteBuffer
fn push_i64_le(buf: %ByteBuffer, val: i64) -> %ByteBuffer
fn push_uleb128(buf: %ByteBuffer, val: i64) -> %ByteBuffer
fn push_sleb128(buf: %ByteBuffer, val: i64) -> %ByteBuffer
fn push_string(buf: %ByteBuffer, s: string) -> %ByteBuffer
fn push_buf(dst: %ByteBuffer, src: &ByteBuffer) -> %ByteBuffer
fn length(buf: &ByteBuffer) -> i64
fn get_byte(buf: &ByteBuffer, idx: i64) -> i64
fn to_string(buf: &ByteBuffer) -> string
fn write_file(buf: &ByteBuffer, path: string) -> bool require { PermFs }
fn free(buf: %ByteBuffer) -> unit
```

All mutating operations consume the buffer and return a new handle (consume-and-return pattern).

## Utilities

### String (`std:str`)

```nexus
// Inspection
fn length(s: string) -> i64
fn contains(s: string, sub: string) -> bool
fn index_of(s: string, sub: string) -> i64
fn starts_with(s: string, prefix: string) -> bool
fn ends_with(s: string, suffix: string) -> bool
fn char_at(s: string, idx: i64) -> char
fn char_code(s: string, idx: i64) -> i64              // Unicode codepoint, -1 if OOB

// Transformation
fn substring(s: string, start: i64, len: i64) -> string
fn trim(s: string) -> string
fn to_upper(s: string) -> string
fn to_lower(s: string) -> string
fn replace(s: string, from_str: string, to_str: string) -> string
fn concat(a: string, b: string) -> string
fn repeat(s: string, n: i64) -> string
fn pad_left(s: string, width: i64, fill: string) -> string
fn pad_right(s: string, width: i64, fill: string) -> string
fn join(xs: [ string ], sep: string) -> string
fn split(s: string, sep: string) -> [ string ]

// Conversion
fn from_i64(val: i64) -> string
fn from_float(val: float) -> string
fn from_bool(val: bool) -> string
fn from_char(c: char) -> string
fn from_char_code(code: i64) -> string                // Unicode codepoint → string
fn parse_i64(s: string) -> Option<i64>
fn parse_f64(s: string) -> Option<f64>
fn to_f64(s: string) -> f64 throws { Exn }
```

### Math (`std:math`)

```nexus
fn abs(val: i64) -> i64
fn max(a: i64, b: i64) -> i64
fn min(a: i64, b: i64) -> i64
fn mod_i64(a: i64, b: i64) -> i64
fn abs_float(val: float) -> float
fn sqrt(val: float) -> float
fn floor(val: float) -> float
fn ceil(val: float) -> float
fn pow(base: float, exp: float) -> float
fn i64_to_float(val: i64) -> float
fn float_to_i64(val: float) -> i64
fn negate(val: bool) -> bool
```

### Result (`std:result`)

```nexus
type Result<T, E> = Ok(val: T) | Err(err: E)

fn is_ok<T, E>(res: Result<T, E>) -> bool
fn is_err<T, E>(res: Result<T, E>) -> bool
fn unwrap_or<T, E>(res: Result<T, E>, default: T) -> T
fn map<T, U, E>(res: Result<T, E>, f: (val: T) -> U) -> Result<U, E>
fn map_err<T, E, F>(res: Result<T, E>, f: (val: E) -> F) -> Result<T, F>
fn and_then<T, U, E>(res: Result<T, E>, f: (val: T) -> Result<U, E>) -> Result<U, E>
fn from_exn<T>(exn: Exn) -> Result<T, Exn>
fn to_exn<T>(res: Result<T, Exn>) -> T throws { Exn }
```

### Exception Utilities (`std:exn`)

```nexus
fn to_string(exn: Exn) -> string
fn backtrace(exn: Exn) -> [string]
```

`backtrace` returns call-stack frames (with source file and line info) captured at the throw point.

### Char (`std:char`)

Character classification functions for ASCII analysis:

```nexus
fn ord(c: char) -> i64
fn is_upper(c: char) -> bool
fn is_lower(c: char) -> bool
fn is_alpha(c: char) -> bool
fn is_digit(c: char) -> bool
fn is_alnum(c: char) -> bool
fn is_hex_digit(c: char) -> bool
fn is_whitespace(c: char) -> bool
fn is_ident_start(c: char) -> bool
fn is_ident_char(c: char) -> bool
fn is_newline(c: char) -> bool
fn digit_value(c: char) -> i64
fn hex_digit_value(c: char) -> i64
```

### Lazy (`std:lazy`)

Combinators for `@` thunk evaluation. Implemented in pure Nexus over `std:runtime/lazy`'s `lazy_spawn` / `lazy_join` dispatch primitives.

```nexus
fn race(a: i64, b: i64) -> i64
fn cancel(thunk: i64) -> unit
fn detach(thunk: i64) -> unit
fn force_all(tasks: [i64]) -> [i64]
```

| Function | Description |
|---|---|
| `race(a, b)` | Force two thunks in parallel, return the first to complete; loser discarded |
| `cancel(thunk)` | Consume a thunk without evaluating (satisfies linearity) |
| `detach(thunk)` | Fire-and-forget: start evaluation, don't wait for result |
| `force_all(tasks)` | Spawn all thunks in parallel, join results in order |

Note: functions use `i64` internally (all values are i64 at WASM level). The `@T` linearity is enforced at the call site by the typechecker.

### Core (`std:core`)

Legacy re-exports for backwards compatibility. Prefer `tuple.nx`, `list.nx`, `math.nx` for new code.

```nexus
type Pair<A, B> = Pair(left: A, right: B)
type Partition<T> = Partition(matched: [ T ], rest: [ T ])

fn fst<A, B>(p: Pair<A, B>) -> A
fn snd<A, B>(p: Pair<A, B>) -> B
fn negate(val: bool) -> bool
fn id<T>(val: T) -> T
```
