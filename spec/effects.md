---
layout: default
title: Checked Exceptions and Capabilities
---

# Checked Exceptions and Capabilities

A Nexus function signature splits two concerns. **Caps** name what the function needs from its environment. **Checked exceptions** name what it may throw. The split sits at the core of the [design thesis](../../design#why-capabilities-not-effects). Each dep and side effect lands in the signature where you can see it.

> **Terminology note.** Some papers call the `require` clause a *coeffect*. The term fits, since it tracks environmental needs (the dual of effects). Here we use *capability*. The Nexus form is row-polymorphic, discharged by `inject`, and shows up as an annotation on a function signature. That structure differs from the coeffect calculi of Petricek and others, which use semiring-indexed annotations on each variable binding.

## Function Signature Shape

```nexus
fn (args...) -> Ret require { Capabilities } throws { Exceptions }
```

Both clauses are optional. Omitted means empty row (pure function with no requirements).

```nexus
let pure = fn (x: i64) -> i64 do return x + 1 end

let greet = fn (msg: string) -> unit require { Console } do
  Console.println(val: msg)
  return ()
end

let risky = fn () -> unit throws { Exn } do
  throw RuntimeError(val: "oops")
end
```

## Checked Exceptions

The one builtin throws type is `Exn`. A `try/catch` block clears `Exn` from the protected code:

```nexus
exception NotFound(msg: string)

let search = fn (key: string) -> string throws { Exn } do
  throw NotFound(msg: key)
end

let main = fn () -> unit do
  try
    let _ = search(key: "missing")
  catch e ->
    match e do
      | NotFound(msg: m) -> ()
      | _ -> ()
    end
  end
  return ()
end
```

Each new exception extends the builtin `Exn` type:

```nexus
export exception PermissionDenied(msg: string, code: i64)
```

`throw` is an expression that unwinds straight to the nearest `catch`. Every I/O capability goes through the cap system instead of through throws.

## Capabilities

A `cap` defines an interface. The interface is a set of function signatures the environment has to supply:

```nexus
export cap Logger do
  fn info(msg: string) -> unit
  fn warn(msg: string) -> unit
end
```

When a function calls `Logger.info(...)`, it must list `Logger` in its `require` row.

Cap methods can declare their own throws and caps:

```nexus
export cap Fs do
  fn open_read(path: string) -> %Handle throws { Exn }
  fn read(handle: %Handle) -> { content: string, handle: %Handle }
  fn close(handle: %Handle) -> unit
end
```

## Handlers

A handler is a value that implements every method on a cap.

```nexus
let console_logger = handler Logger require { Console } do
  fn info(msg: string) -> unit do
    Console.println(val: "[INFO] " ++ msg)
    return ()
  end
  fn warn(msg: string) -> unit do
    Console.println(val: "[WARN] " ++ msg)
    return ()
  end
end

let mock_logger = handler Logger do
  fn info(msg: string) -> unit do return () end
  fn warn(msg: string) -> unit do return () end
end
```

Handler `require { ... }` is a **precondition on every `inject` site**. A handler value with `require { Console }` may be injected only inside a scope that already supplies `Console`. The enclosing function must either declare `require { Console }` or sit under a surrounding `Console` injection. The inject does **not** retroactively add `Console` to the caller's requirements; the caller must already hold it.

Formally, [T-Inject](./type-system-formal#T-Inject) makes this precise. The handler's require row $\rho_i$ must satisfy $\rho_i \subseteq \rho_q$, where $\rho_q$ is the ambient row at the inject site.

An opposite reading is propagation, where injecting a `require {Console}` handler would push `Console` upward into the caller's signature. We weighed that path and rejected it. A function could then reach caps its declared signature does not advertise, and cap containment as an audit property would break.

The type checker enforces:
- Handler methods must match cap signatures exactly
- All cap methods must be implemented (exhaustive)
- Handler method bodies inherit the handler's `require` clause
- At each `inject`, the handler's `require` must be a subset of the surrounding scope's ambient row

## Inject

`inject` hands handler values to a lexical scope and clears the matching `require` entries:

```nexus
inject stdio.system_handler do
  inject console_logger do
    program()  // program's Logger + Console requirements satisfied
  end
end
```

Rules:
- `inject` must reduce requirements -- injecting an unused handler is a type error
- Multiple handlers can be injected in a single `inject` statement: `inject h1, h2 do ... end`
- A handler's own `require` row must be satisfied by the ambient row at the inject site (it does **not** propagate upward to the caller's signature)

## Exception Groups

An exception group lets you catch several related exceptions with one pattern. See [Exception Groups](../exception-groups) for the full reference.

```nexus
exception NotFound(path: string)
exception PermDenied(path: string)
exception group IOError = NotFound | PermDenied

let safe_read = fn (path: string) -> string require { Fs } do
  try
    return Fs.read_to_string(path: path)
  catch
    | IOError -> return ""
  end
end
```

## Main Constraints

A few rules apply only to `main`:

- Signature: `() -> unit`
- `throws` must be a **closed** row of named exceptions (or empty); the runtime entry wrapper catches any declared variant, so they need not be handled internally. Open rows and free type variables are rejected.
- `require` may contain any subset of runtime permissions: `{ PermFs, PermNet, PermConsole, PermRandom, PermClock, PermProc, PermEnv }`

```nexus
let main = fn () -> unit require { PermConsole } do
  inject stdio.system_handler do
    Console.println(val: "Hello")
  end
  return ()
end
```

## Permission mapping

Runtime perms (`PermFs`, `PermNet`, and the rest) are caps that map to WASI caps. They sit between the type system and the runtime sandbox. See [WASM and WASI](../../env/wasm) for the full table.

## Row typing

Throws and cap rows are checked by row unification, with no subtyping. Open rows use tail variables for polymorphism:

```nexus
// This function is polymorphic over additional requirements
let log_and_do = fn <R>(f: () -> unit require { Logger | R }) -> unit require { Logger | R } do
  Logger.info(msg: "starting")
  f()
  return ()
end
```

Compatibility is structural. Two rows unify when they list the same entries, in any order.
