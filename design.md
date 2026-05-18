---
layout: default
title: Design
---

# Design

Nexus rests on one bet: **LLMs are good at code you can read on the page, and bad at code that depends on what's off the page.** GC, implicit casts, ambient I/O, hidden control flow — these are the spots where LLM code goes wrong and where humans miss it on review. Nexus swaps each one for a form you can see in the source.

## On the page vs off it

| Off the page (cut) | On the page (Nexus form) |
|---|---|
| Implicit resource cleanup (GC, finalizers) | `%` linear types — used once |
| Hidden aliasing | `&` borrow — a read-only view |
| Ambient I/O | `require { PermNet }` — stated up front |
| Implicit control transfer (continuations) | `try/catch` — old-school unwind |
| Positional arguments | `add(a: 1, b: 2)` — labels required |
| Brace-matching (off-by-one) | `do ... end` — keyword blocks |
| Implicit scope termination | `if ... then ... end`, `match ... do ... end` |

The rule is plain. If a construct sends you elsewhere to know what happens here, swap it for one that doesn't.

## Why caps, and why not effects

Most of the effect-system literature centers on *algebraic effects*. A function performs an effect op, and a handler intercepts the op through a delimited continuation. The handler picks whether and how to resume the suspended work. That model is powerful, but it lives off the page. At the call site, `Logger.info(msg: x)` says nothing about control flow. The handler might resume, abort, restart, or fire the continuation many times over.

Nexus drops continuations altogether. Instead:

- A **cap** spells out a stateless interface, much like a trait in other languages.
- A **handler** is a plain value that implements the cap's methods.
- **`inject`** hands a handler to a lexical scope. Read it as dependency injection, rather than as algebraic effect handling.
- **Cap calls** are direct, statically resolved function calls. `Logger.info(msg: x)` runs a function. It returns. There's no hidden jump.

```nexus
cap Logger do
  fn info(msg: string) -> unit
end

let console_logger = handler Logger require { Console } do
  fn info(msg: string) -> unit do
    Console.println(val: "[INFO] " ++ msg)
    return ()
  end
end

let main = fn () -> unit require { PermConsole } do
  inject stdio.system_handler, console_logger do
    Logger.info(msg: "starting")
  end
  return ()
end
```

The trade is plain. You give up handler expressiveness so that each call site means just what it says.

## Linear types track resources on the page

GCs and finalizers live off the page. A resource goes away "sometime later," through a step you can't see. Nexus puts the lifecycle in the syntax through the `%` sigil:

```nexus
let %h = Fs.open_read(path: path)   // acquire
let %r = Fs.read(handle: %h)    // consume %h, get new handle back
match %r do
  | { content: c, handle: %h2 } ->
    Fs.close(handle: %h2)     // release
end
```

The compiler holds you to once-and-only-once use. Skip a consume, use it twice, or drop it with `_`, and the code fails to build. There's no GC, no finalizer, and no quiet drop.

## Borrowing puts aliasing on the page

Hidden aliasing chews up code from humans and LLMs alike. The `&` sigil makes every alias show up at the use site:

```nexus
let server = Net.listen(addr: addr)
let req = Net.accept(server: &server)  // &server: borrow, not consume
let method = request_method(req: &req) // &req: borrow, not consume
let _ = Net.respond(req: req, ...)     // consume req
Net.stop(server: server)               // consume server
```

Every read-without-consume gets marked in the syntax. There's no quiet refcount, no shared pointer, and no automatic copy.

## Labeled args and keyword blocks

Positional arguments push you to the function signature to learn what each slot means. Brace-delimited blocks push you to count braces to find the end. Nexus drops both:

```nexus
// Every argument is self-documenting
let result = request(
  method: "POST",
  url: "https://api.example.com",
  headers: headers,
  body: payload
)

// Every block has an unambiguous terminator
if condition then
  // ...
end
```

## Cap-based security

Ambient authority — where any function can read files, hit the network, or read the clock — lives entirely off the page. The `require` clause pins the security surface to every function boundary:

```nexus
let main = fn () -> unit require { PermNet, PermConsole } do
  inject net_handler, stdio_handler do
    let body = Net.get(url: "https://example.com")
    Console.println(val: body)
  end
  return ()
end
```

`require { PermNet, PermConsole }` is checked at build time and enforced again by the WASI runtime. A function may do network I/O only when it declares `PermNet` and a handler for `Net` is in scope. See [WASM and WASI](../env/wasm) for how perms map to caps.
