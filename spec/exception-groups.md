---
layout: default
title: Exception Groups
---

# Exception Groups

An exception group is a named set of exception types. A `catch` arm naming a group expands to match every member.

## Declaration

```nexus
exception NotFound(path: string)
exception PermDenied(path: string, code: i64)

exception group IOError = NotFound | PermDenied
```

Declare a group with `exception group Name = Member1 | Member2 | ...`. Each member has to be an exception that was declared earlier. The `export` modifier opens the group to importers.

## Structured Exceptions

Each exception carries typed fields rather than a pre-formatted string. That shape lets you handle errors either case by case or in bulk:

```nexus
exception UnexpectedToken(expected: string, got: string, span: Span)
exception MissingMain

exception group ParseError = UnexpectedToken | MissingMain
```

Zero-field exceptions (like `MissingMain`) omit parentheses in both declaration and pattern matching.

## Catching Groups

Catching a group name expands to match every member:

```nexus
try
  parse(tokens: tokens)
catch
  | ParseError ->
    // catches both UnexpectedToken and MissingMain
    Console.eprintln(val: "parse failed")
end
```

The form is sugar; the compiler expands `| ParseError ->` into one arm per member.

In the formal type system ([type-system-formal.md](../type-system-formal)), throws-rows are variant-precise. Each member of a group becomes its own row entry. A group catch subtracts the union of its member constructors from the row. The formal rules never see the group at all — only the expanded constructor list shows up (see `caughtVariants` and `members` in T-TryCatch).

## Catching Specific Exceptions

For tighter handling, match each exception type and destructure its fields:

```nexus
try
  compile(src: src)
catch
  | UnexpectedToken(expected: e, got: g, span: sp) ->
    Console.eprintln(val: "expected " ++ e ++ ", got " ++ g)
  | TypeMismatch(func_name: f, detail: d, span: sp) ->
    Console.eprintln(val: "in " ++ f ++ ": " ++ d)
  | MissingMain ->
    Console.eprintln(val: "no main function")
end
```

You can mix specific arms with group arms. The compiler checks each arm on its own.

## Multi-Arm Catch

The `catch` clause supports two forms:

```nexus
// Legacy: single variable binding
try body catch e -> handle(e: e) end

// Multi-arm: pattern matching on exception constructors
try
  body
catch
  | NotFound(msg: m) -> handle_missing(m: m)
  | PermDenied(msg: m) -> handle_perm(m: m)
  | IOError -> handle_generic()
end
```

Multi-arm catch desugars to `catch __exn -> match __exn do ... end` during compilation.

## Group Composition

A group lists individual exceptions only; one group cannot reference another. For a "super-group" spanning several phases, name every member directly:

```nexus
exception group CompileError =
  UnexpectedToken | MissingMain
  | TypeMismatch
  | SymbolNotFound
```

A group is expanded at the catch site, so there's no nesting at runtime.

---

See also: [Checked Exceptions and Capabilities](../effects), [Type System — Formal Rules](../type-system-formal), [Syntax](../syntax)
