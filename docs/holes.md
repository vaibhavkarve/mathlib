# Hole commands

Both VS Code and emacs support integration for 'hole commands'.

In VS Code, if you enter `{! !}`, a small light bulb symbol will appear, and
clicking on it gives a drop down menu of available hole commands. Running one
of these will replace the `{! !}` with whatever text that hole command provides.

In emacs, you can do something similar with `C-c SPC`.

Many of these commands are available whenever `tactic.core` is imported.
Commands that require additional imports are noted below.
All should be available with `import tactic`.

## eqn_stub

[[source]](../src/tactic/core.lean)

Invoking hole command `Equations Stub` ("Generate a list of equations for a recursive definition") in

```lean
meta def foo : {! expr → tactic unit !} -- `:=` is omitted
```

produces:

```lean
meta def foo : expr → tactic unit
| (expr.var a) := _
| (expr.sort a) := _
| (expr.const a a_1) := _
| (expr.mvar a a_1 a_2) := _
| (expr.local_const a a_1 a_2 a_3) := _
| (expr.app a a_1) := _
| (expr.lam a a_1 a_2 a_3) := _
| (expr.pi a a_1 a_2 a_3) := _
| (expr.elet a a_1 a_2 a_3) := _
| (expr.macro a a_1) := _
```

A similar result can be obtained by invoking `Equations Stub` on the following:

```lean
meta def foo : expr → tactic unit := -- do not forget to write `:=`!!
{! !}
```

```lean
meta def foo : expr → tactic unit := -- don't forget to erase `:=`!!
| (expr.var a) := _
| (expr.sort a) := _
| (expr.const a a_1) := _
| (expr.mvar a a_1 a_2) := _
| (expr.local_const a a_1 a_2 a_3) := _
| (expr.app a a_1) := _
| (expr.lam a a_1 a_2 a_3) := _
| (expr.pi a a_1 a_2 a_3) := _
| (expr.elet a a_1 a_2 a_3) := _
| (expr.macro a a_1) := _
```

## match_stub

[[source]](../src/tactic/core.lean)

Invoking hole command `Match Stub` ("Generate a list of equations for a `match` expression") in

```lean
meta def foo (e : expr) : tactic unit :=
{! e !}
```

produces:

```lean
meta def foo (e : expr) : tactic unit :=
match e with
| (expr.var a) := _
| (expr.sort a) := _
| (expr.const a a_1) := _
| (expr.mvar a a_1 a_2) := _
| (expr.local_const a a_1 a_2 a_3) := _
| (expr.app a a_1) := _
| (expr.lam a a_1 a_2 a_3) := _
| (expr.pi a a_1 a_2 a_3) := _
| (expr.elet a a_1 a_2 a_3) := _
| (expr.macro a a_1) := _
end
```

## instance_stub

[[source]](../src/tactic/core.lean)

Invoking the hole command `Instance Stub` ("Generate a skeleton for the structure under construction") on

```lean
instance : monad id :=
{! !}
```

produces

```lean
instance : monad id :=
{ map := _,
  map_const := _,
  pure := _,
  seq := _,
  seq_left := _,
  seq_right := _,
  bind := _ }
```

## tidy

[[source]](../src/tactic/tidy.lean) (Requires `import tactic.tidy`.)

Invoking the hole command `tidy` ("Use `tidy` to complete the goal") runs the tactic of the same name,
replacing the hole with the tactic script `tidy` produces.

## library_search

[[source]](../src/tactic/suggest.lean) (Requires `import tactic.suggest`.)

Invoking the hole command `library_search` ("Use `library_search` to complete the goal") calls the tactic `library_search` to produce a proof term with the type of the hole.

Running it on

```lean
example : 0 < 1 :=
{!!}
```

produces

```lean
example : 0 < 1 :=
nat.one_pos
```

## lint

[[source]](../src/tactic/lint.lean) (Requires `import tactic.lint`.)

Invoking the hole command `lint` ("Find common mistakes in current file") will print text that
indicates mistakes made in the file above the command. It is equivalent to copying and pasting the
output of `#lint`. On large files, it may take some time before the output appears.

## list_constructors

[[source]](../src/tactic/core.lean)

When the type of the hole is an inductive type, invoking `list_constructors` ("Show the list of constructors of the expected type") will produce a list of all the constructors of that inductive type.

When used in the following hole:

```lean
def foo : ℤ ⊕ ℕ :=
{! !}
```

the command will produce:

```lean
def foo : ℤ ⊕ ℕ :=
{! sum.inl, sum.inr !}
```

and will display:

```lean
sum.inl : ℤ → ℤ ⊕ ℕ

sum.inr : ℕ → ℤ ⊕ ℕ
```
