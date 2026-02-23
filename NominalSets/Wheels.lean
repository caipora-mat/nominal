import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Finite.Basic

/-!
# Utility Lemmas and Tactics

Small lemmas and tactics used throughout the nominal-sets library that are not
(yet) in Mathlib.

## Main definitions

* `pick_new a s` / `pick_new a s with h` — tactic: picks a fresh atom `a ∉ s`
  from an infinite type. Works with both `Finset` and finite `Set` arguments.

## Main results

* `notMem_union` — `x ∉ a ∪ b ↔ x ∉ a ∧ x ∉ b` (missing from Mathlib's `Set` API).
-/

@[simp, push, grind =]
theorem notMem_union {α : Type*} (x : α) (a b : Set α) :
  x ∉ a ∪ b ↔ x ∉ a ∧ x ∉ b := by rw [Set.mem_union, not_or]

/-! ### `pick_new` tactic

`pick_new a s` picks a fresh atom `a` not in `s`, introducing
`a : α` and `ha : a ∉ s` into the local context.

- `pick_new a s` — auto-names the hypothesis `aNew` (postfixing `New` to the identifier).
- `pick_new a s with h` — uses `h` as the explicit hypothesis name.

The tactic handles both `Finset` and finite `Set` arguments:
- If `s : Finset α`, uses `Finset.exists_notMem` directly.
- If `s : Set α` with a `Set.Finite s` hypothesis in context, uses `Set.Finite.exists_notMem`.

Requires `[Infinite α]`.

Usage:
```
pick_new a s            -- introduces: a : α, aNew : a ∉ s
pick_new a s with hab   -- introduces: a : α, hab : a ∉ s
```
-/

syntax "pick_new" ident term ("with" ident)? : tactic

macro_rules
  | `(tactic| pick_new $a $s with $h) =>
    `(tactic| first
      | obtain ⟨$a, $h⟩ := ($s : Finset _).exists_notMem
      | obtain ⟨$a, $h⟩ := (show Set.Finite $s by assumption).exists_notMem)
  | `(tactic| pick_new $a $s) =>
    let ah := Lean.mkIdent (Lean.Name.mkSimple (a.getId.toString ++ "New"))
    `(tactic| first
      | obtain ⟨$a, $ah⟩ := ($s : Finset _).exists_notMem
      | obtain ⟨$a, $ah⟩ := (show Set.Finite $s by assumption).exists_notMem)
