import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Finite.Basic

/-!
# Utility Lemmas and Tactics

Small lemmas and tactics used throughout the nominal-sets library that are not
(yet) in Mathlib.

## Main definitions

* `pick_new a s` — tactic macro: picks a fresh atom `a ∉ s` from an infinite type,
  introducing `a : α` and `ha : a ∉ s` into the local context.

## Main results

* `notMem_union` — `x ∉ a ∪ b ↔ x ∉ a ∧ x ∉ b` (missing from Mathlib's `Set` API).
-/

@[simp, grind =, push]
theorem notMem_union {α : Type*} (x : α) (a b : Set α) :
  x ∉ a ∪ b ↔ x ∉ a ∧ x ∉ b := by rw [Set.mem_union, not_or]

/-! ### `pick_new` tactic

`pick_new a s` picks a fresh atom `a` not in the `Finset` `s`, introducing
`a : α` and `ha : a ∉ s` into the local context.

Usage:
```
pick_new a s
-- introduces: a : α, ha : a ∉ s
```
-/

macro "pick_new" a:ident s:term : tactic =>
  let ah := Lean.mkIdent (Lean.Name.mkSimple ("h" ++ a.getId.toString))
  `(tactic| obtain ⟨$a, $ah⟩ := ($s : Finset _).exists_notMem)
