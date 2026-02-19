import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Finite.Basic

-- not in mathlib o.O
@[simp, grind =, push]
theorem notMem_union {α : Type*} (x : α) (a b : Set α) :
  x ∉ a ∪ b ↔ x ∉ a ∧ x ∉ b := by rw [Set.mem_union, not_or]

/-! ### `pick_fresh` tactic

`pick_fresh a s` picks a fresh atom `a` not in the `Finset` `s`, introducing
`a : α` and a hypothesis `ah : a ∉ s` into the local context.

Usage:
```
pick_fresh a s
-- introduces: a : α, ah : a ∉ s
```
-/

macro "pick_new" a:ident s:term : tactic =>
  let ah := Lean.mkIdent (Lean.Name.mkSimple ("h" ++ a.getId.toString))
  `(tactic| obtain ⟨$a, $ah⟩ := ($s : Finset _).exists_notMem)
