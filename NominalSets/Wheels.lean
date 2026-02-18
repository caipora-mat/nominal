import Mathlib.Data.Set.Basic

-- not in mathlib o.O
@[simp, grind =, push]
theorem notMem_union {α : Type*} (x : α) (a b : Set α) :
  x ∉ a ∪ b ↔ x ∉ a ∧ x ∉ b := by rw [Set.mem_union, not_or]
