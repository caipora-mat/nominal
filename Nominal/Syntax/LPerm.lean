import Nominal.Core.Name

namespace Nominal

open Core

abbrev Swap (A : Type*) := A × A
abbrev LPerm (A : Type*) := List (Swap A)

open Equiv

section

variable {𝔸 : Type*} [Name 𝔸]

def swapApply : Swap 𝔸 → 𝔸 → 𝔸
  | (a, b), c => if c = a then b
                   else if c = b then a
                     else c

def LPermApply : LPerm 𝔸 -> 𝔸 -> 𝔸
  | [], c => c
  | s :: sl, c => LPermApply sl (swapApply s c)


/- lemmas -/

/-- Swapping (a, b) is the same as swapping (b, a). -/
lemma swapApply_symm (a b : 𝔸) : swapApply (a, b) = swapApply (b, a) := by
  ext c
  by_cases h₁ : c = a
  · subst h₁
    simp [swapApply, eq_comm]
  · by_cases h₂ : c = b
    · subst h₂
      simp [swapApply, h₁]
    · simp [swapApply, h₁, h₂]

/-- Applying a singleton list permutation reduces to a single swap. -/
@[simp]
lemma LPermApply_singleton (s : Swap 𝔸) : LPermApply [s] = swapApply s := by
  ext a
  simp [LPermApply]

/-- Applying a swap twice yields the original value (swaps are involutions). -/
@[simp]
lemma swapApply_involutive (s : Swap 𝔸) (a : 𝔸) : swapApply s (swapApply s a) = a := by
  simp [swapApply]
  rcases s with ⟨x, y⟩
  by_cases h₁ : a = x
  · subst h₁
    simp
  · by_cases h₂ : a = y
    · subst h₂
      simp [h₁]
    · simp [h₁, h₂]

/-- Swapping a name with itself is the identity. -/
@[simp]
lemma swapApply_self (a c : 𝔸) : swapApply (a, a) c = c := by
   by_cases h : c = a <;> simp [swapApply, h]

/-- Applying swap (a, b) to a yields b. -/
@[simp]
lemma swapApply_left (a b : 𝔸) : swapApply (a, b) a = b := by
  simp [swapApply]

/-- Applying swap (a, b) to b yields a. -/
@[simp]
lemma swapApply_right (a b : 𝔸) : swapApply (a, b) b = a := by
  simp [swapApply]

/-- A swap leaves names other than a and b unchanged. -/
lemma swapApply_other (a b c : 𝔸) (ha : c ≠ a) (hb : c ≠ b) : swapApply (a, b) c = c := by
  simp only [swapApply]
  split
  · exfalso
    trivial
  · trivial

/-- Swap application is injective (follows from involutivity). -/
lemma swapApply_injective (s : Swap 𝔸) : Function.Injective (swapApply s) := by
  intro a1 a2 h
  have h' := congrArg (swapApply s) h
  simp [swapApply_involutive] at h'
  trivial
  
/-- Swap application is surjective (the swap itself provides preimages). -/
lemma swapApply_surjective (s : Swap 𝔸) : Function.Surjective (swapApply s) := by
  intro y
  use (swapApply s y)
  rw [swapApply_involutive]

/-- Applying the empty permutation is the identity. -/
@[simp]
lemma LPermApply_nil (c : 𝔸) : LPermApply [] c = c := by
  simp [LPermApply]

/-- Applying a cons permutation unfolds to applying the head swap then the tail. -/
@[simp]
lemma LPermApply_cons (s : Swap 𝔸) (p : LPerm 𝔸) (a : 𝔸) :
    LPermApply (s :: p) a = LPermApply p (swapApply s a) := by
  simp [LPermApply]

/-- Applying concatenated permutations is the composition of their applications. -/
lemma LPermApply_append (p q : LPerm 𝔸) (a : 𝔸) :
    LPermApply (p ++ q) a = LPermApply q (LPermApply p a) := by
  induction p generalizing a with
  | nil => simp
  | cons x xs ih =>
    rw [List.cons_append]
    rw [LPermApply_cons]
    rw [ih]
    rw [LPermApply_cons]

/-- Left inverse: reverse · p = id -/
lemma LPermApply_reverse_left (p : LPerm 𝔸) (a : 𝔸) :
    LPermApply (List.reverse p) (LPermApply p a) = a := by
  induction p generalizing a with
  | nil => simp
  | cons x xs ih =>
    rw [LPermApply_cons]
    simp [List.reverse_cons, LPermApply_append, ih]

/-- Right inverse: p · reverse = id -/
lemma LPermApply_reverse_right (p : LPerm 𝔸) (a : 𝔸) :
    LPermApply p (LPermApply (List.reverse p) a) = a := by
  have h := LPermApply_reverse_left (List.reverse p) a
  simp only [List.reverse_reverse] at h
  exact h

/-- List permutation application is injective (follows from reverse being its inverse). -/
lemma LPermApply_injective (p : LPerm 𝔸) : Function.Injective (LPermApply p) := by
  intro a1 a2 h
  have h' := congrArg (LPermApply p.reverse) h
  simp [LPermApply_reverse_left] at h'
  trivial

/-- List permutation application is surjective (the reverse provides preimages). -/
lemma LPermApply_surjective (p : LPerm 𝔸) : Function.Surjective (LPermApply p) := by
  intro y
  use (LPermApply p.reverse y)
  have := LPermApply_reverse_left (p := p.reverse) (a := y)
  simpa [List.reverse_reverse]

lemma LPermApply_eq_self_iff_eq_reverse_apply (a : 𝔸) (π : LPerm 𝔸) :
    LPermApply π a = a ↔ a = LPermApply (List.reverse π) a := by
  constructor
  · intro h
    have h := congrArg (LPermApply π.reverse) h
    simp [LPermApply_reverse_left] at h
    trivial
  · intro h
    have h := congrArg (LPermApply π) h
    simp [LPermApply_reverse_right] at h
    trivial

/-- Swap-conjugation: applying `π` after a swap `(b, a)` is the same as applying the swap of
    the permuted atoms `(π b, π a)` after `π`. -/
lemma LPermApply_swap_conjugate (π : LPerm 𝔸) (a b c : 𝔸) :
    LPermApply π (swapApply (b, a) c) =
      swapApply (LPermApply π b, LPermApply π a) (LPermApply π c) := by
  by_cases hcb : c = b
  · subst hcb
    rw [swapApply_left, swapApply_left]
  · by_cases hca : c = a
    · subst hca
      rw [swapApply_right, swapApply_right]
    · have hπcb : LPermApply π c ≠ LPermApply π b := by
        intro heq
        exact hcb (LPermApply_injective π heq)
      have hπca : LPermApply π c ≠ LPermApply π a := by
        intro heq
        exact hca (LPermApply_injective π heq)
      rw [swapApply_other _ _ _ hcb hca,
          swapApply_other _ _ _ hπcb hπca]

end

end Nominal
