-- import NominalSets.FinitePerm.Basic

-- /-!
-- # Properties of Swaps (Transpositions)

-- This file collects basic properties of transpositions (`Equiv.swap`) that are
-- useful in the nominal sets development.

-- ## Main results

-- * `Equiv.Perm.swap_equivariant` — swap is equivariant with respect to the
--   conjugation action: `π * swap a b * π⁻¹ = swap (π a) (π b)`.
-- * `FinitePerm.swap_equivariant` — the same result for finite permutations.
-- -/

-- open Equiv

-- namespace Equiv.Perm

-- variable {α : Type*} [DecidableEq α]

-- #check swap

-- /-- **Equivariance of swap**: conjugating a transposition by a permutation
-- yields the transposition of the images. That is,
-- `π * swap a b * π⁻¹ = swap (π a) (π b)`. -/
-- theorem swap_equivariant (π : Perm α) (a b : α) :
--     π * swap a b * π⁻¹ = swap (π a) (π b) := by
--   ext x
--   simp [Perm.mul_apply, swap_apply_def]
--   split <;> simp_all

-- end Equiv.Perm

-- namespace FinitePerm

-- open Equiv

-- variable {α : Type*} [DecidableEq α]

-- /-- Equivariance of swap for finite permutations: if `π` is a finite
-- permutation, then `π * swap a b * π⁻¹ = swap (π a) (π b)`. -/
-- theorem swap_equivariant (π : FinitePerm α) (a b : α) :
--     π * ⟨swap a b, swap_finite a b⟩ * π⁻¹ =
--       ⟨swap (π.val a) (π.val b), swap_finite (π.val a) (π.val b)⟩ := by
--   ext x
--   simp [Subgroup.coe_mul, Subgroup.coe_inv, Perm.mul_apply, swap_apply_def]
--   split <;> simp_all

-- end FinitePerm
