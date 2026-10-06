import Package.Foundations.Permutation
import Mathlib.Algebra.Group.Subgroup.Map

/-!
Research probe, 2026-10-06: natural generalizations of the Package foundation.
Checked against Lean/Mathlib v4.34.1 (Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612).
This file is standalone research evidence, outside production Package imports.
See docs/research/2026-10-06-foundation-generalizations.md for status and limits.
-/

open NominalPackage

universe u v
namespace Probe
variable {A : Type u} {B : Type v}

theorem moved_permCongr (e : A ≃ B) (π : Equiv.Perm A) :
    {b | e.permCongr π b ≠ b} = e '' {a | π a ≠ a} := by
  ext b
  constructor
  · intro hb
    refine ⟨e.symm b, ?_, e.apply_symm_apply b⟩
    intro h
    exact hb (by simp only [Equiv.permCongr_apply, h, e.apply_symm_apply])
  · rintro ⟨a, ha, rfl⟩ h
    apply ha
    apply e.injective
    simpa only [Equiv.permCongr_apply, e.symm_apply_apply] using h

theorem permSubgroup_map (e : A ≃ B) :
    (permSubgroup A).map e.permCongrHom.toMonoidHom = permSubgroup B := by
  ext π
  rw [Subgroup.mem_map_equiv]
  change ({a | e.symm.permCongr π a ≠ a} : Set A).Finite ↔
    ({b | π b ≠ b} : Set B).Finite
  rw [moved_permCongr]
  exact Set.finite_image_iff e.symm.injective.injOn

def permCongr (e : A ≃ B) : Perm A ≃* Perm B :=
  (e.permCongrHom.subgroupMap (permSubgroup A)).trans
    (MulEquiv.subgroupCongr (permSubgroup_map e))

theorem permCongr_apply (e : A ≃ B) (π : Perm A) (b : B) :
    permCongr e π b = e (π (e.symm b)) := rfl

theorem moved_transport (e : A ≃ B) (π : Perm A) :
    (permCongr e π).moved = e '' π.moved := moved_permCongr e π.val

theorem transport_swap [DecidableEq A] [DecidableEq B] (e : A ≃ B) (a b : A) :
    permCongr e (Perm.swap a b) = Perm.swap (e a) (e b) := by
  ext c
  change e (Equiv.swap a b (e.symm c)) = Equiv.swap (e a) (e b) c
  simpa only [e.apply_symm_apply] using e.injective.map_swap a b (e.symm c)

theorem existing_moved_conj (π σ : Perm A) :
    (π * σ * π⁻¹).moved = π '' σ.moved := by
  exact moved_permCongr π.toEquiv σ.toEquiv

#print axioms permCongr
#print axioms moved_transport
#print axioms transport_swap
#print axioms existing_moved_conj
set_option pp.universes true in
#check @permCongr
end Probe
