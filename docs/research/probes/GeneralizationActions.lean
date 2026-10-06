import Package.Foundations.Action
import Mathlib.GroupTheory.GroupAction.FixingSubgroup
import Mathlib.Algebra.Group.Submonoid.BigOperators

/-!
Research probe, 2026-10-06: natural generalizations of the Package foundation.
Checked against Lean/Mathlib v4.34.1 (Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612).
This file is standalone research evidence, outside production Package imports.
See docs/research/2026-10-06-foundation-generalizations.md for status and limits.
-/

open NominalPackage

universe u v w z

namespace Probe

section Generation
variable {A : Type u} [DecidableEq A]

def outsideSwaps (S : Set A) : Set (Perm A) :=
  {π | ∃ a b, a ∉ S ∧ b ∉ S ∧ π = Perm.swap a b}

theorem fixingSubgroup_eq_closure (S : Set A) :
    fixingSubgroup (Perm A) S = Subgroup.closure (outsideSwaps S) := by
  apply le_antisymm
  · intro π hπ
    obtain ⟨l, hl, hs⟩ := Perm.swap_factorization_avoiding π S
      ((mem_fixingSubgroup_iff (Perm A)).mp hπ)
    rw [← hl]
    apply list_prod_mem
    intro σ hσ
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := List.mem_map.mp hσ
    obtain ⟨_, ha, hb⟩ := hs (a, b) hab
    exact Subgroup.subset_closure ⟨a, b, ha, hb, rfl⟩
  · apply (Subgroup.closure_le _).2
    rintro π ⟨a, b, ha, hb, rfl⟩
    apply (mem_fixingSubgroup_iff (Perm A)).mpr
    intro c hc
    exact Perm.swap_apply_of_ne_of_ne (fun h => ha (h ▸ hc)) (fun h => hb (h ▸ hc))

theorem fixingSubgroup_le_iff (S : Set A) (H : Subgroup (Perm A)) :
    fixingSubgroup (Perm A) S ≤ H ↔
      ∀ a b : A, a ∉ S → b ∉ S → Perm.swap a b ∈ H := by
  rw [fixingSubgroup_eq_closure, Subgroup.closure_le]
  constructor
  · intro h a b ha hb
    exact h ⟨a, b, ha, hb, rfl⟩
  · rintro h _ ⟨a, b, ha, hb, rfl⟩
    exact h a b ha hb

theorem originalCriterion {X : Type v} [MulAction (Perm A) X] (S : Set A) (x : X) :
    (∀ π : Perm A, (∀ a ∈ S, π a = a) → π • x = x) ↔
      (∀ a b : A, a ∉ S → b ∉ S → Perm.swap a b • x = x) := by
  simpa only [SetLike.le_def, mem_fixingSubgroup_iff, Perm.smul_atom,
    MulAction.mem_stabilizer_iff] using
    fixingSubgroup_le_iff S (MulAction.stabilizer (Perm A) x)
end Generation

section HomBridge
variable {A : Type u} {X : Type v} {Y : Type w}
variable [MulAction (Perm A) X] [MulAction (Perm A) Y]

def equivariantToHom {f : X → Y} (hf : Equivariant A f) : X →[Perm A] Y :=
  ⟨f, hf⟩

theorem homIsEquivariant (f : X →[Perm A] Y) : Equivariant A f := f.map_smul

example {f : X → Y} (hf : Equivariant A f) : ⇑(equivariantToHom hf) = f := rfl
end HomBridge

section MovedMathlibBridge
open scoped Pointwise
variable {A : Type u}

theorem moved_eq_compl_fixedBy (π : Perm A) :
    π.moved = (MulAction.fixedBy A π)ᶜ := rfl

theorem moved_inv_fromMathlib (π : Perm A) : π⁻¹.moved = π.moved := by
  simp only [moved_eq_compl_fixedBy, MulAction.fixedBy_inv]

theorem moved_mul_fromMathlib (π σ : Perm A) :
    (π * σ).moved ⊆ π.moved ∪ σ.moved := by
  exact Equiv.Perm.set_support_mul_subset π.toEquiv σ.toEquiv

theorem moved_conj_fromMathlib (π σ : Perm A) :
    (π * σ * π⁻¹).moved = π '' σ.moved := by
  change (MulAction.fixedBy A (π * σ * π⁻¹))ᶜ = π • (MulAction.fixedBy A σ)ᶜ
  rw [Set.smul_set_compl, MulAction.smul_fixedBy]
end MovedMathlibBridge

section WeakerEquivariance
variable {A : Type u} {X : Type v} {Y : Type w} {Z : Type z}
variable [SMul (Perm A) X] [SMul (Perm A) Y] [SMul (Perm A) Z]

def equivariantSMul (f : X → Y) : Prop :=
  ∀ (π : Perm A) x, f (π • x) = π • f x

theorem equivariantSMul_id : equivariantSMul (A := A) (_root_.id : X → X) := fun _ _ => rfl

theorem equivariantSMul_comp {g : Y → Z} {f : X → Y}
    (hg : equivariantSMul (A := A) g) (hf : equivariantSMul (A := A) f) :
    equivariantSMul (A := A) (g ∘ f) := by
  intro π x
  change g (f (π • x)) = π • g (f x)
  rw [hf, hg]

theorem equivariantSMul_fst : equivariantSMul (A := A) (Prod.fst : X × Y → X) := fun _ _ => rfl
theorem equivariantSMul_snd : equivariantSMul (A := A) (Prod.snd : X × Y → Y) := fun _ _ => rfl

theorem equivariantSMul_pair {f : X → Y} {g : X → Z}
    (hf : equivariantSMul (A := A) f) (hg : equivariantSMul (A := A) g) :
    equivariantSMul (A := A) (fun x => (f x, g x)) := by
  intro π x
  exact Prod.ext (hf π x) (hg π x)
end WeakerEquivariance

#print axioms fixingSubgroup_eq_closure
#print axioms originalCriterion
#print axioms homIsEquivariant
#print axioms equivariantSMul_pair
#print axioms moved_conj_fromMathlib
end Probe
