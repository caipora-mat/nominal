import Package.Foundations.Nominal
import Mathlib.Order.Bounds.Basic

/-!
Research probe, 2026-10-06: natural generalizations of the Package foundation.
Checked against Lean/Mathlib v4.34.1 (Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612).
This file is standalone research evidence, outside production Package imports.
See docs/research/2026-10-06-foundation-generalizations.md for status and limits.
-/

open scoped Pointwise
open NominalPackage

namespace SupportGeneralization

universe u v w z

section GenericTransport

variable {G : Type u} {A : Type v} {X : Type w}
variable [Group G] [MulAction G A] [MulAction G X]

theorem supports_smul_set {S : Set A} {x : X}
    (hS : MulAction.Supports G S x) (g : G) :
    MulAction.Supports G (g • S) (g • x) := by
  intro h hfix
  have hc : (g⁻¹ * h * g) • x = x := hS _ (by
    intro a ha
    have hh : h • (g • a) = g • a := hfix ⟨a, ha, rfl⟩
    simp only [mul_smul, hh, inv_smul_smul])
  calc
    h • (g • x) = g • ((g⁻¹ * h * g) • x) := by
      simp only [mul_smul, smul_inv_smul]
    _ = g • x := congrArg (g • ·) hc

theorem supports_smul_set_iff (g : G) (S : Set A) (x : X) :
    MulAction.Supports G (g • S) (g • x) ↔ MulAction.Supports G S x := by
  constructor
  · intro h
    simpa only [inv_smul_smul] using supports_smul_set h g⁻¹
  · exact fun h => supports_smul_set h g

end GenericTransport

section FinsetTransport

variable {A : Type u} {X : Type v} [MulAction (Perm A) X]
variable {S : Finset A} {x : X}

theorem supports_smul_map (hS : Supports S x) (π : Perm A) :
    Supports (S.map π.toEquiv.toEmbedding) (π • x) := by
  have heq : (π.toEquiv.toEmbedding : A → A) = (fun a => π • a) := by
    funext a
    exact π.toEquiv_apply a
  rw [Supports, Finset.coe_map, heq, Set.image_smul]
  exact supports_smul_set hS π

theorem support_smul_map [Infinite A] (hx : FinitelySupported A x) (π : Perm A) :
    (hx.smul π).support = hx.support.map π.toEquiv.toEmbedding := by
  classical
  have heq : (π.toEquiv.toEmbedding : A → A) = π := by
    funext a
    exact π.toEquiv_apply a
  simpa only [Perm.smul_finset, Finset.map_eq_image, heq] using hx.support_smul π

end FinsetTransport

section GenericMap

variable {G : Type u} {A : Type v} {X : Type w} {Y : Type z}
variable [SMul G A] [SMul G X] [SMul G Y]
variable {f : X → Y} {S : Set A} {x : X}

theorem supports_map_set (hf : ∀ (g : G) x, f (g • x) = g • f x)
    (hS : MulAction.Supports G S x) : MulAction.Supports G S (f x) := by
  intro g hfix
  rw [← hf, hS g hfix]

theorem supports_of_map_set (hf : ∀ (g : G) x, f (g • x) = g • f x)
    (hinj : Function.Injective f) (hS : MulAction.Supports G S (f x)) :
    MulAction.Supports G S x := by
  intro g hfix
  apply hinj
  rw [hf]
  exact hS g hfix

theorem supports_map_set_iff (hf : ∀ (g : G) x, f (g • x) = g • f x)
    (hinj : Function.Injective f) :
    MulAction.Supports G S (f x) ↔ MulAction.Supports G S x :=
  ⟨supports_of_map_set hf hinj, supports_map_set hf⟩

end GenericMap

section PackageMap

variable {A : Type u} {X : Type v} {Y : Type w}
variable [MulAction (Perm A) X] [MulAction (Perm A) Y]
variable {f : X → Y} {S : Finset A} {x : X}

theorem supports_of_map (hf : Equivariant A f) (hinj : Function.Injective f)
    (hS : Supports S (f x)) : Supports S x :=
  supports_of_map_set hf hinj hS

theorem finitelySupported_map_iff (hf : Equivariant A f) (hinj : Function.Injective f) :
    FinitelySupported A (f x) ↔ FinitelySupported A x := by
  constructor
  · rintro ⟨S, hS⟩
    exact ⟨S, supports_of_map hf hinj hS⟩
  · exact fun hx => hx.map hf

theorem support_map_eq [Infinite A] (hx : FinitelySupported A x)
    (hf : Equivariant A f) (hinj : Function.Injective f) :
    (hx.map hf).support = hx.support := by
  apply le_antisymm (hx.support_map_subset hf)
  exact hx.support_minimal (supports_of_map hf hinj (hx.map hf).supports_support)

theorem nominal_of_injective [Nominal A Y]
    (hf : Equivariant A f) (hinj : Function.Injective f) : Nominal A X :=
  ⟨fun x => (finitelySupported_map_iff hf hinj).mp (Nominal.finitelySupported (A := A) (f x))⟩

theorem nominal_of_surjective [Nominal A X]
    (hf : Equivariant A f) (hsurj : Function.Surjective f) : Nominal A Y := by
  constructor
  intro y
  obtain ⟨x, rfl⟩ := hsurj y
  exact (Nominal.finitelySupported (A := A) x).map hf

end PackageMap

section LocalIntersection

variable {A : Type u} {X : Type v} [DecidableEq A] [MulAction (Perm A) X]
variable {S T : Set A} {x : X}

theorem supports_set_iff_swap (S : Set A) (x : X) :
    MulAction.Supports (Perm A) S x ↔
      ∀ a b : A, a ∉ S → b ∉ S → Perm.swap a b • x = x := by
  constructor
  · intro h
    apply (Perm.forall_smul_eq_iff_swap_smul_eq S x).mp
    exact fun π hfix => h π (fun a ha => hfix a ha)
  · intro h π hfix
    exact (Perm.forall_smul_eq_iff_swap_smul_eq S x).mpr h π (fun _ ha => hfix ha)

omit [DecidableEq A] in theorem supports_inter_set_of_spare
    (hS : MulAction.Supports (Perm A) S x)
    (hT : MulAction.Supports (Perm A) T x)
    (hspare : ∃ c : A, c ∉ S ∧ c ∉ T) :
    MulAction.Supports (Perm A) (S ∩ T) x := by
  classical
  obtain ⟨c, hcS, hcT⟩ := hspare
  apply (supports_set_iff_swap _ x).mpr
  intro a b ha hb
  by_cases hab : a = b
  · subst b
    simp
  by_cases haS : a ∈ S
  · have haT : a ∉ T := fun hat => ha ⟨haS, hat⟩
    by_cases hbT : b ∈ T
    · have hbS : b ∉ S := fun hbs => hb ⟨hbs, hbT⟩
      have hcb : c ≠ b := fun h => hcT (h ▸ hbT)
      have hacfix := (supports_set_iff_swap T x).mp hT a c haT hcT
      have hcbfix := (supports_set_iff_swap S x).mp hS c b hcS hbS
      have hconj : Perm.swap a c * Perm.swap c b * Perm.swap a c = Perm.swap a b := by
        simpa only [Perm.swap_inv, Perm.swap_apply_right,
          Perm.swap_apply_of_ne_of_ne (Ne.symm hab) (Ne.symm hcb)] using
          Perm.conj_swap (Perm.swap a c) c b
      rw [← hconj, mul_smul, mul_smul, hacfix, hcbfix, hacfix]
    · exact (supports_set_iff_swap T x).mp hT a b haT hbT
  · by_cases hbS : b ∈ S
    · have hbT : b ∉ T := fun hbt => hb ⟨hbS, hbt⟩
      by_cases haT : a ∈ T
      · have hcb : c ≠ b := fun h => hcS (h ▸ hbS)
        have hacfix := (supports_set_iff_swap S x).mp hS a c haS hcS
        have hcbfix := (supports_set_iff_swap T x).mp hT c b hcT hbT
        have hconj : Perm.swap a c * Perm.swap c b * Perm.swap a c = Perm.swap a b := by
          simpa only [Perm.swap_inv, Perm.swap_apply_right,
            Perm.swap_apply_of_ne_of_ne (Ne.symm hab) (Ne.symm hcb)] using
            Perm.conj_swap (Perm.swap a c) c b
        rw [← hconj, mul_smul, mul_smul, hacfix, hcbfix, hacfix]
      · exact (supports_set_iff_swap T x).mp hT a b haT hbT
    · exact (supports_set_iff_swap S x).mp hS a b haS hbS

theorem supports_inter_of_spare {S T : Finset A}
    (hS : Supports S x) (hT : Supports T x)
    (hspare : ∃ c : A, c ∉ S ∧ c ∉ T) : Supports (S ∩ T) x := by
  simpa only [Supports, Finset.coe_inter] using supports_inter_set_of_spare hS hT hspare

theorem supports_inter_infinite {S T : Finset A} [Infinite A]
    (hS : Supports S x) (hT : Supports T x) : Supports (S ∩ T) x := by
  apply supports_inter_of_spare hS hT
  obtain ⟨c, hc⟩ := Finset.exists_notMem (S ∪ T)
  exact ⟨c, fun h => hc (Finset.mem_union_left T h), fun h => hc (Finset.mem_union_right S h)⟩

end LocalIntersection

section ArbitrarySetBoundary

variable {A : Type u}

theorem supports_compl_singleton (a : A) :
    MulAction.Supports (Perm A) ({a}ᶜ : Set A) a := by
  intro π hfix
  by_contra hmove
  have hh : π • (π • a) = π • a := hfix (by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hmove)
  exact hmove (smul_left_cancel π hh)

theorem atom_mem_of_supports [Infinite A] {S : Finset A} {a : A}
    (hS : Supports S a) : a ∈ S := by
  classical
  by_contra ha
  obtain ⟨b, hb⟩ := Finset.exists_notMem (insert a S)
  have hbS : b ∉ S := fun h => hb (Finset.mem_insert_of_mem h)
  have hba : b ≠ a := fun h => hb (h ▸ Finset.mem_insert_self a S)
  exact hba (by simpa using swap_smul_eq_of_supports hS ha hbS)

theorem arbitrary_set_support_does_not_contain_least [Infinite A]
    (a : A) (ha : FinitelySupported A a) :
    MulAction.Supports (Perm A) ({a}ᶜ : Set A) a ∧
      ¬ ((ha.support : Set A) ⊆ {a}ᶜ) := by
  refine ⟨supports_compl_singleton a, ?_⟩
  intro h
  exact h (atom_mem_of_supports ha.supports_support) (Set.mem_singleton a)

end ArbitrarySetBoundary

section OrderReuse

variable {P : Type u} [PartialOrder P] [WellFoundedLT P] {p : P → Prop}

theorem exists_unique_least_of_directed (hp : ∃ a, p a)
    (hd : DirectedOn (fun a b : P => b ≤ a) {a | p a}) :
    ∃! a, p a ∧ ∀ b, p b → a ≤ b := by
  obtain ⟨a, ha⟩ := exists_minimal_of_wellFoundedLT p hp
  have hl : IsLeast {a | p a} a := hd.minimal_iff_isLeast.mp ha
  refine ⟨a, ⟨hl.1, fun b hb => hl.2 hb⟩, ?_⟩
  intro b hb
  exact le_antisymm (hb.2 a hl.1) (hl.2 hb.1)

theorem exists_unique_least_of_inf_closed {L : Type u} [SemilatticeInf L]
    [WellFoundedLT L] {p : L → Prop} (hp : ∃ a, p a)
    (hclosed : ∀ a b, p a → p b → p (a ⊓ b)) :
    ∃! a, p a ∧ ∀ b, p b → a ≤ b :=
  exists_unique_least_of_directed hp
    (fun a ha b hb => ⟨a ⊓ b, hclosed a b ha hb, inf_le_left, inf_le_right⟩)

end OrderReuse

theorem exists_least_support_of_directed {A : Type u} {X : Type v}
    [MulAction (Perm A) X] {x : X} (hx : FinitelySupported A x)
    (hd : DirectedOn (fun S T : Finset A => T ⊆ S) {S | Supports S x}) :
    ∃! S : Finset A, Supports S x ∧ ∀ T : Finset A, Supports T x → S ⊆ T :=
  exists_unique_least_of_directed hx hd

#print axioms supports_smul_set
#print axioms supports_smul_map
#print axioms support_smul_map
#print axioms supports_map_set_iff
#print axioms support_map_eq
#print axioms nominal_of_injective
#print axioms nominal_of_surjective
#print axioms exists_unique_least_of_directed
#print axioms supports_inter_set_of_spare
#print axioms supports_inter_infinite
#print axioms exists_least_support_of_directed
#print axioms arbitrary_set_support_does_not_contain_least
#check @supports_inter_set_of_spare

end SupportGeneralization
