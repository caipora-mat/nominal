import Nominal.Set.FreshQuantifier

/-!
Scratch design probe for PKG-01, 2026-10-05. These are candidate signatures,
not a production predicate API. In particular, no action on bare Prop or
ordinary predicate functions is installed here. A support bound need not be
least. The atom, predicate-domain and quantified-domain universes are separate.
-/
open Nominal.Core Nominal.Set

namespace PredicateSomeAny
universe u v w
variable {α : Type u} [Name α]

structure PredicateSupports {X : Type v} [PermType α X]
    (S : Finset α) (P : X → Prop) : Prop where
  smul_iff : ∀ (π : FinitePerm α), (∀ ⦃a⦄, a ∈ S → π a = a) →
    ∀ x, P (π • x) ↔ P x

namespace PredicateSupports
variable {X : Type v} [PermType α X] {Y : Type w} [PermType α Y]
variable {S T : Finset α} {P Q : X → Prop}

theorem mono (hP : PredicateSupports S P) (hST : S ⊆ T) :
    PredicateSupports T P := ⟨fun π hπ x => hP.smul_iff π (fun _ ha => hπ (hST ha)) x⟩

theorem not (hP : PredicateSupports S P) :
    PredicateSupports S (fun x => ¬ P x) :=
  ⟨fun π hπ x => not_congr (hP.smul_iff π hπ x)⟩

theorem and (hP : PredicateSupports S P) (hQ : PredicateSupports T Q) :
    PredicateSupports (S ∪ T) (fun x => P x ∧ Q x) := by
  refine ⟨fun π hπ x => ?_⟩
  exact and_congr (hP.smul_iff π (fun _ ha => hπ (Finset.mem_union_left T ha)) x)
    (hQ.smul_iff π (fun _ ha => hπ (Finset.mem_union_right S ha)) x)

theorem forall_right {R : X × Y → Prop} (hR : PredicateSupports S R) :
    PredicateSupports S (fun x => ∀ y, R (x, y)) := by
  refine ⟨fun π hπ x => ⟨?_, ?_⟩⟩
  · intro h y
    exact (hR.smul_iff π hπ (x, y)).mp (h (π • y))
  · intro h y
    simpa using (hR.smul_iff π hπ (x, π⁻¹ • y)).mpr (h (π⁻¹ • y))

theorem exists_right {R : X × Y → Prop} (hR : PredicateSupports S R) :
    PredicateSupports S (fun x => ∃ y, R (x, y)) := by
  refine ⟨fun π hπ x => ⟨?_, ?_⟩⟩
  · rintro ⟨y, hy⟩
    refine ⟨π⁻¹ • y, (hR.smul_iff π hπ (x, π⁻¹ • y)).mp ?_⟩
    simpa using hy
  · rintro ⟨y, hy⟩
    exact ⟨π • y, (hR.smul_iff π hπ (x, y)).mpr hy⟩

theorem freshQuantifier_right {R : X × α → Prop} (hR : PredicateSupports S R) :
    PredicateSupports S (fun x => И a, R (x, a)) := by
  refine ⟨fun π hπ x => ?_⟩
  calc
    (И a, R (π • x, a)) ↔ (И a, R (π • x, π • a)) := by
      simpa using (freshQuantifier_smul_iff π⁻¹ (p := fun a => R (π • x, a)))
    _ ↔ (И a, R (x, a)) := freshQuantifier_congr (fun a => hR.smul_iff π hπ (x, a))

theorem section_right {R : X × Y → Prop} (hR : PredicateSupports S R)
    {y : Y} (hy : supports T y) : PredicateSupports (S ∪ T) (fun x => R (x, y)) := by
  refine ⟨fun π hπ x => ?_⟩
  have hfix : π • y = y := hy π (fun _ ha => hπ (Finset.mem_union_right S ha))
  simpa only [PermType.prod_smul, hfix] using
    hR.smul_iff π (fun _ ha => hπ (Finset.mem_union_left T ha)) (x, y)

end PredicateSupports

/-- Fixing a parameter with a certified support needs only its chosen action. -/
theorem equivariantRel_section {X : Type v} [PermType α X]
    {R : α → X → Prop} (hR : EquivariantRel α R) {S : Finset α}
    {x : X} (hx : supports S x) : PredicateSupports S (fun a => R a x) := by
  refine ⟨fun π hπ a => ?_⟩
  have hfix : π • x = x := hx π hπ
  simpa only [hfix] using hR.smul_iff π a x

namespace PredicateSupports
variable {S : Finset α} {P : α → Prop}

theorem outside_iff (hP : PredicateSupports S P) {a b : α}
    (ha : a ∉ S) (hb : b ∉ S) : P a ↔ P b := by
  have h := hP.smul_iff (swap a b) (fun c hc =>
    swap_smul_eq_of_not_mem (s := (S : Set α)) ha hb c hc) a
  simpa using h.symm

theorem someAny_forall (hP : PredicateSupports S P) :
    (И a, P a) ↔ ∀ a, a ∉ S → P a := by
  constructor
  · intro h b hb
    obtain ⟨T, hT⟩ := freshQuantifier_iff_exists_finset.mp h
    pick_new a (S ∪ T)
    have ha : a ∉ S ∧ a ∉ T := by simpa using aNew
    exact (hP.outside_iff ha.1 hb).mp (hT a ha.2)
  · intro h
    exact freshQuantifier_iff_exists_finset.mpr ⟨S, h⟩

theorem someAny_exists (hP : PredicateSupports S P) :
    (И a, P a) ↔ ∃ a, a ∉ S ∧ P a := by
  rw [hP.someAny_forall]
  constructor
  · intro h
    pick_new a S
    exact ⟨a, aNew, h a aNew⟩
  · rintro ⟨a, ha, hPa⟩ b hb
    exact (hP.outside_iff ha hb).mp hPa

theorem finite_or_cofinite (hP : PredicateSupports S P) :
    Set.Finite {a | P a} ∨ Set.Finite {a | ¬ P a} := by
  classical
  by_cases h : ∃ a, a ∉ S ∧ P a
  · exact Or.inr (freshQuantifier_iff.mp (hP.someAny_exists.mpr h))
  · left
    apply S.finite_toSet.subset
    intro a ha
    by_contra hmem
    exact h ⟨a, hmem, ha⟩

theorem fresh_neg (hP : PredicateSupports S P) :
    (¬ (И a, P a)) ↔ (И a, ¬ P a) :=
  freshQuantifier_neg hP.finite_or_cofinite

end PredicateSupports

/-- Bounded Some/Any for a relation, without a nominal instance on its context. -/
example {X : Type v} [PermType α X] {R : α → X → Prop}
    (hR : EquivariantRel α R) {S : Finset α} {x : X} (hx : supports S x) :
    (И a, R a x) ↔ ∃ a, a ∉ S ∧ R a x :=
  (equivariantRel_section hR hx).someAny_exists

/-- Enlarging a certificate preserves the usable bound; no exact support needed. -/
example {P : α → Prop} {S T : Finset α} (hP : PredicateSupports S P) :
    (И a, P a) ↔ ∀ a, a ∉ S ∪ T → P a :=
  (hP.mono Finset.subset_union_left).someAny_forall

/-- No API may turn a classical fresh selector into a supported function. -/
theorem no_supported_fresh_selector (f : NFun α (Finset α) α)
    (hf : ∀ S, f S ∉ S) : False := by
  have h := NFun.supp_apply_le f (supp f)
  rw [supp_atom, supp_finset, Finset.union_self] at h
  exact hf (supp f) (h (Finset.mem_singleton_self _))

#print axioms PredicateSupports.forall_right
#print axioms PredicateSupports.exists_right
#print axioms PredicateSupports.freshQuantifier_right
#print axioms PredicateSupports.someAny_exists
#print axioms PredicateSupports.someAny_forall
#print axioms PredicateSupports.finite_or_cofinite
#print axioms PredicateSupports.fresh_neg
#print axioms no_supported_fresh_selector
end PredicateSomeAny
