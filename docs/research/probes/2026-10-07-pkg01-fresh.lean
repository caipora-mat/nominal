import Package
import Mathlib.Order.Filter.Cofinite

/-! Bounded PKG-01 design evidence. No production declarations. -/
namespace PKG01FreshProbe
open NominalPackage Filter
open scoped Pointwise
universe u v

def Freshly {A : Type u} (p : A → Prop) : Prop := ∀ᶠ a in Filter.cofinite, p a

scoped notation "И " x ", " φ => Freshly (fun x ↦ φ)
scoped notation "И " x " : " t ", " φ => Freshly (fun (x : t) ↦ φ)

example {A : Type u} (p : A → Prop) : (И a : A, p a) ↔ Freshly p := Iff.rfl
example {A : Type u} (p : A → Prop) : (И a, p a) ↔ Freshly p := Iff.rfl

theorem reindex {A : Type u} {B : Type v} (e : A ≃ B) (p : B → Prop) :
    Freshly (fun a => p (e a)) ↔ Freshly p := by
  constructor
  · intro h
    have h' := e.symm.injective.tendsto_cofinite.eventually h
    simpa only [Freshly, Equiv.apply_symm_apply] using h'
  · exact e.injective.tendsto_cofinite.eventually

theorem some_any {A : Type u} [Infinite A] {S : Finset A} {p : A → Prop}
    (hP : SupportsPred S p) :
    (Freshly p ↔ ∃ a, a ∉ S ∧ p a) ∧ (Freshly p ↔ ∀ a, a ∉ S → p a) := by
  classical
  have hconstant : ∀ a b, a ∉ S → b ∉ S → (p a ↔ p b) := by
    intro a b ha hb
    have hfix : ∀ c ∈ S, Perm.swap a b c = c := by
      intro c hc
      exact Perm.swap_apply_of_ne_of_ne (fun h => ha (h ▸ hc)) (fun h => hb (h ▸ hc))
    simpa only [Perm.smul_atom, Perm.swap_apply_left] using (hP (Perm.swap a b) hfix a).symm
  have hCE : Freshly p → ∃ a, a ∉ S ∧ p a := by
    intro h
    exact ((S.eventually_cofinite_notMem).and h).exists
  have hEA : (∃ a, a ∉ S ∧ p a) → ∀ a, a ∉ S → p a := by
    rintro ⟨b, hb, hpb⟩ a ha
    exact (hconstant b a hb ha).mp hpb
  have hAC : (∀ a, a ∉ S → p a) → Freshly p := by
    intro h
    exact S.eventually_cofinite_notMem.mono h
  exact ⟨⟨hCE, fun h => hAC (hEA h)⟩, ⟨fun h => hEA (hCE h), hAC⟩⟩

theorem enlarged_bound {A : Type u} [Infinite A] {S T : Finset A} {p : A → Prop}
    (hP : SupportsPred S p) (hST : S ⊆ T) :
    (Freshly p ↔ ∃ a, a ∉ T ∧ p a) ∧ (Freshly p ↔ ∀ a, a ∉ T → p a) :=
  some_any (hP.mono hST)

theorem added_avoidance {A : Type u} [Infinite A] {S : Finset A} {p : A → Prop}
    (hP : SupportsPred S p) (T : Finset A) :
    (Freshly p ↔ ∃ a, a ∉ S ∧ a ∉ T ∧ p a) ∧
      (Freshly p ↔ ∀ a, a ∉ S → a ∉ T → p a) := by
  classical
  simpa only [Finset.notMem_union, and_assoc, and_imp] using
    enlarged_bound hP (T := S ∪ T) Finset.subset_union_left

theorem fresh_projection {A : Type u} {X : Type v} [MulAction (Perm A) X]
    {S : Finset A} {R : X × A → Prop} (hR : SupportsPred S R) :
    SupportsPred S (fun x => Freshly (fun a => R (x,a))) := by
  intro π hfix x
  calc
    Freshly (fun a => R (π • x, a)) ↔ Freshly (fun a => R (π • x, π a)) :=
      (reindex π.toEquiv _).symm
    _ ↔ Freshly (fun a => R (x,a)) := eventually_congr (Eventually.of_forall fun a => by
      simpa only [Prod.smul_mk, Perm.smul_atom] using hR π hfix (x,a))

theorem context_some_any {A : Type u} {X : Type v} [MulAction (Perm A) X]
    [Infinite A] {R : X × A → Prop}
    (hR : ∀ (π : Perm A) q, R (π • q) ↔ R q) {x : X}
    (hx : FinitelySupported A x) :
    (Freshly (fun a => R (x,a)) ↔ ∃ a, hx.Fresh a ∧ R (x,a)) ∧
      (Freshly (fun a => R (x,a)) ↔ ∀ a, hx.Fresh a → R (x,a)) := by
  simpa only [hx.fresh_iff_notMem_support] using
    some_any (supportsPred_section_of_invariant hR hx.supports_support)

-- The support premise supplies cofinite decision, not a global ultrafilter.
theorem support_decision {A : Type u} [Infinite A] {S : Finset A} {p : A → Prop}
    (hP : SupportsPred S p) : Freshly p ∨ Freshly (fun a => ¬p a) := by
  classical
  by_cases h : Freshly p
  · exact Or.inl h
  · right
    have hnone : ¬ ∃ a, a ∉ S ∧ p a := fun he => h ((some_any hP).1.mpr he)
    exact S.eventually_cofinite_notMem.mono fun a ha hp => hnone ⟨a,ha,hp⟩

theorem neg_of_decision {A : Type u} [Infinite A] {p : A → Prop}
    (hd : Freshly p ∨ Freshly (fun a => ¬p a)) : Freshly (fun a => ¬p a) ↔ ¬ Freshly p := by
  constructor
  · intro hn hp
    obtain ⟨a, hpa, hna⟩ := (hp.and hn).exists
    exact hna hpa
  · intro hn
    exact hd.resolve_left hn

theorem or_of_decision {A : Type u} {p q : A → Prop}
    (hd : Freshly p ∨ Freshly (fun a => ¬p a)) :
    Freshly (fun a => p a ∨ q a) ↔ Freshly p ∨ Freshly q := by
  classical
  constructor
  · intro h
    rcases hd with hp | hn
    · exact Or.inl hp
    · exact Or.inr ((h.and hn).mono fun _ ⟨hpq, hnp⟩ => hpq.resolve_left hnp)
  · rintro (hp | hq)
    · exact hp.mono fun _ hp => Or.inl hp
    · exact hq.mono fun _ hq => Or.inr hq

theorem imp_of_decision {A : Type u} {p q : A → Prop}
    (hd : Freshly p ∨ Freshly (fun a => ¬p a)) :
    Freshly (fun a => p a → q a) ↔ (Freshly p → Freshly q) := by
  constructor
  · intro hpq hp
    exact hp.mp hpq
  · intro h
    rcases hd with hp | hn
    · exact (h hp).mono fun _ hq _ => hq
    · exact hn.mono fun _ hnp hp => (hnp hp).elim

theorem iff_of_decisions {A : Type u} {p q : A → Prop}
    (hp : Freshly p ∨ Freshly (fun a => ¬p a)) (hq : Freshly q ∨ Freshly (fun a => ¬q a)) :
    Freshly (fun a => p a ↔ q a) ↔ (Freshly p ↔ Freshly q) := by
  have hpoint : Freshly (fun a => p a ↔ q a) ↔
      Freshly (fun a => p a → q a) ∧ Freshly (fun a => q a → p a) := by
    exact (eventually_congr (Eventually.of_forall fun _ => iff_def)).trans eventually_and
  rw [hpoint, imp_of_decision hp, imp_of_decision hq]
  exact iff_def.symm

-- An already cofinite operand is a weaker sufficient premise for this individual iff law.
theorem iff_of_cofinite_left {A : Type u} {p q : A → Prop} (hp : Freshly p) :
    Freshly (fun a => p a ↔ q a) ↔ (Freshly p ↔ Freshly q) := by
  constructor
  · intro h
    exact ⟨fun _ => (hp.and h).mono fun _ ha => ha.2.mp ha.1, fun _ => hp⟩
  · intro h
    exact (hp.and (h.mp hp)).mono fun _ ⟨hpa,hqa⟩ => ⟨fun _ => hqa, fun _ => hpa⟩

theorem supported_atom_finite_or_cofinite {A : Type u} (p : A → Prop) :
    FinitelySupportedPred A p ↔ Set.Finite {a | p a} ∨ Set.Finite {a | ¬p a} := by
  classical
  constructor
  · intro h
    rcases finite_or_infinite A with hA | hA
    · exact Or.inl (Set.toFinite _)
    · obtain ⟨S,hP⟩ := h
      rcases support_decision hP with hp | hn
      · exact Or.inr (eventually_cofinite.mp hp)
      · exact Or.inl (by simpa using eventually_cofinite.mp hn)
  · intro h
    have finite_support (q : A → Prop) (hq : Set.Finite {a | q a}) :
        SupportsPred hq.toFinset q := by
      intro π hfix a
      constructor
      · intro hqa
        have hfixed := hfix (π a) (hq.mem_toFinset.mpr hqa)
        have heq : π a = a := π.toEquiv.injective hfixed
        simpa only [Perm.smul_atom, heq] using hqa
      · intro hqa
        have hfixed := hfix a (hq.mem_toFinset.mpr hqa)
        simpa only [Perm.smul_atom, hfixed] using hqa
    rcases h with hp | hn
    · exact ⟨_, finite_support p hp⟩
    · refine ⟨hn.toFinset, fun π hfix a => ?_⟩
      exact not_iff_not.mp (finite_support (fun a => ¬p a) hn π hfix a)

theorem finitely_supported_decision {A : Type u} {p : A → Prop}
    (hp : FinitelySupportedPred A p) : Freshly p ∨ Freshly (fun a => ¬p a) := by
  rcases (supported_atom_finite_or_cofinite p).mp hp with h | h
  · right
    exact eventually_cofinite.mpr (by simpa using h)
  · exact Or.inl (eventually_cofinite.mpr h)

theorem infinite_coinfinite_unsupported {A : Type u} (p : A → Prop)
    (hp : Set.Infinite {a | p a}) (hn : Set.Infinite {a | ¬p a}) :
    ¬ FinitelySupportedPred A p := by
  intro h
  rcases (supported_atom_finite_or_cofinite p).mp h with hf | hf
  · exact hp hf
  · exact hn hf

theorem concrete_infinite_coinfinite :
    Set.Infinite {a : Nat × Bool | a.2 = true} ∧
      Set.Infinite {a : Nat × Bool | ¬ a.2 = true} := by
  constructor
  · apply (Set.infinite_range_of_injective (f := fun n : Nat => (n, true))
      (fun _ _ h => congrArg Prod.fst h)).mono
    rintro _ ⟨n, rfl⟩
    rfl
  · apply (Set.infinite_range_of_injective (f := fun n : Nat => (n, false))
      (fun _ _ h => congrArg Prod.fst h)).mono
    rintro _ ⟨n, rfl⟩
    simp

theorem unsupported_union_of_supported_singletons :
    (∀ n : Nat, FinitelySupportedPred (Nat × Bool) (fun a => a = (n,true))) ∧
      ¬ FinitelySupportedPred (Nat × Bool) (fun a => ∃ n : Nat, a = (n,true)) := by
  constructor
  · intro n
    exact ⟨{(n,true)}, (supportsPred_eq_iff _ _).mpr (supports_atom _ _)⟩
  · have heq : (fun a : Nat × Bool => ∃ n : Nat, a = (n,true)) =
        (fun a => a.2 = true) := by
      funext a
      apply propext
      constructor
      · rintro ⟨n,rfl⟩
        rfl
      · intro h
        exact ⟨a.1, Prod.ext rfl h⟩
    rw [heq]
    exact infinite_coinfinite_unsupported _ concrete_infinite_coinfinite.1
      concrete_infinite_coinfinite.2

theorem arbitrary_boolean_failures :
    let p := fun a : Nat × Bool => a.2 = true
    ¬ Freshly p ∧ ¬ Freshly (fun a => ¬p a) ∧ Freshly (fun a => p a ∨ ¬p a) ∧
      ¬ (Freshly (fun a => ¬p a) ↔ ¬ Freshly p) ∧
      ¬ (Freshly (fun a => p a → False) ↔ (Freshly p → Freshly (fun _ : Nat × Bool => False))) := by
  classical
  dsimp
  have hn : ¬ Freshly (fun a : Nat × Bool => a.2 = true) :=
    fun h => concrete_infinite_coinfinite.2 (eventually_cofinite.mp h)
  have hp : ¬ Freshly (fun a : Nat × Bool => ¬a.2 = true) :=
    fun h => concrete_infinite_coinfinite.1 (by simpa using eventually_cofinite.mp h)
  refine ⟨hn, hp, Eventually.of_forall fun _ => em _, ?_, ?_⟩
  · intro h
    exact hp (h.mpr hn)
  · intro h
    exact hp (h.mpr (fun hc => (hn hc).elim))

theorem one_supported_operand_does_not_suffice_for_iff :
    let p := fun a : Nat × Bool => a.2 = true
    SupportsPred (∅ : Finset (Nat × Bool)) (fun _ : Nat × Bool => False) ∧
      ¬ (Freshly (fun a => False ↔ p a) ↔
        (Freshly (fun _ : Nat × Bool => False) ↔ Freshly p)) := by
  dsimp
  refine ⟨fun _ _ _ => Iff.rfl, ?_⟩
  intro h
  have hn := arbitrary_boolean_failures.1
  have hnp := arbitrary_boolean_failures.2.1
  have hf : ¬ Freshly (fun _ : Nat × Bool => False) := by
    intro hc
    exact hc.exists.elim (fun _ hFalse => hFalse)
  have hi : Freshly (fun _ : Nat × Bool => False) ↔ Freshly (fun a : Nat × Bool => a.2 = true) :=
    ⟨fun hc => (hf hc).elim, fun hc => (hn hc).elim⟩
  exact hnp ((h.mpr hi).mono fun _ ha hp => ha.mpr hp)

example : Freshly (fun _ : Bool => False) := by simp [Freshly]

-- Even a nominal acted carrier can have an empty-supported infinite/coinfinite subset.
-- Thus atom Some/Any cannot be generalized to cofinite quantification on every carrier.
theorem arbitrary_nominal_carrier_boundary :
    SupportsPred (∅ : Finset Nat)
      (fun q : Discrete Nat Bool × Nat => q.1.val = true) ∧
      (∃ q : Discrete Nat Bool × Nat, q.1.val = true) ∧
      ¬ Freshly (fun q : Discrete Nat Bool × Nat => q.1.val = true) := by
  refine ⟨fun _ _ _ => Iff.rfl, ⟨(Discrete.mk true,0), rfl⟩, ?_⟩
  have hn : Set.Infinite {q : Discrete Nat Bool × Nat | ¬q.1.val = true} := by
    apply (Set.infinite_range_of_injective
      (f := fun n : Nat => ((Discrete.mk false : Discrete Nat Bool), n))
      (fun _ _ h => congrArg Prod.snd h)).mono
    rintro _ ⟨n,rfl⟩
    simp
  exact fun h => hn (eventually_cofinite.mp h)

theorem no_supported_fresh_selector {A : Type u} [DecidableEq A]
    (f : Finset A → A) (hfresh : ∀ S, f S ∉ S) :
    ¬ FinitelySupportedMap A f := by
  rintro ⟨T, hT⟩
  have hval : Supports T (f T) := by
    simpa only [Finset.union_self] using hT.apply (supports_finset A T)
  let b := f (insert (f T) T)
  have hb : b ∉ insert (f T) T := hfresh _
  have hbT : b ∉ T := fun h => hb (Finset.mem_insert_of_mem h)
  have hba : b ≠ f T := fun h => hb (h ▸ Finset.mem_insert_self _ _)
  have hfix := swap_smul_eq_of_supports hval (hfresh T) hbT
  exact hba (by simpa only [Perm.smul_atom, Perm.swap_apply_left] using hfix)

theorem failed_exists_interchange {A : Type u} [Infinite A] :
    Freshly (fun a : A => ∃ x : A, a = x) ∧ ¬ (∃ x : A, Freshly (fun a => a = x)) := by
  constructor
  · exact Eventually.of_forall fun a => ⟨a,rfl⟩
  · rintro ⟨x,hx⟩
    obtain ⟨a, ha, hne⟩ := (hx.and (eventually_cofinite_ne x)).exists
    exact hne ha

theorem failed_forall_interchange {A : Type u} [Infinite A] :
    (∀ x : A, Freshly (fun a => a ≠ x)) ∧ ¬ Freshly (fun a : A => ∀ x : A, a ≠ x) := by
  constructor
  · exact eventually_cofinite_ne
  · intro h
    obtain ⟨a, ha⟩ := h.exists
    exact ha a rfl

theorem finite_forall {A : Type u} {I : Type v} [Finite I] (p : I → A → Prop) :
    Freshly (fun a => ∀ i, p i a) ↔ ∀ i, Freshly (p i) := eventually_all

-- A shared finite support bound repairs both interchanges; separate section bounds do not.
theorem uniform_support_interchange {A : Type u} [Infinite A] {I : Type v}
    {S : Finset A} {p : I → A → Prop} (hp : ∀ i, SupportsPred S (p i)) :
    (Freshly (fun a => ∀ i, p i a) ↔ ∀ i, Freshly (p i)) ∧
      (Freshly (fun a => ∃ i, p i a) ↔ ∃ i, Freshly (p i)) := by
  constructor
  · constructor
    · exact forall_eventually_of_eventually_forall
    · intro h
      exact S.eventually_cofinite_notMem.mono fun a ha i => ((some_any (hp i)).2.mp (h i)) a ha
  · constructor
    · intro h
      have hExists : SupportsPred S (fun a => ∃ i, p i a) :=
        fun π hfix a => exists_congr fun i => hp i π hfix a
      obtain ⟨a,ha,i,hpa⟩ := (some_any hExists).1.mp h
      exact ⟨i, (some_any (hp i)).1.mpr ⟨a,ha,hpa⟩⟩
    · rintro ⟨i,hi⟩
      exact hi.mono fun _ hpa => ⟨i,hpa⟩

theorem uniform_support_forall {A : Type u} {I : Type v}
    {S : Finset A} {p : I → A → Prop} (hp : ∀ i, SupportsPred S (p i)) :
    Freshly (fun a => ∀ i, p i a) ↔ ∀ i, Freshly (p i) := by
  rcases finite_or_infinite A with hA | hA
  · simp [Freshly]
  · exact (uniform_support_interchange hp).1

theorem uniform_support_exists_nonempty {A : Type u} {I : Type v} [Nonempty I]
    {S : Finset A} {p : I → A → Prop} (hp : ∀ i, SupportsPred S (p i)) :
    Freshly (fun a => ∃ i, p i a) ↔ ∃ i, Freshly (p i) := by
  rcases finite_or_infinite A with hA | hA
  · simp [Freshly]
  · exact (uniform_support_interchange hp).2

theorem failed_finite_empty_exists :
    Freshly (fun _ : Bool => ∃ _ : Empty, False) ∧
      ¬ (∃ _ : Empty, Freshly (fun _ : Bool => False)) := by simp [Freshly]

theorem failed_finite_nonempty_exists :
    Freshly (fun a : Nat × Bool => ∃ i : Bool, a.2 = i) ∧
      ¬ (∃ i : Bool, Freshly (fun a : Nat × Bool => a.2 = i)) := by
  constructor
  · exact Eventually.of_forall fun a => ⟨a.2,rfl⟩
  · rintro ⟨i,h⟩
    cases i with
    | false =>
      apply arbitrary_boolean_failures.2.1
      exact h.mono fun a ha ht => by simp [ha] at ht
    | true => exact arbitrary_boolean_failures.1 h

-- These are jointly invariant despite their failed full interchanges above.
theorem equality_jointly_invariant {A : Type u} (π : Perm A) (q : A × A) :
    ((π • q).1 = (π • q).2) ↔ q.1 = q.2 := π.toEquiv.injective.eq_iff

theorem disequality_jointly_invariant {A : Type u} (π : Perm A) (q : A × A) :
    ((π • q).1 ≠ (π • q).2) ↔ q.1 ≠ q.2 := not_congr (equality_jointly_invariant π q)

#print axioms some_any
#print axioms reindex
#print axioms added_avoidance
#print axioms fresh_projection
#print axioms context_some_any
#print axioms or_of_decision
#print axioms imp_of_decision
#print axioms iff_of_decisions
#print axioms iff_of_cofinite_left
#print axioms supported_atom_finite_or_cofinite
#print axioms finitely_supported_decision
#print axioms infinite_coinfinite_unsupported
#print axioms unsupported_union_of_supported_singletons
#print axioms arbitrary_boolean_failures
#print axioms one_supported_operand_does_not_suffice_for_iff
#print axioms arbitrary_nominal_carrier_boundary
#print axioms no_supported_fresh_selector
#print axioms failed_exists_interchange
#print axioms failed_forall_interchange
#print axioms uniform_support_interchange
#print axioms uniform_support_forall
#print axioms uniform_support_exists_nonempty
#print axioms failed_finite_empty_exists
#print axioms failed_finite_nonempty_exists
end PKG01FreshProbe

namespace PKG01FreshNotationConsumer
open scoped PKG01FreshProbe
example {A : Type*} (p : A → Prop) :
    (И a : A, p a) ↔ PKG01FreshProbe.Freshly p := Iff.rfl
example {A : Type*} (p : A → Prop) :
    (И a, p a) ↔ PKG01FreshProbe.Freshly p := Iff.rfl
end PKG01FreshNotationConsumer
