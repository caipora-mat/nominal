/-
Copyright (c) 2026 Nominal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nominal contributors
-/
import Package.Foundations.PredicateLogic
import Mathlib.Order.Filter.Cofinite
import Mathlib.Order.Filter.Finite

/-!
# Cofinite truth and supplied-bound Some/Any

`Freshly` is ordinary cofinite truth for every predicate, without an action or
support premise. Open `NominalPackage.FreshQuantifier` for typed and untyped `И`.

For canonical atoms, a finite logical bound makes a predicate constant outside
that bound. Over infinite atoms this gives Some/Any, including extra finite
avoidance, without computing least support. The finite/cofinite classification
and cofinite decision need no infinitude. Boolean laws state their decision
premises separately; cofinite truth is not an ultrafilter on arbitrary subsets.

Joint fresh projection preserves support by reindexing. Uniform external
families instead require one common bound, with no action on their Sort-valued
index. Their universal interchange needs no infinitude; existential interchange
needs infinite atoms or a nonempty index, since cofinite is bottom on finite types.
-/

namespace NominalPackage
universe u v w i

/-- All but finitely many inputs satisfy this ordinary predicate. -/
def Freshly {A : Type u} (p : A → Prop) : Prop := ∀ᶠ a in Filter.cofinite, p a

namespace FreshQuantifier
scoped notation "И " a ", " p => Freshly (fun a => p)
scoped notation "И " a " : " A ", " p => Freshly (fun (a : A) => p)
end FreshQuantifier

namespace Freshly
variable {A : Type u} {B : Type v} {p q : A → Prop}

theorem iff_eventually (p : A → Prop) : Freshly p ↔ ∀ᶠ a in Filter.cofinite, p a := Iff.rfl

theorem iff_finite (p : A → Prop) : Freshly p ↔ Set.Finite {a | ¬p a} :=
  Filter.eventually_cofinite

theorem iff_exists_finset (p : A → Prop) :
    Freshly p ↔ ∃ S : Finset A, ∀ a, a ∉ S → p a := by
  classical
  constructor
  · intro h
    exact ⟨(iff_finite p |>.1 h).toFinset, fun a ha => by
      simpa only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] using ha⟩
  · rintro ⟨S, hS⟩
    exact S.eventually_cofinite_notMem.mono hS

theorem of_forall (h : ∀ a, p a) : Freshly p := Filter.Eventually.of_forall h

theorem mono (hp : Freshly p) (h : ∀ a, p a → q a) : Freshly q :=
  Filter.Eventually.mono hp h

theorem congr_eventually (h : Freshly (fun a => p a ↔ q a)) : Freshly p ↔ Freshly q :=
  Filter.eventually_congr h

theorem congr (h : ∀ a, p a ↔ q a) : Freshly p ↔ Freshly q :=
  congr_eventually (of_forall h)

@[simp] theorem true (A : Type u) : Freshly (fun _ : A => True) :=
  Filter.eventually_true _

theorem and_iff : Freshly (fun a => p a ∧ q a) ↔ Freshly p ∧ Freshly q :=
  Filter.eventually_and

theorem mp (hp : Freshly p) (h : Freshly (fun a => p a → q a)) : Freshly q :=
  Filter.Eventually.mp hp h

theorem const_iff [Infinite A] (b : Prop) : Freshly (fun _ : A => b) ↔ b :=
  Filter.eventually_const

theorem not_false [Infinite A] : ¬Freshly (fun _ : A => False) :=
  fun h => (const_iff False).1 h

theorem «exists» [Infinite A] (hp : Freshly p) : ∃ a, p a := Filter.Eventually.exists hp

/-- Cofinite truth is unchanged by an equivalence, even across universes. -/
theorem reindex (e : A ≃ B) (p : B → Prop) : Freshly (p ∘ e) ↔ Freshly p := by
  constructor
  · intro h
    simpa only [Freshly, Function.comp_apply, Equiv.apply_symm_apply] using
      e.symm.injective.tendsto_cofinite.eventually h
  · exact e.injective.tendsto_cofinite.eventually

theorem forall_of {I : Sort i} {p : I → A → Prop}
    (h : Freshly (fun a => ∀ j, p j a)) : ∀ j, Freshly (p j) :=
  fun j => h.mono (fun _ ha => ha j)

theorem of_exists {I : Sort i} {p : I → A → Prop}
    (h : ∃ j, Freshly (p j)) : Freshly (fun a => ∃ j, p j a) := by
  obtain ⟨j, hj⟩ := h
  exact hj.mono (fun _ ha => ⟨j, ha⟩)

theorem forall_finite {I : Sort i} [Finite I] {p : I → A → Prop} :
    Freshly (fun a => ∀ j, p j a) ↔ ∀ j, Freshly (p j) := Filter.eventually_all

theorem not_iff_of_decision [Infinite A] (hd : Freshly p ∨ Freshly (fun a => ¬p a)) :
    Freshly (fun a => ¬p a) ↔ ¬Freshly p := by
  refine ⟨fun hn hp => ?_, hd.resolve_left⟩
  exact not_false ((and_iff.2 ⟨hp, hn⟩).mono (fun _ h => h.2 h.1))

/-- Decision of just the left operand suffices; the other predicate is arbitrary. -/
theorem or_iff_of_decision (hd : Freshly p ∨ Freshly (fun a => ¬p a)) :
    Freshly (fun a => p a ∨ q a) ↔ Freshly p ∨ Freshly q := by
  constructor
  · intro h
    rcases hd with hp | hn
    · exact Or.inl hp
    · exact Or.inr ((and_iff.2 ⟨h, hn⟩).mono (fun _ ha => ha.1.resolve_left ha.2))
  · rintro (hp | hq)
    · exact hp.mono (fun _ => Or.inl)
    · exact hq.mono (fun _ => Or.inr)

theorem or_iff_of_decision_right (hd : Freshly q ∨ Freshly (fun a => ¬q a)) :
    Freshly (fun a => p a ∨ q a) ↔ Freshly p ∨ Freshly q := by
  simpa only [or_comm] using (or_iff_of_decision (q := p) hd)

/-- Only the antecedent needs eventual decision, including on finite atom types. -/
theorem imp_iff_of_decision (hd : Freshly p ∨ Freshly (fun a => ¬p a)) :
    Freshly (fun a => p a → q a) ↔ (Freshly p → Freshly q) := by
  refine ⟨fun h hp => hp.mp h, fun h => ?_⟩
  rcases hd with hp | hn
  · exact (h hp).mono (fun _ hq _ => hq)
  · exact hn.mono (fun _ hn hp => (hn hp).elim)

theorem iff_iff_of_decisions (hp : Freshly p ∨ Freshly (fun a => ¬p a))
    (hq : Freshly q ∨ Freshly (fun a => ¬q a)) :
    Freshly (fun a => p a ↔ q a) ↔ (Freshly p ↔ Freshly q) := by
  rw [congr (fun _ => iff_def), and_iff, imp_iff_of_decision hp, imp_iff_of_decision hq]
  exact iff_def.symm

/-- Cofinite truth of one operand suffices here, even when the other is undecided. -/
theorem iff_iff_of_freshly_left (hp : Freshly p) :
    Freshly (fun a => p a ↔ q a) ↔ (Freshly p ↔ Freshly q) := by
  constructor
  · intro h
    exact ⟨fun _ => (and_iff.2 ⟨hp, h⟩).mono (fun _ ha => ha.2.1 ha.1), fun _ => hp⟩
  · intro h
    exact (and_iff.2 ⟨hp, h.1 hp⟩).mono (fun _ ha => ⟨fun _ => ha.2, fun _ => ha.1⟩)
end Freshly

namespace SupportsPred
variable {A : Type u} {S : Finset A} {p : A → Prop}

/-- Swapping two atoms outside a sufficient bound cannot change truth. -/
theorem iff_of_notMem (hp : SupportsPred S p) {a b : A} (ha : a ∉ S) (hb : b ∉ S) :
    p a ↔ p b := by
  classical
  have hfix : ∀ c ∈ S, Perm.swap a b c = c := fun c hc =>
    Perm.swap_apply_of_ne_of_ne (fun h => ha (h ▸ hc)) (fun h => hb (h ▸ hc))
  simpa only [Perm.smul_atom, Perm.swap_apply_left] using (hp (Perm.swap a b) hfix a).symm

theorem freshly_iff_exists [Infinite A] (hp : SupportsPred S p) :
    Freshly p ↔ ∃ a, a ∉ S ∧ p a := by
  constructor
  · intro h
    exact (S.eventually_cofinite_notMem.and h).exists
  · rintro ⟨a, ha, hpa⟩
    exact S.eventually_cofinite_notMem.mono (fun b hb => (hp.iff_of_notMem ha hb).1 hpa)

theorem freshly_iff_forall [Infinite A] (hp : SupportsPred S p) :
    Freshly p ↔ ∀ a, a ∉ S → p a := by
  constructor
  · intro h a ha
    obtain ⟨b, hb, hpb⟩ := hp.freshly_iff_exists.1 h
    exact (hp.iff_of_notMem hb ha).1 hpb
  · exact S.eventually_cofinite_notMem.mono

theorem freshly_iff [Infinite A] (hp : SupportsPred S p) {a : A} (ha : a ∉ S) :
    Freshly p ↔ p a :=
  ⟨fun h => hp.freshly_iff_forall.1 h a ha, fun h => hp.freshly_iff_exists.2 ⟨a, ha, h⟩⟩

theorem freshly_iff_exists_avoiding [Infinite A] (hp : SupportsPred S p) (T : Finset A) :
    Freshly p ↔ ∃ a, a ∉ S ∧ a ∉ T ∧ p a := by
  classical
  simpa only [Finset.notMem_union, and_assoc] using
    (hp.mono (Finset.subset_union_left (s₂ := T))).freshly_iff_exists

theorem freshly_iff_forall_avoiding [Infinite A] (hp : SupportsPred S p) (T : Finset A) :
    Freshly p ↔ ∀ a, a ∉ S → a ∉ T → p a := by
  classical
  simpa only [Finset.notMem_union, and_imp] using
    (hp.mono (Finset.subset_union_left (s₂ := T))).freshly_iff_forall
end SupportsPred

/-- Support decides cofinite truth even on finite atom types. -/
theorem FinitelySupportedPred.freshly_or_not {A : Type u} {p : A → Prop}
    (hp : FinitelySupportedPred A p) : Freshly p ∨ Freshly (fun a => ¬p a) := by
  classical
  obtain ⟨S, hS⟩ := hp
  by_cases h : ∃ a, a ∉ S ∧ p a
  · obtain ⟨a, ha, hpa⟩ := h
    exact Or.inl (S.eventually_cofinite_notMem.mono
      (fun b hb => (hS.iff_of_notMem ha hb).1 hpa))
  · exact Or.inr (S.eventually_cofinite_notMem.mono (fun a ha hpa => h ⟨a, ha, hpa⟩))

/-- Under the canonical atom action, precisely the finite or cofinite predicates are supported. -/
theorem finitelySupportedPred_atom_iff {A : Type u} (p : A → Prop) :
    FinitelySupportedPred A p ↔ Set.Finite {a | p a} ∨ Set.Finite {a | ¬p a} := by
  classical
  constructor
  · intro hp
    rcases hp.freshly_or_not with h | h
    · exact Or.inr ((Freshly.iff_finite p).1 h)
    · exact Or.inl (by simpa only [not_not] using (Freshly.iff_finite _).1 h)
  · have finite_support (q : A → Prop) (hq : Set.Finite {a | q a}) :
        SupportsPred hq.toFinset q := by
      intro π hfix a
      constructor
      · intro hqa
        have hfixed := hfix (π a) (hq.mem_toFinset.2 hqa)
        have heq : π a = a := π.toEquiv.injective hfixed
        simpa only [Perm.smul_atom, heq] using hqa
      · intro hqa
        have hfixed := hfix a (hq.mem_toFinset.2 hqa)
        simpa only [Perm.smul_atom, hfixed] using hqa
    rintro (hp | hn)
    · exact (finite_support p hp).finitelySupported
    · exact ((supportsPred_not_iff _ p).1 (finite_support (fun a => ¬p a) hn)).finitelySupported

theorem not_finitelySupportedPred_of_infinite_coinfinite {A : Type u} (p : A → Prop)
    (hp : Set.Infinite {a | p a}) (hn : Set.Infinite {a | ¬p a}) :
    ¬FinitelySupportedPred A p := by
  intro h
  exact ((finitelySupportedPred_atom_iff p).1 h).elim hp hn

namespace FinitelySupportedPred
variable {A : Type u} {p q : A → Prop}

theorem freshly_not_iff [Infinite A] (hp : FinitelySupportedPred A p) :
    Freshly (fun a => ¬p a) ↔ ¬Freshly p := Freshly.not_iff_of_decision hp.freshly_or_not

theorem freshly_or_iff (hp : FinitelySupportedPred A p) :
    Freshly (fun a => p a ∨ q a) ↔ Freshly p ∨ Freshly q :=
  Freshly.or_iff_of_decision hp.freshly_or_not

theorem freshly_imp_iff (hp : FinitelySupportedPred A p) :
    Freshly (fun a => p a → q a) ↔ (Freshly p → Freshly q) :=
  Freshly.imp_iff_of_decision hp.freshly_or_not

theorem freshly_iff_iff (hp : FinitelySupportedPred A p) (hq : FinitelySupportedPred A q) :
    Freshly (fun a => p a ↔ q a) ↔ (Freshly p ↔ Freshly q) :=
  Freshly.iff_iff_of_decisions hp.freshly_or_not hq.freshly_or_not
end FinitelySupportedPred

/-- Joint fresh projection retains the bound, even for finite atoms and nonnominal X. -/
theorem SupportsPred.fresh {A : Type u} {X : Type v} [MulAction (Perm A) X]
    {S : Finset A} {R : X × A → Prop} (hR : SupportsPred S R) :
    SupportsPred S (fun x => Freshly (fun a => R (x,a))) := by
  intro π hfix x
  calc
    Freshly (fun a => R (π • x, a)) ↔ Freshly (fun a => R (π • x, π a)) :=
      (Freshly.reindex π.toEquiv _).symm
    _ ↔ Freshly (fun a => R (x,a)) := Freshly.congr (fun a => by
      simpa only [Prod.smul_mk, Perm.smul_atom] using hR π hfix (x,a))

theorem FinitelySupportedPred.fresh {A : Type u} {X : Type v} [MulAction (Perm A) X]
    {R : X × A → Prop} (hR : FinitelySupportedPred A R) :
    FinitelySupportedPred A (fun x => Freshly (fun a => R (x,a))) := by
  obtain ⟨S, hS⟩ := hR
  exact hS.fresh.finitelySupported

namespace Freshly
variable {A : Type u} {I : Sort i} {S : Finset A} {p : I → A → Prop}

theorem forall_iff_of_uniform_support (hp : ∀ j, SupportsPred S (p j)) :
    Freshly (fun a => ∀ j, p j a) ↔ ∀ j, Freshly (p j) := by
  rcases finite_or_infinite A with hA | hA
  · simp [Freshly]
  · exact ⟨forall_of, fun h => S.eventually_cofinite_notMem.mono
      (fun a ha j => (hp j).freshly_iff_forall.1 (h j) a ha)⟩

theorem exists_iff_of_uniform_support [Infinite A] (hp : ∀ j, SupportsPred S (p j)) :
    Freshly (fun a => ∃ j, p j a) ↔ ∃ j, Freshly (p j) := by
  refine ⟨fun h => ?_, of_exists⟩
  obtain ⟨a, ha, j, hj⟩ := (SupportsPred.iEx hp).freshly_iff_exists.1 h
  exact ⟨j, (hp j).freshly_iff_exists.2 ⟨a, ha, hj⟩⟩

/-- A nonempty external index handles the bottom-filter case without infinite atoms. -/
theorem exists_iff_of_uniform_support_nonempty [Nonempty I]
    (hp : ∀ j, SupportsPred S (p j)) :
    Freshly (fun a => ∃ j, p j a) ↔ ∃ j, Freshly (p j) := by
  rcases finite_or_infinite A with hA | hA
  · simp [Freshly]
  · exact exists_iff_of_uniform_support hp
end Freshly

section Contexts
variable {A : Type u} {X : Type v} [MulAction (Perm A) X] [Infinite A]
variable {S T : Finset A} {R : X × A → Prop} {x : X}

/-- Relation and individual parameter bounds combine; the carrier need not be nominal. -/
theorem freshly_section_iff_exists [DecidableEq A]
    (hR : SupportsPred S R) (hx : Supports T x) :
    Freshly (fun a => R (x,a)) ↔ ∃ a, a ∉ S ∪ T ∧ R (x,a) :=
  (hR.section hx).freshly_iff_exists

theorem freshly_section_iff_forall [DecidableEq A]
    (hR : SupportsPred S R) (hx : Supports T x) :
    Freshly (fun a => R (x,a)) ↔ ∀ a, a ∉ S ∪ T → R (x,a) :=
  (hR.section hx).freshly_iff_forall

theorem freshly_section_iff_exists_avoiding [DecidableEq A]
    (hR : SupportsPred S R) (hx : Supports T x) (U : Finset A) :
    Freshly (fun a => R (x,a)) ↔ ∃ a, a ∉ S ∪ T ∧ a ∉ U ∧ R (x,a) :=
  (hR.section hx).freshly_iff_exists_avoiding U

theorem freshly_section_iff_forall_avoiding [DecidableEq A]
    (hR : SupportsPred S R) (hx : Supports T x) (U : Finset A) :
    Freshly (fun a => R (x,a)) ↔ ∀ a, a ∉ S ∪ T → a ∉ U → R (x,a) :=
  (hR.section hx).freshly_iff_forall_avoiding U

/-- An invariant relation needs only this parameter's least-support freshness. -/
theorem freshly_invariant_section_iff_exists
    (hR : ∀ (π : Perm A) z, R (π • z) ↔ R z) (hx : FinitelySupported A x) :
    Freshly (fun a => R (x,a)) ↔ ∃ a, hx.Fresh a ∧ R (x,a) := by
  simpa only [hx.fresh_iff_notMem_support] using
    (supportsPred_section_of_invariant hR hx.supports_support).freshly_iff_exists

theorem freshly_invariant_section_iff_forall
    (hR : ∀ (π : Perm A) z, R (π • z) ↔ R z) (hx : FinitelySupported A x) :
    Freshly (fun a => R (x,a)) ↔ ∀ a, hx.Fresh a → R (x,a) := by
  simpa only [hx.fresh_iff_notMem_support] using
    (supportsPred_section_of_invariant hR hx.supports_support).freshly_iff_forall

theorem freshly_invariant_section_iff_exists_avoiding
    (hR : ∀ (π : Perm A) z, R (π • z) ↔ R z) (hx : FinitelySupported A x) (U : Finset A) :
    Freshly (fun a => R (x,a)) ↔ ∃ a, hx.Fresh a ∧ a ∉ U ∧ R (x,a) := by
  simpa only [hx.fresh_iff_notMem_support] using
    (supportsPred_section_of_invariant hR hx.supports_support).freshly_iff_exists_avoiding U

theorem freshly_invariant_section_iff_forall_avoiding
    (hR : ∀ (π : Perm A) z, R (π • z) ↔ R z) (hx : FinitelySupported A x) (U : Finset A) :
    Freshly (fun a => R (x,a)) ↔ ∀ a, hx.Fresh a → a ∉ U → R (x,a) := by
  simpa only [hx.fresh_iff_notMem_support] using
    (supportsPred_section_of_invariant hR hx.supports_support).freshly_iff_forall_avoiding U
end Contexts

/-- Atom evaluation using the ordinary predicate object's individual certificate. -/
theorem FinitelySupportedPred.freshly_iff_of_fresh {A : Type u} [Infinite A]
    {p : A → Prop} (hp : FinitelySupportedPred A p) {a : A}
    (ha : ((finitelySupportedPred_iff A p).1 hp).Fresh a) : Freshly p ↔ p a := by
  have hobj := (finitelySupportedPred_iff A p).1 hp
  exact ((supportsPred_iff _ p).2 hobj.supports_support).freshly_iff
    ((hobj.fresh_iff_notMem_support a).1 ha)

end NominalPackage
