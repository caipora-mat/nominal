import Package
import Mathlib.Data.Setoid.Basic

/-! PKG-01 design evidence, 2026-10-07. Scratch only: no Package declarations. -/
namespace PKG01Descent
open NominalPackage
universe u v w z t

section ScalarPullback
variable {M : Type u} {X : Type v} {Y : Type w} [SMul M X] [SMul M Y]

-- The elementary mechanism uses one scalar, no group laws or support definition.
theorem invariant_pullback_iff (q : X → Y) (hSurj : Function.Surjective q)
    (m : M) (hq : ∀ x, q (m • x) = m • q x) (P : Y → Prop) :
    (∀ x, P (q (m • x)) ↔ P (q x)) ↔ (∀ y, P (m • y) ↔ P y) := by
  constructor
  · intro h y
    obtain ⟨x, rfl⟩ := hSurj y
    simpa only [hq] using h x
  · intro h x
    simpa only [hq] using h (q x)
end ScalarPullback

section FunctionObjectPullback
variable {G : Type u} [DivisionMonoid G]
    {B : Type v} [SMul G B] {X : Type w} {Y : Type z} {Z : Type t}
    [MulAction G X] [MulAction G Y] [MulAction G Z]

def precompObject (q : X → Y) (F : FunctionObject G Y Z) : FunctionObject G X Z :=
  FunctionObject.ofFun G (F ∘ q)

theorem precompObject_smul (q : X → Y)
    (hq : ∀ (g : G) x, q (g • x) = g • q x)
    (g : G) (F : FunctionObject G Y Z) :
    precompObject q (g • F) = g • precompObject q F := by
  ext x
  simp only [precompObject, FunctionObject.ofFun_apply, Function.comp_apply,
    FunctionObject.smul_apply, hq]

omit [DivisionMonoid G] [SMul G B] [MulAction G X] [MulAction G Y] [MulAction G Z] in
theorem precompObject_injective (q : X → Y) (hq : Function.Surjective q) :
    Function.Injective (precompObject (G := G) (Z := Z) q) := by
  intro F H h
  ext y
  obtain ⟨x, rfl⟩ := hq y
  exact DFunLike.congr_fun h x

-- This is a direct reuse of delivered general support reflection for injective maps.
theorem supports_precompObject_iff (q : X → Y)
    (hq : ∀ (g : G) x, q (g • x) = g • q x)
    (hSurj : Function.Surjective q) (S : Set B) (F : FunctionObject G Y Z) :
    MulAction.Supports G S (precompObject q F) ↔ MulAction.Supports G S F :=
  ActionSupport.supports_map_iff (precompObject q) (precompObject_smul q hq)
    (precompObject_injective q hSurj) S F
end FunctionObjectPullback

section PredicatePullback
variable {A : Type u} {X : Type v} {Y : Type w}
    [MulAction (Perm A) X] [MulAction (Perm A) Y]

-- The atom-specific logical result does not need group support machinery.
theorem supportsPred_pullback_iff (q : X → Y) (hq : Equivariant A q)
    (hSurj : Function.Surjective q) (S : Finset A) (P : Y → Prop) :
    SupportsPred S (P ∘ q) ↔ SupportsPred S P := by
  exact forall_congr' fun π => forall_congr' fun _hfix =>
    invariant_pullback_iff q hSurj π (hq π) P

theorem finitelySupportedPred_pullback_iff (q : X → Y) (hq : Equivariant A q)
    (hSurj : Function.Surjective q) (P : Y → Prop) :
    FinitelySupportedPred A (P ∘ q) ↔ FinitelySupportedPred A P :=
  exists_congr fun S => supportsPred_pullback_iff q hq hSurj S P

theorem renamePred_pullback (q : X → Y) (hq : Equivariant A q)
    (π : Perm A) (P : Y → Prop) :
    renamePred π P ∘ q = renamePred π (P ∘ q) := by
  funext x
  simp only [renamePred, Function.comp_apply, hq π⁻¹ x]

-- Equality of least support concerns the individually supported predicate object.
-- Neither underlying carrier has to be nominal.
theorem pullback_exact_support [Infinite A] (q : X → Y) (hq : Equivariant A q)
    (hSurj : Function.Surjective q) (P : Y → Prop)
    (hP : FinitelySupportedPred A P) :
    ((finitelySupportedPred_iff A (P ∘ q)).1
      ((finitelySupportedPred_pullback_iff q hq hSurj P).2 hP)).support =
      ((finitelySupportedPred_iff A P).1 hP).support := by
  apply le_antisymm
  · apply FinitelySupported.support_minimal
    apply (supportsPred_iff _ _).1
    apply (supportsPred_pullback_iff q hq hSurj _ P).2
    exact (supportsPred_iff _ _).2 (FinitelySupported.supports_support _)
  · apply FinitelySupported.support_minimal
    apply (supportsPred_iff _ _).1
    apply (supportsPred_pullback_iff q hq hSurj _ P).1
    exact (supportsPred_iff _ _).2 (FinitelySupported.supports_support _)
end PredicatePullback

section OrdinaryDescent
variable {X : Type u} (s : Setoid X)

def Compatible (p : X → Prop) : Prop := ∀ x y, s.r x y → (p x ↔ p y)

theorem compatible_iff_le_ker (p : X → Prop) :
    Compatible s p ↔ s ≤ Setoid.ker p :=
  ⟨fun h x y hxy => propext (h x y hxy), fun h _ _ hxy => Iff.of_eq (h hxy)⟩

theorem compatible_iff_factorsThrough (p : X → Prop) :
    Compatible s p ↔ Function.FactorsThrough p (Quotient.mk s) := by
  constructor
  · intro h x y hxy
    exact propext (h x y (Quotient.exact hxy))
  · intro h x y hxy
    exact Iff.of_eq (h (Quotient.sound hxy))

def descend (p : X → Prop) (hp : Compatible s p) : Quotient s → Prop :=
  Quotient.lift p (fun x y hxy => propext (hp x y hxy))

@[simp] theorem descend_mk (p : X → Prop) (hp : Compatible s p) (x : X) :
    descend s p hp (Quotient.mk s x) ↔ p x := Iff.rfl

-- Existing arbitrary-function universal property, specialized only at Iff compatibility.
def ordinaryEquiv : (Quotient s → Prop) ≃ {p : X → Prop // Compatible s p} :=
  (Setoid.liftEquiv (β := Prop) s).symm.trans
    (Equiv.subtypeEquivRight fun p => (compatible_iff_le_ker s p).symm)

@[simp] theorem ordinaryEquiv_apply (P : Quotient s → Prop) (x : X) :
    (ordinaryEquiv s P).val x ↔ P (Quotient.mk s x) := Iff.rfl

@[simp] theorem ordinaryEquiv_symm_apply (p : {p : X → Prop // Compatible s p})
    (x : X) : (ordinaryEquiv s).symm p (Quotient.mk s x) ↔ p.val x := Iff.rfl

theorem ordinaryEquiv_symm_eq_descend (p : {p : X → Prop // Compatible s p}) :
    (ordinaryEquiv s).symm p = descend s p.val p.property := rfl

theorem descend_pullback (P : Quotient s → Prop) :
    descend s (ordinaryEquiv s P).val (ordinaryEquiv s P).property = P :=
  (ordinaryEquiv s).symm_apply_apply P

theorem compatible_iff_exists_descend (p : X → Prop) :
    Compatible s p ↔ ∃ P : Quotient s → Prop, ∀ x, P (Quotient.mk s x) ↔ p x := by
  constructor
  · intro hp
    exact ⟨descend s p hp, fun _ => Iff.rfl⟩
  · rintro ⟨P, hP⟩ x y hxy
    rw [← hP x, ← hP y, Quotient.sound hxy]

theorem cannot_descend (p : X → Prop) {x y : X} (hxy : s.r x y)
    (hx : p x) (hy : ¬ p y) :
    ¬ ∃ P : Quotient s → Prop, ∀ z, P (Quotient.mk s z) ↔ p z := by
  intro hP
  exact hy (((compatible_iff_exists_descend s p).2 hP x y hxy).1 hx)

-- The nondependent Prop result does not settle arbitrary dependent data coherence.
def dependentDescend {C : Quotient s → Sort v} (f : ∀ x, C (Quotient.mk s x))
    (h : ∀ x y (hxy : s.r x y), (Quotient.sound hxy) ▸ f x = f y) :
    ∀ q, C q := Quotient.rec f h

def dependentSingleton (q : Quotient s) : {r : Quotient s // r = q} :=
  Quotient.recOnSubsingleton q (fun x => ⟨Quotient.mk s x, rfl⟩)
end OrdinaryDescent

section CanonicalDescent
variable {A : Type u} {X : Type v} [MulAction (Perm A) X]
    (s : Setoid X) (hs : SMulInvariant (Perm A) s)
theorem supportsPred_quotient_pullback_iff (S : Finset A) (P : Quotient s → Prop) :
    letI := QuotientAction.mulAction s hs
    SupportsPred S (P ∘ Quotient.mk s) ↔ SupportsPred S P := by
  let _ := QuotientAction.mulAction s hs
  exact supportsPred_pullback_iff (Quotient.mk s) (QuotientAction.equivariant_mk A s hs)
    Quotient.mk_surjective S P

theorem supportsPred_descend_iff (S : Finset A) (p : X → Prop) (hp : Compatible s p) :
    letI := QuotientAction.mulAction s hs
    SupportsPred S (descend s p hp) ↔ SupportsPred S p := by
  let _ := QuotientAction.mulAction s hs
  exact (supportsPred_quotient_pullback_iff s hs S (descend s p hp)).symm

include hs in
theorem compatible_rename (p : X → Prop) (hp : Compatible s p) (π : Perm A) :
    Compatible s (renamePred π p) := fun _ _ hxy => hp _ _ (hs π⁻¹ hxy)

theorem descend_rename (p : X → Prop) (hp : Compatible s p) (π : Perm A) :
    letI := QuotientAction.mulAction s hs
    descend s (renamePred π p) (compatible_rename s hs p hp π) =
      renamePred π (descend s p hp) := by
  let _ := QuotientAction.mulAction s hs
  funext q
  induction q using Quotient.inductionOn with
  | h x => rfl

-- Carrier-level supported specialization, independent of the final bundle choice.
def supportedEquiv :
    letI := QuotientAction.mulAction s hs
    {P : Quotient s → Prop // FinitelySupportedPred A P} ≃
      {p : {p : X → Prop // FinitelySupportedPred A p} // Compatible s p.val} := by
  let _ := QuotientAction.mulAction s hs
  exact {
    toFun P := ⟨⟨(ordinaryEquiv s P.val).val, by
      obtain ⟨S, hS⟩ := P.property
      exact ⟨S, (supportsPred_quotient_pullback_iff s hs S P.val).2 hS⟩⟩,
      (ordinaryEquiv s P.val).property⟩
    invFun p := ⟨descend s p.val.val p.property, by
      obtain ⟨S, hS⟩ := p.val.property
      exact ⟨S, (supportsPred_descend_iff s hs S p.val.val p.property).2 hS⟩⟩
    left_inv P := by
      apply Subtype.ext
      exact descend_pullback s P.val
    right_inv p := by
      apply Subtype.ext
      apply Subtype.ext
      rfl }
end CanonicalDescent

section SupportedConsumer
variable {A : Type u}

def duplicateSetoid (A : Type u) : Setoid (A × Discrete A Bool) := Setoid.ker Prod.fst

theorem duplicateInvariant : SMulInvariant (Perm A) (duplicateSetoid A) :=
  fun π _ _ h => congrArg (π • ·) h

theorem duplicateBound (a : A) (S : Finset A)
    (haS : ({a} : Finset A) ⊆ S) :
    SupportsPred S (fun p : A × Discrete A Bool => p.1 = a) := by
  have heq : SupportsPred S (fun x : A => x = a) :=
    (supportsPred_eq_iff S a).2 (supports_mono haS (supports_atom A a))
  exact (supportsPred_pullback_iff Prod.fst (Equivariant.fst A)
    (fun x => ⟨(x, Discrete.mk true), rfl⟩) S (fun x : A => x = a)).2 heq

theorem duplicateCompatible (a : A) :
    Compatible (duplicateSetoid A) (fun p => p.1 = a) := by
  intro x y h
  change x.1 = y.1 at h
  change x.1 = a ↔ y.1 = a
  rw [h]

-- A supplied larger-than-necessary bound transfers exactly, and constructor results
-- let a consumer establish a value at two different representatives.
theorem duplicateDescendedConsumer (a : A) (S : Finset A)
    (haS : ({a} : Finset A) ⊆ S) :
    letI := QuotientAction.mulAction (duplicateSetoid A) duplicateInvariant
    let P := descend (duplicateSetoid A) (fun p => p.1 = a) (duplicateCompatible a)
    SupportsPred S P ∧
      P (Quotient.mk _ (a, Discrete.mk true)) ∧
      P (Quotient.mk _ (a, Discrete.mk false)) := by
  let _ := QuotientAction.mulAction (duplicateSetoid A) duplicateInvariant
  exact ⟨(supportsPred_descend_iff (duplicateSetoid A) duplicateInvariant S
    _ (duplicateCompatible a)).2 (duplicateBound a S haS), rfl, rfl⟩
end SupportedConsumer

section Counterexamples

-- Equivariant, nonempty source: support reflection fails outside the diagonal image.
theorem nonSurjective_pullback_counterexample :
    Equivariant Nat (fun n : Nat => (n,n)) ∧
      ¬ Function.Surjective (fun n : Nat => (n,n)) ∧
      SupportsPred (∅ : Finset Nat) ((fun p : Nat × Nat => p.1 = 0 ∧ p.1 ≠ p.2) ∘
        (fun n : Nat => (n,n))) ∧
      ¬ SupportsPred (∅ : Finset Nat) (fun p : Nat × Nat => p.1 = 0 ∧ p.1 ≠ p.2) := by
  refine ⟨fun _ _ => rfl, ?_, ?_, ?_⟩
  · intro h
    obtain ⟨n, h⟩ := h (0,1)
    have h0 := congrArg Prod.fst h
    have h1 := congrArg Prod.snd h
    change n = 0 at h0
    change n = 1 at h1
    omega
  · intro _ _ _
    simp
  · intro h
    have hp := (h (Perm.swap 0 1) (by simp) (0,2)).2
      (show (0 : Nat) = 0 ∧ (0 : Nat) ≠ 2 by decide)
    have h10 : (1 : Nat) = 0 := by
      simpa only [Prod.smul_mk, Perm.smul_atom, Perm.swap_apply_left] using hp.1
    omega

def vacuousBinderSetoid (A : Type u) : Setoid (A × Discrete A Unit) where
  r _ _ := True
  iseqv := ⟨fun _ => trivial, fun _ => trivial, fun _ _ => trivial⟩

-- Raw binder-name observation is not alpha-compatible, even if finitely supported.
theorem raw_binder_observation_supported (a : Nat) :
    SupportsPred ({a} : Finset Nat) (fun z : Nat × Discrete Nat Unit => z.1 = a) := by
  intro π hfix z
  have ha : π • a = a := hfix a (Finset.mem_singleton_self a)
  change π • z.1 = a ↔ z.1 = a
  calc
    π • z.1 = a ↔ π • z.1 = π • a := by rw [ha]
    _ ↔ z.1 = a := smul_left_cancel_iff π

theorem raw_binder_observation_cannot_descend (a b : Nat) (hab : a ≠ b) :
    ¬ ∃ P : Quotient (vacuousBinderSetoid Nat) → Prop,
      ∀ z, P (Quotient.mk _ z) ↔ z.1 = a :=
  cannot_descend (vacuousBinderSetoid Nat) (fun z => z.1 = a)
    (x := (a, Discrete.mk ())) (y := (b, Discrete.mk ())) trivial rfl (fun h => hab h.symm)

theorem flag_unsupported :
    ¬ FinitelySupportedPred (Nat × Bool) (fun a : Nat × Bool => a.2 = true) := by
  rintro ⟨S, hS⟩
  have hTrue : Set.Infinite {a : Nat × Bool | a.2 = true} := by
    apply (Set.infinite_range_of_injective (f := fun n : Nat => (n,true))
      (fun _ _ h => congrArg Prod.fst h)).mono
    rintro _ ⟨n, rfl⟩
    rfl
  have hFalse : Set.Infinite {a : Nat × Bool | a.2 ≠ true} := by
    apply (Set.infinite_range_of_injective (f := fun n : Nat => (n,false))
      (fun _ _ h => congrArg Prod.fst h)).mono
    rintro _ ⟨n, rfl⟩
    simp
  obtain ⟨a, ha, haS⟩ := hTrue.exists_notMem_finset S
  obtain ⟨b, hb, hbS⟩ := hFalse.exists_notMem_finset S
  have hfix : ∀ c ∈ S, Perm.swap a b c = c := by
    intro c hc
    exact Perm.swap_apply_of_ne_of_ne (fun h => haS (h ▸ hc)) (fun h => hbS (h ▸ hc))
  exact hb (by simpa only [Perm.smul_atom, Perm.swap_apply_left] using
    (hS (Perm.swap a b) hfix a).2 ha)

-- This nontrivial quotient forgets an extra Bool label, preserving the atom itself.
-- Its ordinary predicate is still unsupported; no support certificate is needed.
theorem flagCompatible : Compatible (duplicateSetoid (Nat × Bool)) (fun a => a.1.2 = true) := by
  intro x y h
  change x.1 = y.1 at h
  change x.1.2 = true ↔ y.1.2 = true
  rw [h]

def flagDescended : Quotient (duplicateSetoid (Nat × Bool)) → Prop :=
  descend _ (fun a => a.1.2 = true) flagCompatible

theorem flag_consumer (n : Nat) :
    flagDescended (Quotient.mk _ ((n,true), Discrete.mk false)) ∧
      ¬ flagDescended (Quotient.mk _ ((n,false), Discrete.mk true)) := by
  exact ⟨rfl, Bool.noConfusion⟩

-- Ordinary quotient induction can reason with this unsupported predicate.
-- Its true cases have a true-flag representative; no support premise is used.
theorem flag_induction_consumer (q : Quotient (duplicateSetoid (Nat × Bool))) :
    flagDescended q → ∃ n b, q = Quotient.mk _ ((n,true), Discrete.mk b) := by
  induction q using Quotient.inductionOn with
  | h x =>
    rcases x with ⟨⟨n, flag⟩, label⟩
    intro h
    change flag = true at h
    subst flag
    exact ⟨n, label.val, rfl⟩

theorem flagDescended_unsupported :
    letI := QuotientAction.mulAction (duplicateSetoid (Nat × Bool)) duplicateInvariant
    ¬ FinitelySupportedPred (Nat × Bool) flagDescended := by
  let _ := QuotientAction.mulAction (duplicateSetoid (Nat × Bool)) duplicateInvariant
  intro h
  apply flag_unsupported
  apply (finitelySupportedPred_pullback_iff
    (Prod.fst : (Nat × Bool) × Discrete (Nat × Bool) Bool → Nat × Bool)
    (Equivariant.fst (Nat × Bool)) (fun a => ⟨(a, Discrete.mk true), rfl⟩)
    (fun a => a.2 = true)).1
  obtain ⟨S, hS⟩ := h
  exact ⟨S, (supportsPred_descend_iff (duplicateSetoid (Nat × Bool)) duplicateInvariant S
    (fun a => a.1.2 = true) flagCompatible).1 hS⟩

end Counterexamples

#check supports_precompObject_iff
#check invariant_pullback_iff
#check ordinaryEquiv
#check supportsPred_descend_iff
#check supportedEquiv
#print axioms supports_precompObject_iff
#print axioms invariant_pullback_iff
#print axioms ordinaryEquiv
#print axioms pullback_exact_support
#print axioms supportsPred_descend_iff
#print axioms descend_rename
#print axioms supportedEquiv
#print axioms nonSurjective_pullback_counterexample
#print axioms raw_binder_observation_cannot_descend
#print axioms raw_binder_observation_supported
#print axioms dependentDescend
#print axioms dependentSingleton
#print axioms flag_consumer
#print axioms flag_induction_consumer
#print axioms flagDescended_unsupported
#print axioms duplicateDescendedConsumer
end PKG01Descent
