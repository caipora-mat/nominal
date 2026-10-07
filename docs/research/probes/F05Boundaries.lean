import Package

/-! Bounded F05 research evidence. Not imported by production; no production API changes. -/
namespace F05Boundaries
open NominalPackage
open scoped Pointwise
universe u v w z

def SupportsMap {A : Type u} {X : Type v} {Y : Type w}
    [MulAction (Perm A) X] [MulAction (Perm A) Y]
    (S : Finset A) (f : X → Y) : Prop :=
  ∀ π : Perm A, (∀ a ∈ S, π a = a) → ∀ x, f (π • x) = π • f x

def SupportsPred {A : Type u} {X : Type v} [MulAction (Perm A) X]
    (S : Finset A) (P : X → Prop) : Prop :=
  ∀ π : Perm A, (∀ a ∈ S, π a = a) → ∀ x, P (π • x) ↔ P x

theorem supportsMap_apply {A : Type u} {X : Type v} {Y : Type w}
    [MulAction (Perm A) X] [MulAction (Perm A) Y] [DecidableEq A]
    {S T : Finset A} {f : X → Y} {x : X}
    (hf : SupportsMap S f) (hx : Supports T x) : Supports (S ∪ T) (f x) := by
  apply (supports_iff _ _).2
  intro π hfix
  have hx' := (supports_iff _ _).1 hx π (fun a ha => hfix a (Finset.mem_union_right S ha))
  simpa only [hx'] using (hf π (fun a ha => hfix a (Finset.mem_union_left T ha)) x).symm

theorem supportsMap_const_iff {A : Type u} {X : Type v} {Y : Type w}
    [MulAction (Perm A) X] [MulAction (Perm A) Y] [Nonempty X]
    (S : Finset A) (y : Y) : SupportsMap S (fun _ : X => y) ↔ Supports S y := by
  constructor
  · intro h
    apply (supports_iff _ _).2
    intro π hfix
    obtain ⟨x⟩ := ‹Nonempty X›
    exact (h π hfix x).symm
  · intro h π hfix _
    exact ((supports_iff _ _).1 h π hfix).symm

theorem supportsMap_empty_domain {A : Type u} {X : Type v} {Y : Type w}
    [MulAction (Perm A) X] [MulAction (Perm A) Y] [IsEmpty X]
    (S : Finset A) (f : X → Y) : SupportsMap S f := by
  intro _ _ x
  exact isEmptyElim x

theorem constants_injective_iff {X : Type v} {Y : Type w} :
    Function.Injective (fun y : Y => fun _ : X => y) ↔ Nonempty X ∨ Subsingleton Y := by
  classical
  constructor
  · intro h
    by_cases hx : Nonempty X
    · exact Or.inl hx
    · right
      exact ⟨fun y z => h (funext (fun x => (hx ⟨x⟩).elim))⟩
  · intro h
    rcases h with hx | hy
    · obtain ⟨x⟩ := hx
      intro _ _ heq
      exact congrFun heq x
    · exact fun y z _ => hy.elim y z

-- Finite support of a jointly equivariant projection does not support every section.
theorem projection_sections_boundary {A : Type u} {X : Type v} {Y : Type w}
    [MulAction (Perm A) X] [MulAction (Perm A) Y] [Nonempty Y]
    (x : X) (hx : ¬ FinitelySupported A x) :
    SupportsMap (∅ : Finset A) (Prod.fst : X × Y → X) ∧
      ¬ ∃ S : Finset A, SupportsMap S (fun _ : Y => x) := by
  refine ⟨fun _ _ _ => rfl, ?_⟩
  rintro ⟨S, hS⟩
  exact hx ⟨S, (supportsMap_const_iff S x).1 hS⟩

theorem supportsPred_eq_iff {A : Type u} {X : Type v} [MulAction (Perm A) X]
    (S : Finset A) (x : X) : SupportsPred S (fun y => y = x) ↔ Supports S x := by
  constructor
  · intro h
    apply (supports_iff _ _).2
    intro π hfix
    exact (h π hfix x).2 rfl
  · intro h π hfix y
    have hx := (supports_iff _ _).1 h π hfix
    calc
      π • y = x ↔ π • y = π • x := by rw [hx]
      _ ↔ y = x := smul_left_cancel_iff π

theorem equality_sections_boundary {A : Type u} {X : Type v}
    [MulAction (Perm A) X] (x : X) (hx : ¬ FinitelySupported A x) :
    SupportsPred (∅ : Finset A) (fun p : X × X => p.1 = p.2) ∧
      ¬ ∃ S : Finset A, SupportsPred S (fun y => y = x) := by
  refine ⟨fun π _ _ => smul_left_cancel_iff π, ?_⟩
  rintro ⟨S, hS⟩
  exact hx ⟨S, (supportsPred_eq_iff S x).1 hS⟩

theorem fixed_atom_predicate_supported_not_invariant {A : Type u} [DecidableEq A]
    (a b : A) (hab : a ≠ b) :
    SupportsPred ({a} : Finset A) (fun x : A => x = a) ∧
      ¬ SupportsPred (∅ : Finset A) (fun x : A => x = a) := by
  refine ⟨(supportsPred_eq_iff _ a).2 (supports_atom A a), ?_⟩
  intro h
  have hfix := (supports_empty_iff a).1 ((supportsPred_eq_iff _ a).1 h) (Perm.swap a b)
  exact hab (by simpa only [Perm.smul_atom, Perm.swap_apply_left] using hfix.symm)

theorem infinite_coinfinite_unsupported {A : Type u} [DecidableEq A]
    (P : A → Prop) (hP : Set.Infinite {a | P a})
    (hnP : Set.Infinite {a | ¬ P a}) : ¬ ∃ S : Finset A, SupportsPred S P := by
  rintro ⟨S, hS⟩
  obtain ⟨a, ha, haS⟩ := hP.exists_notMem_finset S
  obtain ⟨b, hb, hbS⟩ := hnP.exists_notMem_finset S
  have hfix : ∀ c ∈ S, Perm.swap a b c = c := by
    intro c hc
    exact Perm.swap_apply_of_ne_of_ne (fun h => haS (h ▸ hc)) (fun h => hbS (h ▸ hc))
  have hp := (hS (Perm.swap a b) hfix a).2 ha
  exact hb (by simpa only [Perm.smul_atom, Perm.swap_apply_left] using hp)

theorem no_supported_fresh_selector {A : Type u} [DecidableEq A]
    (f : Finset A → A) (hfresh : ∀ S, f S ∉ S) :
    ¬ ∃ T : Finset A, SupportsMap T f := by
  rintro ⟨T, hT⟩
  have hval : Supports T (f T) := by
    simpa only [Finset.union_self] using supportsMap_apply hT (supports_finset A T)
  let b := f (insert (f T) T)
  have hb : b ∉ insert (f T) T := hfresh _
  have hbT : b ∉ T := fun h => hb (Finset.mem_insert_of_mem h)
  have hba : b ≠ f T := fun h => hb (h ▸ Finset.mem_insert_self _ _)
  have hfix := swap_smul_eq_of_supports hval (hfresh T) hbT
  exact hba (by simpa only [Perm.smul_atom, Perm.swap_apply_left] using hfix)

-- A direct truth-valued certificate bridges through the existing tagged discrete carrier.
theorem supportsPred_iff_tagged {A : Type u} {X : Type v}
    [MulAction (Perm A) X] (S : Finset A) (P : X → Prop) :
    SupportsPred S P ↔ SupportsMap S (fun x => (Discrete.mk (P x) : Discrete A Prop)) := by
  constructor
  · intro h π hfix x
    exact congrArg Discrete.mk (propext (h π hfix x))
  · intro h π hfix x
    exact Iff.of_eq (congrArg Discrete.val (h π hfix x))

theorem mem_smul_set_iff {G : Type u} [Group G] {X : Type v} [MulAction G X]
    (g : G) (P : Set X) (x : X) : x ∈ g • P ↔ g⁻¹ • x ∈ P := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa only [inv_smul_smul] using hy
  · intro h
    exact ⟨g⁻¹ • x, h, smul_inv_smul g x⟩

theorem supportsPred_iff_subset {A : Type u} {X : Type v}
    [MulAction (Perm A) X] (S : Finset A) (P : X → Prop) :
    SupportsPred S P ↔ Supports S {x | P x} := by
  constructor
  · intro h
    apply (supports_iff _ _).2
    intro π hfix
    ext x
    rw [mem_smul_set_iff]
    have hp := h π hfix (π⁻¹ • x)
    simpa only [smul_inv_smul, Set.mem_ofPred_eq] using hp.symm
  · intro h π hfix x
    have heq := (supports_iff _ _).1 h π hfix
    have hp := congrArg (fun P : Set X => π • x ∈ P) heq
    simpa only [mem_smul_set_iff, inv_smul_smul, Set.mem_ofPred_eq] using (Iff.of_eq hp).symm

-- All subsets of atoms form an acted-on carrier, but not a nominal carrier.
theorem subset_projection_counterexample {A : Type u} [DecidableEq A]
    (P : A → Prop) (hP : Set.Infinite {a | P a})
    (hnP : Set.Infinite {a | ¬ P a}) :
    SupportsMap (Y := Set A) (∅ : Finset A) (Prod.fst : Set A × Discrete A Unit → Set A) ∧
      ¬ ∃ S : Finset A, SupportsMap S (fun _ : Discrete A Unit => {a | P a}) := by
  let : Nonempty (Discrete A Unit) := ⟨⟨()⟩⟩
  apply projection_sections_boundary
  rintro ⟨S, hS⟩
  exact infinite_coinfinite_unsupported P hP hnP ⟨S, (supportsPred_iff_subset S P).2 hS⟩

theorem concrete_unsupported_predicate :
    ¬ ∃ S : Finset (Nat × Bool), SupportsPred S (fun p : Nat × Bool => p.2 = true) := by
  apply infinite_coinfinite_unsupported
  · apply (Set.infinite_range_of_injective (f := fun n : Nat => (n, true))
      (fun _ _ h => congrArg Prod.fst h)).mono
    rintro _ ⟨n, rfl⟩
    rfl
  · apply (Set.infinite_range_of_injective (f := fun n : Nat => (n, false))
      (fun _ _ h => congrArg Prod.fst h)).mono
    rintro _ ⟨n, rfl⟩
    simp

#print axioms projection_sections_boundary
#print axioms equality_sections_boundary
#print axioms fixed_atom_predicate_supported_not_invariant
#print axioms constants_injective_iff
#print axioms infinite_coinfinite_unsupported
#print axioms no_supported_fresh_selector
#print axioms supportsPred_iff_tagged
#print axioms supportsPred_iff_subset
#print axioms subset_projection_counterexample
#print axioms concrete_unsupported_predicate
end F05Boundaries
