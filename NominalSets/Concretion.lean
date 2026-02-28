import NominalSets.NameAbstraction

/-!
# Concretion for Name Abstractions

Given a name abstraction `F : NameAbs α X`, the **concretion** `F ⊙ a` attempts to
extract the body of `F` at atom `a`. It returns `some x` when `a` is the binder or
is fresh for the body, and `none` otherwise.

## Main definitions

* `concreteAt F a` — concretion of `F` at `a`, as `Option X`; notation `F ⊙ a`.

## Main results

* `concreteAt_abs_self` — `(abs a x) ⊙ a = some x`.
* `concreteAt_abs_fresh` — `a' ≠ a → a' # x → (abs a x) ⊙ a' = some (swap a a' • x)`.
* `concreteAt_abs_not_fresh` — `a' ≠ a → a' ∈ supp x → (abs a x) ⊙ a' = none`.
* `abs_concreteAt_eq` — `a # F → ∃ y, F ⊙ a = some y ∧ F = abs a y` (Proposition 4.9).
* `concreteAt_none_iff` — `F ⊙ a = none ↔ ¬ a # F`.
* `abs_of_concreteAt_eq_some` — `F ⊙ a = some y → F = abs a y`.
* `concreteAt_get` — `F = abs a ((F ⊙ a).get h)` when `a # F`.
* `concreteAt_equivariant` — `π • (F ⊙ a) = (π • F) ⊙ (π • a)`.
* `nameAbs_ext` — extensionality via freshness quantifier (equation 4.16).
* `liftAbs` — functorial map `⟪a⟫ x ↦ ⟪a⟫ f x` for equivariant `f`.
* `liftAbs_abs` — `liftAbs f hf (⟪a⟫ x) = ⟪a⟫ f x`.
* `liftAbs_equivariant` — `liftAbs f hf` is equivariant.
* `liftAbs_unique` — universal property: uniqueness of `liftAbs`.
* `liftAbs_concreteAt` — `(liftAbs f hf F) ⊙ a = Option.map f (F ⊙ a)` when `a # F`.
* `liftAbs_id` — `liftAbs id _ = id`.
* `liftAbs_comp` — `liftAbs g _ ∘ liftAbs f _ = liftAbs (g ∘ f) _`.
* `liftAbs_injective` — injective `f` implies injective `liftAbs f`.
* `liftAbs_surjective` — surjective `f` implies surjective `liftAbs f`.

## References

* [A. M. Pitts, *Nominal Sets*][Pitts2013], Definition 4.7, Proposition 4.9, equation 4.16.
-/

namespace NominalSets

open MulAction PermType

universe u

variable {α : Type u} [Name α] {X : Type u} [Nominal α X]

namespace NameAbs

/-! ### Concretion (Pitts, Definition 4.7 / Proposition 4.9) -/

/-- **Concretion** of a name abstraction at atom `a`: if `a` is the binder, returns the body;
otherwise returns `none`. -/
noncomputable def concreteAt (F : NameAbs α X) (a' : α) : Option X :=
  Quotient.liftOn F
    (fun ⟨a, x⟩ ↦
      if a' = a then some x
      -- a # x is not decidable since it is defined ∩ for any set. Even though supp isn't computable
      -- since it is a finset, set membership is decidable.
      else if a' ∉ supp x then some (swap a a' • x)
      else none)
    (fun ⟨a₁, x₁⟩ ⟨a₂, x₂⟩ h ↦ by
      have heq : abs a₁ x₁ = abs a₂ x₂ := Quotient.sound h
      rw [abs_eq_iff] at heq
      rcases heq with ⟨rfl, rfl⟩ | ⟨hne, hfresh, rfl⟩
      · rfl
      · -- a₁ ≠ a₂, a₁ # (a₂, x₂), body is swap a₁ a₂ • x₂
        simp only [fresh_prod_right, fresh_atoms] at hfresh
        obtain ⟨_, ha₁x₂⟩ := hfresh
        by_cases ha₁ : a' = a₁
        · subst ha₁
          have ha'x₂ : a' ∉ supp x₂ := (fresh_atom_left a' x₂).mp ha₁x₂
          simp only [↓reduceIte, hne, ha'x₂, not_false_eq_true, ↓reduceIte]
          rw [swap_comm]
        · by_cases ha₂ : a' = a₂
          · subst ha₂
            have ha'ne : a' ≠ a₁ := Ne.symm hne
            have ha'notin : a' ∉ supp (swap a₁ a' • x₂) := by
              rw [mem_supp_smul, swap_inv]; simp only [swap_apply_right]
              exact (fresh_atom_left a₁ x₂).mp ha₁x₂
            simp only [ha'ne, ha'notin, not_false_eq_true, ↓reduceIte]
            rw [← mul_smul, swap_mul_self, one_smul]
          · -- a' ≠ a₁, a' ≠ a₂: swap a₁ a₂ fixes a', so membership is the same
            have hfix : (swap a₁ a₂) • a' = a' :=
              swap_apply_of_ne (fun h ↦ ha₁ h) (fun h ↦ ha₂ h)
            have hmem' : a' ∈ supp (swap a₁ a₂ • x₂) ↔ a' ∈ supp x₂ := by
              rw [mem_supp_smul, swap_inv, hfix]
            simp only [ha₁, ha₂, ↓reduceIte]
            -- align the decidable condition on both sides
            simp only [show a' ∉ supp (swap a₁ a₂ • x₂) ↔ a' ∉ supp x₂ from not_congr hmem']
            split_ifs with hfx
            · rfl
            · congr 1
              calc swap a₁ a' • swap a₁ a₂ • x₂
                  = (swap a₁ a' * swap a₁ a₂) • x₂ := by rw [mul_smul]
                _ = (swap a₂ a' * swap a₁ a') • x₂ := by rw [swap_mul_swap_comm hne ha₁ ha₂]
                _ = swap a₂ a' • (swap a₁ a' • x₂) := by rw [mul_smul]
                _ = swap a₂ a' • x₂ := by rw [fresh_swap ha₁x₂ ((fresh_atom_left a' x₂).mpr hfx)]
            )

/-- Notation `F ⊙ a` for concretion of `F` at `a`. -/
scoped infixl:90 " ⊙ " => NominalSets.NameAbs.concreteAt

/-- Concretion of `abs a x` at `a` returns `some x`. -/
@[simp]
theorem concreteAt_abs_self (a : α) (x : X) : (abs a x) ⊙ a = some x := by
  unfold concreteAt abs
  simp only [Quotient.liftOn_mk, ↓reduceIte]

/-- If `a' ≠ a` and `a' # x`, then concretion at `a'` gives `some (swap a a' • x)`. -/
@[simp]
theorem concreteAt_abs_fresh {a a' : α} {x : X} (hne : a' ≠ a) (hfresh : a' # x) :
    (abs a x) ⊙ a' = some (swap a a' • x) := by
  unfold concreteAt abs
  simp only [Quotient.liftOn_mk, hne, ↓reduceIte, (fresh_atom_left a' x).mp hfresh, not_false_eq_true]

/-- If `a' ≠ a` and `a' ∈ supp x`, then concretion at `a'` gives `none`. -/
@[simp]
theorem concreteAt_abs_not_fresh {a a' : α} {x : X} (hne : a' ≠ a) (hmem : a' ∈ supp x) :
    (abs a x) ⊙ a' = none := by
  unfold concreteAt abs
  simp only [Quotient.liftOn_mk, hne, ↓reduceIte]
  exact if_neg (not_not.mpr hmem)

/-- Concretion at a fresh atom: if `a # F`, then `F ⊙ a = some y` for a unique `y`, and `F = abs a y`. This is Pitts' Proposition 4.9. -/
theorem abs_concreteAt_eq {F : NameAbs α X} {a : α} (ha : a # F) :
    ∃ y, F ⊙ a = some y ∧ F = abs a y := by
  induction F using ind with | _ b y =>
  rw [fresh_abs] at ha
  rcases ha with rfl | hay
  · -- a = b: concretion at binder
    exact ⟨y, concreteAt_abs_self a y, rfl⟩
  · -- a # y, a ≠ b (if a = b then a ∈ supp (abs a y) but a # abs a y, contradiction)
    by_cases hab : a = b
    · subst hab; exact ⟨y, concreteAt_abs_self a y, rfl⟩
    · refine ⟨swap b a • y, concreteAt_abs_fresh hab hay, ?_⟩
      rw [abs_eq_iff]
      have hbsy : b # swap b a • y := by
        rw [fresh_atom_left, mem_supp_smul, swap_inv, swap_apply_left]
        exact (fresh_atom_left a y).mp hay
      exact Or.inr ⟨Ne.symm hab,
        fresh_prod_right.mpr ⟨(fresh_atoms b a).mpr (Ne.symm hab), hbsy⟩,
        by rw [← mul_smul, swap_mul_self, one_smul]⟩

/-- If `a' ∉ supp F ∪ {a}`, concretion at `a'` gives `none` or equals concretion at `a`
up to a swap. -/
theorem concreteAt_eq_none_of_not_fresh {F : NameAbs α X} {a : α} (ha : ¬ a # F) :
    F ⊙ a = none := by
  induction F using ind with | _ b y =>
  rw [fresh_abs] at ha
  push_neg at ha
  obtain ⟨hab, hay⟩ := ha
  exact concreteAt_abs_not_fresh hab (not_not.mp ((fresh_atom_left a y).not.mp hay))

/-- Concretion is `none` iff the atom is not fresh. -/
@[simp]
theorem concreteAt_none_iff {F : NameAbs α X} {a : α} : F ⊙ a = none ↔ ¬ a # F :=
  ⟨fun h ha => by obtain ⟨y, hy, _⟩ := abs_concreteAt_eq ha; simp [hy] at h,
   concreteAt_eq_none_of_not_fresh⟩

/-- Concretion is `some` iff the atom is fresh. -/
@[simp]
theorem concreteAt_isSome_iff {F : NameAbs α X} {a : α} :
    (F ⊙ a).isSome = true ↔ a # F := by
  rw [Option.isSome_iff_ne_none, ne_eq, concreteAt_none_iff, not_not]

/-- Variant of `concreteAt_abs_self` with an explicit equality hypothesis. -/
theorem concreteAt_abs_eq {a a' : α} {x : X} (h : a' = a) :
    (abs a x) ⊙ a' = some x :=
  h ▸ concreteAt_abs_self a x

/-- Injectivity of concretion: if two concretions at the same atom give `some`, the
results agree. -/
theorem concreteAt_injective {F : NameAbs α X} {a : α} {y z : X}
    (hy : F ⊙ a = some y) (hz : F ⊙ a = some z) : y = z :=
  Option.some_injective _ (hy ▸ hz)

/-- If concretion at `a` returns `some y`, then `F = abs a y`. -/
theorem abs_of_concreteAt_eq_some {F : NameAbs α X} {a : α} {y : X}
    (h : F ⊙ a = some y) : F = abs a y := by
  have ha : a # F := concreteAt_isSome_iff.mp (by simp [h])
  obtain ⟨y', hy', heq⟩ := abs_concreteAt_eq ha
  rw [heq]; congr 1
  exact concreteAt_injective hy' h

/-- Extracting the concretion value when `a # F`: `Option.get` of `F ⊙ a` recovers the
body witnessed by `abs_concreteAt_eq`. -/
theorem concreteAt_get {F : NameAbs α X} {a : α} (_ha : a # F)
    (h : (F ⊙ a).isSome := by simp [concreteAt_isSome_iff, _ha]) :
    F = abs a ((F ⊙ a).get h) :=
  abs_of_concreteAt_eq_some (Option.some_get h).symm

/-- Concretion is equivariant: `π • (F ⊙ a) = (π • F) ⊙ (π • a)`. -/
@[simp]
theorem concreteAt_equivariant (π : FinitePerm α) (F : NameAbs α X) (a : α) :
    π • (F ⊙ a) = (π • F) ⊙ (π • a) := by
  induction F using ind with | _ b x =>
  simp only [abs_equivariant]
  by_cases hab : a = b
  · subst hab; simp
  · by_cases hfx : a # x
    · simp only [concreteAt_abs_fresh hab hfx,
          concreteAt_abs_fresh ((smul_ne_iff π a b).mpr hab)
            ((fresh_equivariant_iff π).mpr hfx),
          option_smul_some]
      congr 1
      rw [← swap_equivariant π b a, conj_smul, ← mul_smul' π (swap b a) x,
          mul_smul' (π * swap b a) π⁻¹ (π • x), PermType.inv_smul_smul]
    · have hmem := not_not.mp ((fresh_atom_left a x).not.mp hfx)
      have hπmem : π • a ∈ supp (π • x) :=
        (mem_supp_smul π (π • a)).mpr (by simpa using hmem)
      rw [concreteAt_abs_not_fresh hab hmem, option_smul_none,
          concreteAt_abs_not_fresh ((smul_ne_iff π a b).mpr hab) hπmem]

/-! ### Extensionality (Pitts, equation 4.16) -/

/-- **Name-abstraction extensionality**: two abstractions are equal iff for fresh-enough
atoms `c`, their concretions at `c` agree. -/
theorem nameAbs_ext {F G : NameAbs α X} : F = G ↔ (И c, F ⊙ c = G ⊙ c) := by
  constructor
  · intro h; subst h; exact freshQuantifier_of_forall (fun _ ↦ rfl)
  · intro hFQ
    induction F using ind with | _ a₁ x₁ =>
    induction G using ind with | _ a₂ x₂ =>
    apply Quotient.sound
    change AlphaEqv a₁ x₁ a₂ x₂; unfold AlphaEqv
    have hfreshFQ : FreshQuantifier (fun c ↦ c # (a₁, x₁, a₂, x₂)) := fresh_atom_cofinite (a₁, x₁, a₂, x₂)
    apply freshQuantifier_mono _ (freshQuantifier_and.mpr ⟨hfreshFQ, hFQ⟩)
    intro c ⟨hcfresh, hceq⟩
    simp only [fresh_prod_right, fresh_atoms] at hcfresh
    obtain ⟨hca₁, hcx₁, hca₂, hcx₂⟩ := hcfresh
    have h₁ : (abs a₁ x₁) ⊙ c = some (swap a₁ c • x₁) := concreteAt_abs_fresh hca₁ hcx₁
    have h₂ : (abs a₂ x₂) ⊙ c = some (swap a₂ c • x₂) := concreteAt_abs_fresh hca₂ hcx₂
    rw [h₁, h₂] at hceq
    exact Option.some_injective _ hceq

/-! ### Functorial action (map) -/

/-- Functorial map: given an equivariant function `f : X → Y`, lift it to
`NameAbs α X → NameAbs α Y` by `⟪a⟫ x ↦ ⟪a⟫ f x`. -/
noncomputable def liftAbs {Y : Type u} [Nominal α Y] (f : X → Y)
    (hf : ∀ (π : FinitePerm α) (x : X), f (π • x) = π • f x) : NameAbs α X → NameAbs α Y :=
  fun F ↦ Quotient.liftOn F
    (fun p ↦ abs p.1 (f p.2))
    (fun ⟨a₁, x₁⟩ ⟨a₂, x₂⟩ h ↦ by
      have heq : abs a₁ x₁ = abs a₂ x₂ := Quotient.sound h
      rw [abs_eq_iff] at heq
      rcases heq with ⟨rfl, rfl⟩ | ⟨hne, hfresh, hrename⟩
      · rfl
      · rw [abs_eq_iff]
        refine Or.inr ⟨hne, ?_, ?_⟩
        · -- a₁ # (a₂, f x₂): follows from a₁ # (a₂, x₂) and supp (f x₂) ⊆ supp x₂
          simp only [fresh_prod_right, fresh_atoms] at hfresh ⊢
          obtain ⟨hne', hfx₂⟩ := hfresh
          exact ⟨hne', (fresh_atom_left a₁ (f x₂)).mpr
            (fun h ↦ (fresh_atom_left a₁ x₂).mp hfx₂ (supp_map_le f hf x₂ h))⟩
        · -- f x₁ = swap a₁ a₂ • f x₂
          rw [hrename, hf])

/-- `map` commutes with `abs`: `map f (⟪a⟫ x) = ⟪a⟫ f x`. -/
@[simp]
theorem liftAbs_abs {Y : Type u} [Nominal α Y] (f : X → Y)
    (hf : ∀ (π : FinitePerm α) (x : X), f (π • x) = π • f x)
    (a : α) (x : X) : liftAbs f hf (abs a x) = abs a (f x) := by
  simp [liftAbs, abs]

/-- `map` is equivariant. -/
@[simp]
theorem liftAbs_equivariant {Y : Type u} [Nominal α Y] (f : X → Y)
    (hf : ∀ (π : FinitePerm α) (x : X), f (π • x) = π • f x)
    (π : FinitePerm α) (F : NameAbs α X) :
    liftAbs f hf (π • F) = π • liftAbs f hf F := by
  induction F using ind with | _ a x => simp [hf]

/-- Uniqueness of `liftAbs`: any function that agrees with `liftAbs f hf` on all
representatives must equal it. -/
theorem liftAbs_unique {Y : Type u} [Nominal α Y] (f : X → Y)
    (hf : ∀ (π : FinitePerm α) (x : X), f (π • x) = π • f x)
    (g : NameAbs α X → NameAbs α Y)
    (hg : ∀ (a : α) (x : X), g (abs a x) = abs a (f x)) :
    g = liftAbs f hf := by
  funext F; induction F using ind with | _ a x =>
  rw [hg, liftAbs_abs]

/-- Map–concretion interaction for fresh atoms:
`(liftAbs f hf F) ⊙ a = Option.map f (F ⊙ a)` when `a # F`. -/
theorem liftAbs_concreteAt {Y : Type u} [Nominal α Y] (f : X → Y)
    (hf : ∀ (π : FinitePerm α) (x : X), f (π • x) = π • f x)
    (F : NameAbs α X) (a : α) (ha : a # F) :
    (liftAbs f hf F) ⊙ a = Option.map f (F ⊙ a) := by
  induction F using ind with | _ b x =>
  rw [liftAbs_abs]
  rw [fresh_abs] at ha
  rcases ha with rfl | hax
  · simp
  · have hfx : a # f x := (fresh_atom_left a (f x)).mpr
      (fun h ↦ (fresh_atom_left a x).mp hax (supp_map_le f hf x h))
    by_cases hab : a = b
    · subst hab; simp
    · simp only [concreteAt_abs_fresh hab hax, concreteAt_abs_fresh hab hfx,
        Option.map_some, hf]

/-- Support bound for `liftAbs`: `supp (liftAbs f hf F) ⊆ supp F`. -/
theorem supp_liftAbs_le {Y : Type u} [Nominal α Y] (f : X → Y)
    (hf : ∀ (π : FinitePerm α) (x : X), f (π • x) = π • f x)
    (F : NameAbs α X) : supp (liftAbs f hf F) ⊆ supp F := by
  induction F using ind with | _ a x =>
  simp only [liftAbs_abs, supp_abs]
  exact Finset.sdiff_subset_sdiff (supp_map_le f hf x) (Finset.Subset.refl _)

/-- И-quantified version of `liftAbs_concreteAt`: for cofinitely many `a`,
`(liftAbs f hf F) ⊙ a = Option.map f (F ⊙ a)`. -/
theorem liftAbs_concreteAt_freshQuantifier {Y : Type u} [Nominal α Y] (f : X → Y)
    (hf : ∀ (π : FinitePerm α) (x : X), f (π • x) = π • f x)
    (F : NameAbs α X) :
    И a, (liftAbs f hf F) ⊙ a = Option.map f (F ⊙ a) :=
  freshQuantifier_mono (fun a ha ↦ liftAbs_concreteAt f hf F a ha) (fresh_atom_cofinite F)

/-- `liftAbs id` is the identity. -/
@[simp]
theorem liftAbs_id :
    liftAbs (id : X → X) (fun _ _ ↦ rfl) = id := by
  funext F; induction F using ind with | _ a x => simp

/-- `liftAbs` composes: `liftAbs g hg ∘ liftAbs f hf = liftAbs (g ∘ f) _`. -/
theorem liftAbs_comp {Y Z : Type u} [Nominal α Y] [Nominal α Z]
    (f : X → Y) (hf : ∀ (π : FinitePerm α) (x : X), f (π • x) = π • f x)
    (g : Y → Z) (hg : ∀ (π : FinitePerm α) (y : Y), g (π • y) = π • g y)
    (F : NameAbs α X) :
    liftAbs g hg (liftAbs f hf F) =
      liftAbs (g ∘ f) (fun π x ↦ by simp [Function.comp, hf, hg]) F := by
  induction F using ind with | _ a x => simp

/-- If `f` is injective, then `liftAbs f hf` is injective. -/
theorem liftAbs_injective {Y : Type u} [Nominal α Y] {f : X → Y}
    (hf : ∀ (π : FinitePerm α) (x : X), f (π • x) = π • f x)
    (hinj : Function.Injective f) :
    Function.Injective (liftAbs f hf) := by
  intro F G h
  rw [nameAbs_ext]
  have hFQ := nameAbs_ext.mp h  -- И c, (liftAbs f hf F) ⊙ c = (liftAbs f hf G) ⊙ c
  apply freshQuantifier_mono _ (freshQuantifier_and.mpr ⟨fresh_atom_cofinite F,
    freshQuantifier_and.mpr ⟨fresh_atom_cofinite G, hFQ⟩⟩)
  intro c ⟨hcF, hcG, hceq⟩
  rw [liftAbs_concreteAt f hf F c hcF, liftAbs_concreteAt f hf G c hcG] at hceq
  exact Option.map_injective hinj hceq

/-- If `f` is surjective, then `liftAbs f hf` is surjective. -/
theorem liftAbs_surjective {Y : Type u} [Nominal α Y] {f : X → Y}
    (hf : ∀ (π : FinitePerm α) (x : X), f (π • x) = π • f x)
    (hsurj : Function.Surjective f) :
    Function.Surjective (liftAbs f hf) := by
  intro G; induction G using ind with | _ a y =>
  obtain ⟨x, rfl⟩ := hsurj y
  exact ⟨abs a x, liftAbs_abs f hf a x⟩

end NameAbs

end NominalSets
