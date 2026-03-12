import NominalSets.NameAbstraction
import NominalSets.Concretion

import Mathlib.Tactic.Linarith.Frontend

/-!
# Freshness Condition for Binders

This file contains Theorem 4.15 (the general freshness condition for binders, FCB) and
Corollary 4.17 (its equivariant specialisation).

Structural isomorphisms of the name abstraction functor, the separated product, and
the adjunctions are in `NominalSets.Structural`.

## Main definitions

* `NameAbs.FCB F` — the freshness condition for binders predicate: `И a, ∀ x, ∃ y, F (a, x) = some y ∧ a # y` (equation 4.32).
* `NameAbs.liftFCB F hFCB` — the unique finitely supported function `[A]X →ᶠˢ Y` extending `F` (Theorem 4.15).
* `NameAbs.liftFresh f hEquiv hFresh` — the equivariant elimination principle `[A]X → Y` (Corollary 4.17).
* `NameAbs.liftFresh_NFun f hEquiv hFresh` — `liftFresh` packaged as an `NFun` with empty support.
* `NameAbs.liftFreshParam f hEquiv hFresh` — parametric form of Corollary 4.17 with a parameter `z : Z`.

## Main results

### Freshness condition for binders (Pitts, Theorem 4.15)
* `liftFCB_abs` — `И a, ∀ x, liftFCB F hFCB (⟪a⟫ x) = F (a, x)` (property 4.33).
* `liftFCB_abs_of_fresh` — `a # F → some (liftFCB F hFCB (⟪a⟫ x)) = F (a, x)` (from 4.36).
* `liftFCB_abs_of_fresh_eq` — `a # F → F (a, x) = some y → liftFCB F hFCB (⟪a⟫ x) = y`.
* `liftFCB_abs_unwrap` — cofinite form: `И a, ∀ x y, F (a, x) = some y → liftFCB F hFCB (⟪a⟫ x) = y`.
* `liftFCB_concreteAt` — `a # F → z ⊙ a = some x → some (liftFCB F hFCB z) = F (a, x)`.
* `supp_liftFCB_le` — `supp (liftFCB F hFCB) ⊆ supp F`.
* `liftFCB_unique` — uniqueness of `liftFCB`.
* `liftFCB_eq_iff` — `liftFCB F hFCB z = y ↔ (И a, ∃ x, z = ⟪a⟫x ∧ some y = F(a,x))` (eq. 4.35).
* `fresh_liftFCB` — `a # F → a # liftFCB F hFCB`.
* `FCB_smul` — `FCB F → FCB (π • F)`.
* `FCB_fresh` — `FCB F → И a, ∀ x, a # F (a, x)`.
* `FCB_congr'` — `F = G → (FCB F ↔ FCB G)`.
* `liftFCB_smul` — `π • liftFCB F hFCB = liftFCB (π • F) _`.
* `liftFCB_inj` — if `liftFCB F hF = liftFCB G hG`, then `И a, ∀ x, F (a, x) = G (a, x)`.
* `liftFCB_isEquivariant_of_supp_empty` — `liftFCB F hFCB` is equivariant when `supp F = ∅`.
* `liftFCB_map` — naturality: post-composing `F` with equivariant `g` commutes with the lift.
* `liftFCB_congr` — if `F = G` then `liftFCB F hF = liftFCB G hG`.

### FCB for total functions
* `FCB_of_total` — a total `F : (α × X) →ᶠˢ Y` with `∀ a x, a # F (a, x)` satisfies FCB after composing with `some`.

### Equivariant specialisation (Pitts, Corollary 4.17)
* `liftFresh_abs` — `liftFresh f _ _ (⟪a⟫ x) = f a x`.
* `liftFresh_equivariant` — `IsEquivariant α (liftFresh f _ _)`.
* `liftFresh_smul` — `π • liftFresh f _ _ z = liftFresh f _ _ (π • z)`.
* `liftFresh_unique` — uniqueness of `liftFresh`.
* `liftFresh_ext` — `liftFresh f _ _ = liftFresh g _ _ ↔ ∀ a x, f a x = g a x`.
* `liftFresh_congr` — pointwise-equal inputs give the same lift.
* `liftFresh_comp_equivariant` — post-composing with equivariant `g` commutes with `liftFresh`.
* `liftFresh_proj` — the lift of `(a, x) ↦ x` extracts the body.
* `liftFresh_NFun_apply` — `liftFresh_NFun f _ _ z = liftFresh f _ _ z`.
* `liftFresh_NFun_unique` — uniqueness of `liftFresh_NFun`.
* `supp_liftFresh_NFun` — `supp (liftFresh_NFun f _ _) = ∅`.
* `fresh_liftFresh_NFun` — every atom is fresh for `liftFresh_NFun f _ _`.

### Parametric form of Corollary 4.17 (Pitts, equations 4.38–4.39)
* `liftFreshParam` — `Z → [A]X → Y` lifting `f : Z → α → X → Y` with a parameter.
* `liftFreshParam_abs` — `И a, ∀ x, liftFreshParam f _ _ z (⟪a⟫ x) = f z a x`.
* `liftFreshParam_equivariant` — equivariance of `liftFreshParam` jointly in `z` and the abstraction.
* `liftFreshParam_unique` — uniqueness of `liftFreshParam`.

## References

* [A. M. Pitts, *Nominal Sets*][Pitts2013], Chapter 4, Sections 4.3–4.5.
-/

namespace NominalSets

open MulAction PermType

universe u

variable {α : Type u} [Name α] {X : Type u} [Nominal α X]

namespace NameAbs

/-! ### Freshness condition for binders (Pitts, Theorem 4.15) -/

section FCB

variable {Y : Type u} [Nominal α Y]

/-- When `π` fixes `F`, equivariance of `NFun` application on pairs simplifies to
`F (π • a, π • x) = π • F (a, x)`. Wraps `NFun.smul_apply_smul` + the fixpoint rewrite. -/
private theorem smul_nfun_pair_apply {Z : Type u} [Nominal α Z]
    (π : FinitePerm α) (F : NFun α (α × X) Z) (hπF : π • F = F) (a : α) (x : X) :
    F (π • a, π • x) = π • F (a, x) := by
  have := NFun.smul_apply_smul π F (a, x)
  rwa [hπF, PermType.prod_smul] at this

/- **Theorem 4.15 (Pitts, Section 4.5)**

**Freshness condition for binders**: Given a finitely supported function
`F : (α × X) →ᶠˢ Y` satisfying

    (Иa)(∀x) a # F(a, x)              — condition (4.32)

there is a unique finitely supported function `F̄ : [A]X →ᶠˢ Y` satisfying

    (Иa)(∀x) F(a, x) = F̄(⟨a⟩x)       — property (4.33)

Moreover `supp F̄ ⊆ supp F`. -/

/-- The **freshness condition for binders** (FCB, eq. 4.32): for cofinitely many atoms `a`,
the result `F(a, x)` is fresh for `a`, uniformly in `x`. -/
def FCB (F : NFun α (α × X) (Option Y)) : Prop := И a, ∀ x : X, ∃ y : Y, F (a, x) = some y ∧ a # y

/-- **Independence of representative** (well-definedness of `liftFCB`).

Given `F : (α × X) →ᶠˢ Option Y` (partial) satisfying the FCB condition, and two representations
of the same abstraction `z = ⟪c₁⟫y₁ = ⟪c₂⟫y₂` with `c₁ # F` and `c₂ # F`, then `F(c₁, y₁) = F(c₂, y₂)`.

**Proof outline:**

1. *Derive `И a, ∀ x, a # F(a,x)`:* The FCB condition gives `∃ y, F(a,x) = some y ∧ a # y`; rewriting by `fresh_some` yields `a # F(a,x)`.
2. *Pick a "good" third atom `c₃`:* Choose `c₃ # (F, z)` that also satisfies the FCB freshness via `freshQuantifier_and` + `freshQuantifier_exists`.
3. *Obtain a third representative:* Since `c₃ # z`, `abs_concreteAt_eq_forall` gives `z = ⟪c₃⟫y₃`.
4. *Reduce both sides to `F(c₃, y₃)` via an auxiliary conjugation argument:*
   For any `c # F` with `⟪c⟫w = ⟪c₃⟫y₃`, either `c = c₃` (so `w = y₃` by
   `abs_same_name_iff`) or `c ≠ c₃` (so `w = swap c c₃ • y₃` by `abs_eq_iff`).
   In the latter case, `swap c c₃` fixes `F` (both atoms are fresh), and equivariance
   (`NFun.smul_apply_smul`) gives `F(c, w) = swap c c₃ • F(c₃, y₃)`. The swap acts
   trivially because `c # F(c₃, y₃)` (by `supp_apply_le`) and `c₃ # F(c₃, y₃)`
   (by FCB).
5. *Conclude:* `F(c₁, y₁) = F(c₃, y₃) = F(c₂, y₂)`. -/
private theorem liftFCB_val_indep {F : NFun α (α × X) (Option Y)} (hFCB : FCB F) {z : NameAbs α X}
    {c₁ : α} (hc₁F : c₁ # F) {y₁ : X} (h₁ : z = abs c₁ y₁)
    {c₂ : α} (hc₂F : c₂ # F) {y₂ : X} (h₂ : z = abs c₂ y₂) :
    F (c₁, y₁) = F (c₂, y₂) := by
  -- Derive И a, ∀ x, a # F(a,x) from the FCB condition
  have hFCB' : И a, ∀ x : X, a # F (a, x) :=
    freshQuantifier_mono (fun a ha x ↦ by obtain ⟨y, hy, hay⟩ := ha x; rw [hy]; exact fresh_some.mpr hay) hFCB
  -- Pick c₃ # (F, z) satisfying the FCB freshness condition
  have hBoth : И a, (a # (F, z)) ∧ (∀ x : X, a # F (a, x)) :=
    freshQuantifier_and.mpr ⟨fresh_atom_cofinite (F, z), hFCB'⟩
  obtain ⟨c₃, hc₃fresh, hc₃FCB⟩ := freshQuantifier_exists hBoth
  split_fresh hc₃fresh with hc₃F hc₃z
  -- c₃ # z gives z = ⟪c₃⟫y₃ via abs_concreteAt_eq_forall
  obtain ⟨y₃, _, hz₃⟩ := abs_concreteAt_eq_forall c₃ hc₃z
  -- Reduce both sides to F(c₃, y₃) via conjugation
  suffices aux : ∀ (c : α) (w : X), c # F → abs c w = abs c₃ y₃ → F (c, w) = F (c₃, y₃) by
    calc F (c₁, y₁) = F (c₃, y₃) := aux c₁ y₁ hc₁F (h₁.symm ▸ hz₃)
      _ = F (c₂, y₂) := (aux c₂ y₂ hc₂F (h₂.symm ▸ hz₃)).symm
  intro c w hcF habsEq
  by_cases heq : c = c₃
  · subst heq; rw [abs_same_name_iff] at habsEq; rw [habsEq]
  · rw [abs_eq_iff] at habsEq
    obtain (⟨h, _⟩ | ⟨_, hfreshc, hweq⟩) := habsEq
    · exact absurd h heq
    · -- w = swap c c₃ • y₃, swap c c₃ fixes F
      have hFixF : swap c c₃ • F = F := fresh_swap hcF hc₃F
      have key := smul_nfun_pair_apply (swap c c₃) F hFixF c₃ y₃
      simp only [swap_apply_right] at key
      rw [hweq, key]
      exact fresh_swap (NFun.fresh_apply hcF hfreshc) (hc₃FCB y₃)

/-- **Auxiliary NFun for `liftFCB`** (Pitts, equation 4.34).

For fixed `F : (α × X) →ᶠˢ Option Y` and `z : [A]X`, defines the finitely supported partial function `G : α →ᶠˢ Option Y` by

    `G(a) = z ⊙ a >>= (fun x ↦ F(a, x))`

i.e., concretise `z` at `a` (getting `some x` when `a # z`, `none` otherwise), then apply `F(a, ·)`. When `a # z`, this reduces to `F(a, z@a)`.

The support witness is `supp F ∪ supp z`. The equivariance proof proceeds by cases on `z ⊙ a`:
- `none`: both sides are `none`.
- `some x`: reduces to `F(π•a, π•x) = π • F(a,x)` by `NFun.smul_apply_smul`.

Applying the partial freshness theorem (`freshF`) to this `G` produces `liftFCB_fun`. -/
private noncomputable def liftFCB_nfun (F : NFun α (α × X) (Option Y)) (z : NameAbs α X) : NFun α α (Option Y) :=
  NFun.ofSupports ⟨fun a ↦ z ⊙ a >>= fun x ↦ F (a, x)⟩ (supp F ∪ supp z)
    (by
      rw [supports_pfun_iff]
      intro π hπ a
      have hπF : π • F = F := supp_supports F π (fun b hb ↦ by
        rw [PermType.atoms_smul]; exact hπ (Finset.mem_coe.mpr (Finset.mem_union_left _ hb)))
      have hπz : π • z = z := supp_supports z π (fun b hb ↦ by
        rw [PermType.atoms_smul]; exact hπ (Finset.mem_coe.mpr (Finset.mem_union_right _ hb)))
      change (z ⊙ (π • a) >>= fun x ↦ F (π • a, x)) = π • (z ⊙ a >>= fun x ↦ F (a, x))
      rw [show z ⊙ (π • a) = π • (z ⊙ a) from by
        conv_lhs => rw [← hπz]; exact (concreteAt_equivariant π z a).symm]
      cases z ⊙ a with
      | none => rfl
      | some x =>
        change F (π • a, π • x) = π • F (a, x)
        exact smul_nfun_pair_apply π F hπF a x)

@[simp] private theorem liftFCB_nfun_apply (F : NFun α (α × X) (Option Y)) (z : NameAbs α X) (a : α) :
    liftFCB_nfun F z a = (z ⊙ a >>= fun x ↦ F (a, x)) :=
  NFun.ofSupports_apply _ _ _ _

/-- **Freshness condition for `liftFCB_nfun`**: the partial function `G = liftFCB_nfun F z`
satisfies the hypothesis of the partial freshness theorem (FC), i.e., `И a, ∃ y, G(a) = some y ∧ a # y`.

**Proof:** For `a # (F, z)`, concretise `z` at `a` via `abs_concreteAt_eq_forall` to get
`z ⊙ a = some x` with `z = ⟪a⟫x`. Then `G(a) = F(a, x)`, and the FCB condition on `F` gives `∃ y, F(a, x) = some y ∧ a # y`.

This is the proof term that, paired with `liftFCB_nfun F z`, feeds into `freshF` to define `liftFCB_fun`. -/
private theorem liftFCB_nfun_fc (F : NFun α (α × X) (Option Y)) (hFCB : FCB F) (z : NameAbs α X) : FC (liftFCB_nfun F z) := by
  have hBoth : И a, a # (F, z) ∧ (∀ x : X, ∃ y : Y, F (a, x) = some y ∧ a # y) :=
    freshQuantifier_and.mpr ⟨fresh_atom_cofinite (F, z), hFCB⟩
  apply freshQuantifier_mono _ hBoth
  intro a ⟨hafz, hfcb⟩
  split_fresh hafz with haF haz
  obtain ⟨x, hconc, _⟩ := abs_concreteAt_eq_forall a haz
  obtain ⟨y, hFax, hay⟩ := hfcb x
  exact ⟨y, by simp only [liftFCB_nfun_apply, hconc]; exact hFax, hay⟩

/-- **The underlying function for `liftFCB`** (Pitts, equation 4.34).

Given `F : (α × X) →ᶠˢ Option Y` satisfying FCB, defines `F̄ : [A]X → Y` by

    `F̄(z) = freshF (liftFCB_nfun F z) (liftFCB_nfun_fc F hFCB z)`

That is, `F̄(z)` is the unique `y : Y` such that `И a, (liftFCB_nfun F z)(a) = some y`,
obtained from the partial freshness theorem. Informally: `F̄(z) = fresh a in F(a, z@a)`.

This is a bare function `[A]X → Y`; it is promoted to an `NFun` (with `supp F̄ ⊆ supp F`) in `liftFCB`. -/
private noncomputable def liftFCB_fun (F : NFun α (α × X) (Option Y)) (hFCB : FCB F) (z : NameAbs α X) : Y :=
  freshF (liftFCB_nfun F z) (liftFCB_nfun_fc F hFCB z)

/-- **Computation rule for `liftFCB_fun`**: when `a # F` and `z = ⟪a⟫x`,
`some (liftFCB_fun F hFCB z) = F(a, x)`.

**Proof outline:**

1. *Freshness theorem gives a spec:* `freshF_spec` yields `И b, G(b) = some (liftFCB_fun F hFCB z)` where `G = liftFCB_nfun F z`.
2. *Show `G` is cofinitely equal to `F(a, x)`:* For `b # (F, z)`, `abs_concreteAt_eq_forall` gives `z = ⟪b⟫y`, so `G(b) = F(b, y)`.
   Then `liftFCB_val_indep` (well-definedness) gives `F(b, y) = F(a, x)`. Hence `И b, G(b) = F(a, x)`.
3. *Conclude:* Both `И b, G(b) = some (liftFCB_fun ...)` and `И b, G(b) = F(a, x)` hold. Picking a common witness `b` gives `some (liftFCB_fun ...) = G(b) = F(a, x)`.

Note: the conclusion is `some`-wrapped because `F` returns `Option Y` while `liftFCB_fun` returns `Y` (the `some` is stripped by `freshF`). -/
private theorem liftFCB_fun_eq {F : NFun α (α × X) (Option Y)} (hFCB : FCB F)
    {z : NameAbs α X} {a : α} (haF : a # F) {x : X} (hz : z = abs a x) : some (liftFCB_fun F hFCB z) = F (a, x) := by
  have hspec := freshF_spec (liftFCB_nfun F z) (liftFCB_nfun_fc F hFCB z)
  -- Show И b, (liftFCB_nfun F z) b = F(a, x), then freshQuantifier_some_unique concludes.
  -- First, build И b, (liftFCB_nfun F z) b = F(a, x).
  have hgoal : И b, (liftFCB_nfun F z) b = F (a, x) := by
    apply freshQuantifier_mono _ (fresh_atom_cofinite (F, z))
    intro b hbfz
    split_fresh hbfz with hbF hbz
    obtain ⟨y, hconc, hzb⟩ := abs_concreteAt_eq_forall b hbz
    have heval : (liftFCB_nfun F z) b = F (b, y) := by simp [liftFCB_nfun_apply, hconc]
    rw [heval]
    exact liftFCB_val_indep hFCB hbF hzb haF hz
  -- hspec: И b, G b = some (freshF G _)   and   hgoal: И b, G b = F(a,x)
  -- Extract y from F(a,x) = some y via FCB, then use freshQuantifier_some_unique.
  obtain ⟨b, hb_spec, hb_goal⟩ := freshQuantifier_exists (freshQuantifier_and.mpr ⟨hspec, hgoal⟩)
  change some (freshF (liftFCB_nfun F z) (liftFCB_nfun_fc F hFCB z)) = F (a, x)
  rw [← hb_goal, hb_spec]

/-- **Theorem 4.15** (Pitts, Section 4.5): the **lifted function** `F̄ : [A]X →ᶠˢ Y`.

Given `F : (α × X) →ᶠˢ Option Y` satisfying the FCB condition (4.32), `liftFCB F hFCB`
is the unique finitely supported function `F̄ : [A]X →ᶠˢ Y` with `(Иa)(∀x) F̄(⟪a⟫x) = F(a, x)` (property 4.33) and `supp F̄ ⊆ supp F`.

**Construction:** Wraps `liftFCB_fun` (which computes `F̄(z) = freshF(liftFCB_nfun F z)`) into an `NFun` via `NFun.ofSupports` with support set `supp F`.

**Proof that `supp F` supports `liftFCB_fun`:** Must show that any `π` fixing `supp F` satisfies `F̄(π • z) = π • F̄(z)`.
1. Since `π` fixes `supp F`, we have `π • F = F`.
2. Pick `a # F` with `z = ⟪a⟫x` via `exists_fresh_rep`. Then `π•a # F` (since `π` fixes `supp F`) and `π • z = ⟪π•a⟫(π•x)`.
3. `liftFCB_fun_eq` gives `some(F̄(π•z)) = F(π•a, π•x)` and `some(F̄(z)) = F(a, x)`.
4. Equivariance of `F` gives `F(π•a, π•x) = π • F(a, x)`.
5. Chaining: `some(F̄(π•z)) = F(π•a, π•x) = π • F(a, x) = π • some(F̄(z)) = some(π • F̄(z))`, and `Option.some_injective` strips the `some`. -/
noncomputable def liftFCB (F : NFun α (α × X) (Option Y)) (hFCB : FCB F) : NFun α (NameAbs α X) Y :=
  NFun.ofSupports ⟨liftFCB_fun F hFCB⟩ (supp F)
    (by
      rw [supports_pfun_iff]
      intro π hπ z
      change liftFCB_fun F hFCB (π • z) = π • liftFCB_fun F hFCB z
      -- Step 1: π fixes supp F, so π • F = F
      have hπF : π • F = F := supp_supports F π (fun b hb => by
        rw [PermType.atoms_smul]; exact hπ (Finset.mem_coe.mpr hb))
      -- Step 2: fresh representative z = ⟪a⟫x with a # F, and π • z = ⟪π•a⟫(π•x)
      obtain ⟨a, x, haF, hz⟩ := exists_fresh_rep z F
      have hπaF : (π • a) # F := by rwa [← hπF, fresh_equivariant_iff]
      have hπz : π • z = abs (π • a) (π • x) := by rw [hz, abs_equivariant]
      -- Steps 3–5: chain some-wrapped equalities and inject
      have hlhs := liftFCB_fun_eq hFCB hπaF hπz
      have hrhs := liftFCB_fun_eq hFCB haF hz
      apply Option.some_injective
      calc some (liftFCB_fun F hFCB (π • z))
          = F (π • a, π • x) := hlhs
        _ = π • F (a, x) := smul_nfun_pair_apply π F hπF a x
        _ = π • some (liftFCB_fun F hFCB z) := by rw [hrhs]
        _ = some (π • liftFCB_fun F hFCB z) := by simp)

/-- **Computation rule for `liftFCB`**: if `a # F`, then
`some (liftFCB F hFCB ⟪a⟫x) = F (a, x)`. The equality lives at `Option Y` level
(the LHS is coerced via `Coe Y (Option Y)`). (From 4.36.) -/
@[simp]
theorem liftFCB_abs_of_fresh (F : NFun α (α × X) (Option Y)) (hFCB : FCB F)
    {a : α} (ha : a # F) (x : X) : liftFCB F hFCB ⟪a⟫x = F (a, x) := by
  change liftFCB_fun F hFCB (abs a x) = F (a, x); exact liftFCB_fun_eq hFCB ha rfl

/-- `liftFCB` agrees with `F` on representatives: for cofinitely many `a` and all `x`, `liftFCB F hFCB (⟪a⟫ x) = F (a, x)`. (Property 4.33.) -/
theorem liftFCB_abs (F : NFun α (α × X) (Option Y)) (hFCB : FCB F) : И a, ∀ x : X, liftFCB F hFCB ⟪a⟫x = F (a, x) :=
  freshQuantifier_mono (fun _ ha x ↦ liftFCB_abs_of_fresh F hFCB ha x) (fresh_atom_cofinite F)

/-- Support bound: `supp (liftFCB F hFCB) ⊆ supp F`. -/
@[grind .]
theorem supp_liftFCB_le (F : NFun α (α × X) (Option Y)) (hFCB : FCB F) : supp (liftFCB F hFCB) ⊆ supp F :=
  -- liftFCB is defined via NFun.ofSupports with support set `supp F`, so `supports (supp F) (liftFCB F hFCB)` holds by construction.
  supp_le (NFun.ofSupports_supports _ _ _)

/-- Uniqueness of `liftFCB`: any finitely supported function `G : [A]X →ᶠˢ Y` satisfying property (4.33) must equal `liftFCB F hFCB`. -/
theorem liftFCB_unique (F : NFun α (α × X) (Option Y)) (hFCB : FCB F)
    (G : NFun α (NameAbs α X) Y) (hG : И a, ∀ x : X, G ⟪a⟫x = F (a, x)) : G = liftFCB F hFCB := by
  ext z
  -- Pick b # (F, G) and z = ⟪b⟫x
  obtain ⟨b, x, hbFG, hz⟩ := exists_fresh_rep z (F, G)
  split_fresh hbFG with hbF hbG
  rw [hz]
  -- Pick c # (F, G, b, x) with ∀ x, some (G ⟪c⟫x) = F (c, x)
  obtain ⟨c, ⟨hcall, hGc'⟩⟩ := freshQuantifier_exists (freshQuantifier_and.mpr ⟨fresh_atom_cofinite (F, G, b, x), hG⟩)
  split_fresh hcall with hcF hcG hcb hcx
  -- swap b c fixes G and F (both atoms are fresh)
  have hswapG : swap b c • G = G := fresh_swap hbG hcG
  have hswapF : swap b c • F = F := fresh_swap hbF hcF
  have hGbx : some (G (abs b x)) = F (b, x) := by
    have key_G := NFun.smul_apply_smul (swap b c) G (abs b x)
    rw [hswapG, abs_equivariant, swap_apply_left] at key_G
    have key_F := smul_nfun_pair_apply (swap b c) F hswapF b x
    simp only [swap_apply_left] at key_F
    apply smul_injective (swap b c)
    simp only [option_smul_some]
    rw [← key_G, hGc', key_F]
  apply Option.some_injective
  rw [hGbx, ← liftFCB_abs_of_fresh F hFCB hbF x]

/-- If `a # F` then `a # liftFCB F hFCB`. Direct consequence of `supp_liftFCB_le`. -/
@[grind .]
theorem fresh_liftFCB {F : NFun α (α × X) (Option Y)} {hFCB : FCB F} {a : α} (ha : a # F) : a # liftFCB F hFCB :=
  fresh_of_supp_subset (supp_liftFCB_le F hFCB) ha

/-- Equivariance of the FCB predicate: if `FCB F` then `FCB (π • F)`. Analogous to `FC_smul`. -/
theorem FCB_smul (π : FinitePerm α) {F : NFun α (α × X) (Option Y)} (h : FCB F) : FCB (π • F) := by
  -- FCB (π • F) means: И a, ∀ x, ∃ y, (π • F)(a,x) = some y ∧ a # y
  -- Shift via freshQuantifier_smul_iff: enough to show for π⁻¹ • a
  apply freshQuantifier_mono _ ((freshQuantifier_smul_iff π).mp h)
  intro a ha x
  -- ha : ∀ x, ∃ y, F(π⁻¹ • a, x) = some y ∧ (π⁻¹ • a) # y
  obtain ⟨y, hFy, hay⟩ := ha (π⁻¹ • x)
  refine ⟨π • y, ?_, ?_⟩
  · -- (π • F)(a, x) = π • F(π⁻¹ • a, π⁻¹ • x) = π • some y = some (π • y)
    simp only [NFun.smul_apply, PermType.prod_smul]
    rw [hFy, option_smul_some]
  · -- a # (π • y) ← π • (π⁻¹ • a) # π • y ← (π⁻¹ • a) # y
    rw [show a = π • (π⁻¹ • a) from (PermType.smul_inv_smul π a).symm]
    exact fresh_equivariant π hay

/-- Equivariance of `liftFCB`: `π • liftFCB F hFCB = liftFCB (π • F) (FCB_smul π hFCB)`. -/
theorem liftFCB_smul (π : FinitePerm α) (F : NFun α (α × X) (Option Y)) (hFCB : FCB F) :
    π • liftFCB F hFCB = liftFCB (π • F) (FCB_smul π hFCB) := by
  have : И a, ∀ x : X, some ((π • liftFCB F hFCB) ⟪a⟫x) = (π • F) (a, x) := by
    apply freshQuantifier_mono _ ((freshQuantifier_smul_iff π).mp (liftFCB_abs F hFCB))
    intro a ha x
    simp only [NFun.smul_apply, abs_equivariant, PermType.prod_smul]
    exact congrArg (π • ·) (ha (π⁻¹ • x))
  exact liftFCB_unique (π • F) (FCB_smul π hFCB) (π • liftFCB F hFCB) this

/-- Characterisation of `liftFCB` values (eq. 4.35): `liftFCB F hFCB z = y` iff
for cofinitely many `a`, there exists `x` with `z = ⟪a⟫x` and `some y = F (a, x)`. -/
theorem liftFCB_eq_iff {F : NFun α (α × X) (Option Y)} {hFCB : FCB F}
    {z : NameAbs α X} {y : Y} : liftFCB F hFCB z = y ↔ (И a, ∃ x : X, z = ⟪a⟫x ∧ some y = F (a, x)) := by
  constructor
  · -- Forward: liftFCB F hFCB z = y → И a, ∃ x, z = ⟪a⟫x ∧ some y = F(a,x)
    intro h
    apply freshQuantifier_mono _ (fresh_atom_cofinite (F, z))
    intro a hafz
    split_fresh hafz with haF haz
    obtain ⟨x, _, hz⟩ := abs_concreteAt_eq_forall a haz
    exact ⟨x, hz, by rw [← h, hz, liftFCB_abs_of_fresh F hFCB haF x]⟩
  · -- Backward: (И a, ∃ x, z = ⟪a⟫x ∧ some y = F(a,x)) → liftFCB F hFCB z = y
    intro h
    -- Pick a # F satisfying the И condition
    obtain ⟨a, haF, ⟨x, hz, hsome⟩⟩ := freshQuantifier_exists
      (freshQuantifier_and.mpr ⟨fresh_atom_cofinite F, h⟩)
    apply Option.some_injective
    calc some (liftFCB F hFCB z) = some (liftFCB F hFCB (abs a x)) := by rw [hz]
      _ = F (a, x) := by rw [liftFCB_abs_of_fresh F hFCB haF x]
      _ = some y := hsome.symm

/-- FCB implies the freshness condition: for cofinitely many `a`, `a # F(a, x)` for all `x`.
This is weaker than FCB (which additionally asserts `F(a,x)` is `some`), but is the
operationally useful consequence. -/
theorem FCB_fresh {F : NFun α (α × X) (Option Y)} (hFCB : FCB F) : И a, ∀ x : X, a # F (a, x) :=
  freshQuantifier_mono (fun a ha x ↦ by obtain ⟨y, hy, hay⟩ := ha x; rw [hy]; exact fresh_some.mpr hay) hFCB

/-- Congruence for the FCB predicate: `F = G → (FCB F ↔ FCB G)`. -/
theorem FCB_congr' {F G : NFun α (α × X) (Option Y)} (h : F = G) : FCB F ↔ FCB G := by
  subst h; rfl

/-- Unwrapped computation rule for `liftFCB`: if `a # F` and `F (a, x) = some y`, then
`liftFCB F hFCB (⟪a⟫ x) = y`. This is `liftFCB_abs_of_fresh` with the `some` stripped. -/
theorem liftFCB_abs_of_fresh_eq {F : NFun α (α × X) (Option Y)} {hFCB : FCB F} {a : α} (haF : a # F) {x : X} {y : Y} (hFax : F (a, x) = some y) :
    liftFCB F hFCB ⟪a⟫x = y := by
  apply Option.some_injective
  rw [liftFCB_abs_of_fresh F hFCB haF x, hFax]

/-- Computation rule for `liftFCB` via concretion: if `a # F` and `z ⊙ a = some x`,
then `some (liftFCB F hFCB z) = F (a, x)`. Combines `abs_of_concreteAt_eq_some` and `liftFCB_abs_of_fresh`. -/
theorem liftFCB_concreteAt {F : NFun α (α × X) (Option Y)} {hFCB : FCB F} {z : NameAbs α X} {a : α} (haF : a # F) {x : X} (hconc : z ⊙ a = some x) :
    some (liftFCB F hFCB z) = F (a, x) := by
  rw [abs_of_concreteAt_eq_some hconc, liftFCB_abs_of_fresh F hFCB haF x]

/-- Cofinite computation rule for `liftFCB` with unwrapped `some`: for cofinitely many `a`
and all `x`, if `F(a,x) = some y` then `liftFCB F hFCB ⟪a⟫x = y`. -/
theorem liftFCB_abs_unwrap {F : NFun α (α × X) (Option Y)} (hFCB : FCB F) :
    И a, ∀ x : X, ∀ y : Y, F (a, x) = some y → liftFCB F hFCB ⟪a⟫x = y :=
  freshQuantifier_mono (fun _ haF _ _ hFax ↦ liftFCB_abs_of_fresh_eq haF hFax) (fresh_atom_cofinite F)

/-- Injectivity of `liftFCB` in `F`: if `liftFCB F hF = liftFCB G hG`, then `F` and `G`
agree cofinitely on representatives. Converse direction of uniqueness. -/
theorem liftFCB_inj {F G : NFun α (α × X) (Option Y)} {hF : FCB F} {hG : FCB G} (h : liftFCB F hF = liftFCB G hG) :
    И a, ∀ x : X, F (a, x) = G (a, x) := by
  have hFA := liftFCB_abs F hF
  have hGA := liftFCB_abs G hG
  apply freshQuantifier_mono _ (freshQuantifier_and.mpr ⟨hFA, hGA⟩)
  intro a ⟨hFa, hGa⟩ x
  calc F (a, x)
      = some (liftFCB F hF ⟪a⟫x) := (hFa x).symm
    _ = some (liftFCB G hG ⟪a⟫x) := by rw [h]
    _ = G (a, x) := hGa x

/-- The underlying function of `liftFCB F hFCB` is equivariant when `supp F = ∅`. -/
theorem liftFCB_isEquivariant_of_supp_empty {F : NFun α (α × X) (Option Y)} {hFCB : FCB F}
    (hF : supp F = ∅) : IsEquivariant α (liftFCB F hFCB : NameAbs α X → Y) := by
  have hsupp : supp (liftFCB F hFCB) = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro a ha
    exact Finset.notMem_empty a (hF ▸ supp_liftFCB_le F hFCB ha)
  exact NFun.supp_eq_empty_iff_isEquivariant.mp hsupp

/-- Naturality of `liftFCB`: post-composing `F` with an equivariant `g : Y → Z` commutes with the lift. -/
theorem liftFCB_map {Z : Type u} [Nominal α Z] {F : NFun α (α × X) (Option Y)} {hFCB : FCB F}
    (g : Y → Z) (hg : IsEquivariant α g) (hFCB' : FCB (F.map (Option.map g) (isEquivariant_option_map hg))) :
    ∀ z, liftFCB (F.map (Option.map g) (isEquivariant_option_map hg)) hFCB' z = g (liftFCB F hFCB z) := by
  intro z
  -- Pick a # F with z = ⟪a⟫x
  obtain ⟨a, x, haF, hz⟩ := exists_fresh_rep z F
  have haF' : a # F.map (Option.map g) (isEquivariant_option_map hg) :=
    fresh_of_supp_subset (NFun.supp_map_le _ _ _) haF
  rw [hz]
  apply Option.some_injective
  calc some (liftFCB (F.map (Option.map g) (isEquivariant_option_map hg)) hFCB' ⟪a⟫x)
      = (F.map (Option.map g) (isEquivariant_option_map hg)) (a, x) := liftFCB_abs_of_fresh _ hFCB' haF' x
    _ = Option.map g (F (a, x)) := NFun.map_apply _ _ _ _
    _ = Option.map g (some (liftFCB F hFCB ⟪a⟫x)) := by rw [liftFCB_abs_of_fresh F hFCB haF x]
    _ = some (g (liftFCB F hFCB ⟪a⟫x)) := rfl

end FCB

/-! ### Corollary 4.17 (Pitts, Section 4.5) -/

section LiftFresh

/- **Corollary 4.17 (Pitts, Section 4.5)**

A simpler form of Theorem 4.15 for **equivariant** functions with a parameter. Given
`X, Y, Z ∈ Nom` and an equivariant function `f : α → X → Y` such that
`∀ a x, a # f a x`, there is a unique equivariant function `f̄ : [A]X → Y` satisfying
`(Иa)(∀x) f̄(⟪a⟫x) = f a x`.

This is the main elimination principle for defining functions out of `NameAbs`. -/

variable {Y : Type u} [Nominal α Y]

/-- Auxiliary: wrap an equivariant `f : α → X → Y` into an `NFun α (α × X) (Option Y)` via
`(a, x) ↦ some (f a x)`. Equivariance of `f` gives empty support. -/
private noncomputable def liftFresh_nfun (f : α → X → Y) (hEquiv : IsEquivariant₂ α f) : NFun α (α × X) (Option Y) :=
  NFun.ofSupports ⟨fun p ↦ some (f p.1 p.2)⟩ ∅
    (by
      rw [supports_pfun_iff]
      intro π _ ⟨a, x⟩
      simp only [PermType.prod_smul]
      exact congrArg some (hEquiv.map_smul π a x))

@[simp] private theorem liftFresh_nfun_apply (f : α → X → Y) (hEquiv : IsEquivariant₂ α f) (a : α) (x : X) :
    liftFresh_nfun f hEquiv (a, x) = some (f a x) :=
  NFun.ofSupports_apply _ _ _ _

private theorem liftFresh_nfun_fcb (f : α → X → Y) (hEquiv : IsEquivariant₂ α f) (hFresh : ∀ (a : α) (x : X), a # f a x) :
    FCB (liftFresh_nfun f hEquiv) :=
  freshQuantifier_of_forall (fun a ↦ fun x ↦ ⟨f a x, by simp, hFresh a x⟩)

theorem liftFresh_nfun_supp (f : α → X → Y) (hEquiv : IsEquivariant₂ α f) : supp (liftFresh_nfun f hEquiv) = ∅ := by
  rw [NFun.supp_eq_empty_iff']
  intro π ⟨a, x⟩
  change liftFresh_nfun f hEquiv (π • a, π • x) = π • liftFresh_nfun f hEquiv (a, x)
  simp only [liftFresh_nfun_apply, option_smul_some]
  exact congrArg some (hEquiv.map_smul π a x)

private theorem liftFresh_nfun_fresh (f : α → X → Y) (hEquiv : IsEquivariant₂ α f) (a : α) : a # liftFresh_nfun f hEquiv := by
  rw [fresh_atom_left, liftFresh_nfun_supp]; exact Finset.notMem_empty a

/-- **Corollary 4.17**: Given an equivariant binary function `f : α → X → Y` satisfying
the freshness condition `∀ a x, a # f a x`, produce the unique equivariant function `[A]X → Y` satisfying `f̄(⟪a⟫ x) = f a x`. -/
noncomputable def liftFresh (f : α → X → Y)
    (hEquiv : IsEquivariant₂ α f) (hFresh : ∀ (a : α) (x : X), a # f a x) : NameAbs α X → Y :=
  liftFCB (liftFresh_nfun f hEquiv) (liftFresh_nfun_fcb f hEquiv hFresh)

/-- **Computation rule for `liftFresh`**: `liftFresh f hEquiv hFresh (⟪a⟫ x) = f a x`.
Unlike `liftFCB_abs_of_fresh`, no freshness hypothesis is needed (the underlying
`NFun` has empty support), and the equality lives at `Y` level directly. -/
@[simp]
theorem liftFresh_abs (f : α → X → Y) (hEquiv : IsEquivariant₂ α f) (hFresh : ∀ (a : α) (x : X), a # f a x)
    (a : α) (x : X) : liftFresh f hEquiv hFresh ⟪a⟫x = f a x := by
  have h := liftFCB_abs_of_fresh (liftFresh_nfun f hEquiv) (liftFresh_nfun_fcb f hEquiv hFresh)
    (liftFresh_nfun_fresh f hEquiv a) x
  simp only [liftFresh_nfun_apply] at h
  exact Option.some_injective _ h

@[simp]
theorem liftFresh_equivariant (f : α → X → Y) (hEquiv : IsEquivariant₂ α f) (hFresh :
    ∀ (a : α) (x : X), a # f a x) : IsEquivariant α (liftFresh f hEquiv hFresh) where
  map_smul := by
    intro π z
    let F := liftFresh_nfun f hEquiv
    let hFCB := liftFresh_nfun_fcb f hEquiv hFresh
    change (liftFCB F hFCB) (π • z) = π • (liftFCB F hFCB) z
    have hsupp : supp (liftFCB F hFCB) = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro a ha
      have := supp_liftFCB_le F hFCB ha
      rw [liftFresh_nfun_supp] at this
      exact Finset.notMem_empty a this
    exact (NFun.supp_eq_empty_iff'.mp hsupp) π z

/-- Uniqueness of `liftFresh`: any function that agrees on representatives must equal `liftFresh f`. -/
theorem liftFresh_unique (f : α → X → Y) (hEquiv : IsEquivariant₂ α f) (hFresh : ∀ (a : α) (x : X), a # f a x)
    (g : NameAbs α X → Y) (hg : ∀ (a : α) (x : X), g ⟪a⟫x = f a x) : g = liftFresh f hEquiv hFresh := by
  funext z
  induction z using NameAbs.ind with | h a x => rw [hg a x, liftFresh_abs]

/-- Extensionality for `liftFresh`: two lifts are equal iff the underlying functions agree. -/
theorem liftFresh_ext (f g : α → X → Y)
    (hfEquiv : IsEquivariant₂ α f) (hfFresh : ∀ (a : α) (x : X), a # f a x)
    (hgEquiv : IsEquivariant₂ α g) (hgFresh : ∀ (a : α) (x : X), a # g a x) :
    liftFresh f hfEquiv hfFresh = liftFresh g hgEquiv hgFresh ↔ ∀ (a : α) (x : X), f a x = g a x := by
  constructor
  · intro h a x
    have := congr_fun h ⟪a⟫x
    simp only [liftFresh_abs] at this
    exact this
  · intro h
    funext z
    induction z using NameAbs.ind with | h a x => simp [h a x]

/-- Package `liftFresh` as an `NFun` with empty support. -/
noncomputable def liftFresh_NFun (f : α → X → Y) (hEquiv : IsEquivariant₂ α f) (hFresh : ∀ (a : α) (x : X), a # f a x) :
    NFun α (NameAbs α X) Y :=
  NFun.ofSupports ⟨liftFresh f hEquiv hFresh⟩ ∅
    (by
      rw [supports_pfun_iff]
      intro π _ z
      exact (liftFresh_equivariant f hEquiv hFresh).map_smul π z)

@[simp]
theorem liftFresh_NFun_apply (f : α → X → Y) (hEquiv : IsEquivariant₂ α f) (hFresh : ∀ (a : α) (x : X), a # f a x)
    (z : NameAbs α X) : liftFresh_NFun f hEquiv hFresh z = liftFresh f hEquiv hFresh z :=
  NFun.ofSupports_apply _ _ _ _

@[simp]
theorem supp_liftFresh_NFun (f : α → X → Y) (hEquiv : IsEquivariant₂ α f) (hFresh : ∀ (a : α) (x : X), a # f a x) :
    supp (liftFresh_NFun f hEquiv hFresh) = ∅ :=
  Finset.subset_empty.mp (supp_le (NFun.ofSupports_supports _ _ _))

/-- Permuting `liftFresh` has no effect, since `liftFresh` is equivariant.
`π • (liftFresh f hEquiv hFresh z) = liftFresh f hEquiv hFresh (π • z)`. -/
@[simp]
theorem liftFresh_smul (π : FinitePerm α) (f : α → X → Y) (hEquiv : IsEquivariant₂ α f) (hFresh : ∀ (a : α) (x : X), a # f a x)
    (z : NameAbs α X) : π • liftFresh f hEquiv hFresh z = liftFresh f hEquiv hFresh (π • z) :=
  ((liftFresh_equivariant f hEquiv hFresh).map_smul π z).symm

/-- Every atom is fresh for `liftFresh_NFun f hEquiv hFresh`. -/
theorem fresh_liftFresh_NFun (f : α → X → Y) (hEquiv : IsEquivariant₂ α f) (hFresh : ∀ (a : α) (x : X), a # f a x)
    (a : α) : a # (liftFresh_NFun f hEquiv hFresh) := by
  rw [fresh_atom_left, supp_liftFresh_NFun]; exact Finset.notMem_empty a

/-- Congruence form of `liftFresh_ext`: pointwise-equal inputs give the same lift. -/
theorem liftFresh_congr (f g : α → X → Y)
    (hfEquiv : IsEquivariant₂ α f) (hfFresh : ∀ (a : α) (x : X), a # f a x)
    (hgEquiv : IsEquivariant₂ α g) (hgFresh : ∀ (a : α) (x : X), a # g a x)
    (h : ∀ (a : α) (x : X), f a x = g a x) : liftFresh f hfEquiv hfFresh = liftFresh g hgEquiv hgFresh :=
  (liftFresh_ext f g hfEquiv hfFresh hgEquiv hgFresh).mpr h

/-- Uniqueness of `liftFresh` at the `NFun` level: any equivariant `NFun` that agrees on
representatives must be the `liftFresh_NFun` packaging. -/
theorem liftFresh_NFun_unique (f : α → X → Y) (hEquiv : IsEquivariant₂ α f) (hFresh : ∀ (a : α) (x : X), a # f a x)
    (G : NFun α (NameAbs α X) Y) (hG : ∀ (a : α) (x : X), G ⟪a⟫x = f a x) :
    G = liftFresh_NFun f hEquiv hFresh := by
  ext z
  rw [liftFresh_NFun_apply]
  exact congr_fun (liftFresh_unique f hEquiv hFresh G hG) z

/-- Post-composition of an equivariant function with `liftFresh`. -/
theorem liftFresh_comp_equivariant {Z : Type u} [Nominal α Z]
    (f : α → X → Y) (hfEquiv : IsEquivariant₂ α f) (hfFresh : ∀ (a : α) (x : X), a # f a x)
    (g : Y → Z) (hg : IsEquivariant α g) :
    g ∘ liftFresh f hfEquiv hfFresh =
      liftFresh (fun a x => g (f a x))
        (hfEquiv.comp_post hg) (fun a x => fresh_of_equivariant hg (hfFresh a x)) := by
  funext z
  induction z using NameAbs.ind with | h a x =>
    simp only [Function.comp, liftFresh_abs]

/-- The lift of the projection `(a, x) ↦ x` recovers the concretion value:
for any `z : [A]X`, `liftFresh (fun _ x => x) ... z` extracts the body. -/
theorem liftFresh_proj
    (hEquiv : IsEquivariant₂ α (fun (_ : α) (x : X) => x)) (hFresh : ∀ (a : α) (x : X), a # x)
    (a : α) (x : X) : liftFresh (fun _ x => x) hEquiv hFresh ⟪a⟫x = x := by
  simp

end LiftFresh

/-- Congruence for `liftFCB`: if `F = G` then their lifts agree regardless of which FCB proof is used. -/
theorem liftFCB_congr {X Y : Type u} [Nominal α X] [Nominal α Y] {F G : NFun α (α × X) (Option Y)} (hFG : F = G)
    (hF : FCB F) (hG : FCB G) : liftFCB F hF = liftFCB G hG := by
  subst hFG; rfl

/-! ### FCB for total functions -/

section FCBTotal

variable {Y : Type u} [Nominal α Y]

/-- A total finitely supported function `F : (α × X) →ᶠˢ Y` satisfying
`∀ a x, a # F(a,x)` automatically satisfies FCB when composed with `some`. -/
theorem FCB_of_total (F : NFun α (α × X) Y) (hFresh : ∀ (a : α) (x : X), a # F (a, x)) :
    FCB (F.map some isEquivariant_some) :=
  freshQuantifier_of_forall (fun a x ↦ ⟨F (a, x), by simp, hFresh a x⟩)

end FCBTotal

/-! ### Parametric form of Corollary 4.17 (Pitts, equations 4.38–4.39) -/

section LiftFreshParam

variable {Y : Type u} [Nominal α Y] {Z : Type u} [Nominal α Z]
variable (f : Z → α → X → Y)
variable (hEquiv : ∀ (π : FinitePerm α) (z : Z) (a : α) (x : X), f (π • z) (π • a) (π • x) = π • f z a x)

/-- Auxiliary: wrap a 3-argument equivariant function `f : Z → α → X → Y` into an
`NFun α (α × (Z × X)) (Option Y)` via `(a, (z, x)) ↦ some (f z a x)`.
The equivariance assumption ensures empty support. -/
private noncomputable def liftFreshParam_nfun : NFun α (α × (Z × X)) (Option Y) :=
  NFun.ofSupports ⟨fun p ↦ some (f p.2.1 p.1 p.2.2)⟩ ∅
    (by
      rw [supports_pfun_iff]
      intro π _ ⟨a, z, x⟩
      simp only [PermType.prod_smul]
      exact congrArg some (hEquiv π z a x))

@[simp] private theorem liftFreshParam_nfun_apply (a : α) (z : Z) (x : X) :
    liftFreshParam_nfun f hEquiv (a, (z, x)) = some (f z a x) :=
  NFun.ofSupports_apply _ _ _ _

private theorem liftFreshParam_nfun_supp : supp (liftFreshParam_nfun f hEquiv) = ∅ := by
  rw [NFun.supp_eq_empty_iff']
  intro π ⟨a, z, x⟩
  change liftFreshParam_nfun f hEquiv (π • a, (π • z, π • x)) = π • liftFreshParam_nfun f hEquiv (a, (z, x))
  simp only [liftFreshParam_nfun_apply, option_smul_some]
  exact congrArg some (hEquiv π z a x)

private theorem liftFreshParam_nfun_fresh (a : α) : a # liftFreshParam_nfun f hEquiv := by
  rw [fresh_atom_left, liftFreshParam_nfun_supp]; exact Finset.notMem_empty a

/-- Auxiliary: for fixed `z`, the partial function `(a, x) ↦ some (f z a x)` is finitely
supported with support `supp z`. -/
private noncomputable def liftFreshParam_nfun_z (z : Z) : NFun α (α × X) (Option Y) :=
  NFun.ofSupports ⟨fun p ↦ some (f z p.1 p.2)⟩ (supp z)
    (by
      rw [supports_pfun_iff]
      intro π hπ ⟨a, x⟩
      simp only [PermType.prod_smul]
      have hπz : π • z = z := supp_supports z π hπ
      change some (f z (π • a) (π • x)) = π • some (f z a x)
      rw [option_smul_some, ← hEquiv π z a x, hπz])

@[simp] private theorem liftFreshParam_nfun_z_apply (z : Z) (a : α) (x : X) : liftFreshParam_nfun_z f hEquiv z (a, x) = some (f z a x) :=
  NFun.ofSupports_apply _ _ _ _

private theorem liftFreshParam_nfun_z_fcb (hFresh : ∀ (z : Z), И (a : α), ∀ (x : X), a # f z a x)
    (z : Z) : FCB (liftFreshParam_nfun_z f hEquiv z) :=
  freshQuantifier_mono (fun a ha x ↦ ⟨f z a x, by simp, ha x⟩) (hFresh z)

/-- **Corollary 4.17 (parametric form)**: Given nominal sets `Z`, `X`, `Y` and a function
`f : Z → α → X → Y` equivariant in all three arguments and satisfying the cofinite freshness
condition `∀ z, И a, ∀ x, a # f z a x`, there is a unique function `f̄ : Z → [A]X → Y`
satisfying `(И a)(∀ x) f̄ z (⟪a⟫x) = f z a x`, equivariant jointly in `z` and the abstraction.

This is the full three-variable form of Corollary 4.17 (Pitts, equations 4.38–4.39),
adding a parameter `z : Z` to the elimination principle. The parameter-free `liftFresh`
is recovered by taking `Z = Unit`. -/
noncomputable def liftFreshParam (hFresh : ∀ (z : Z), И (a : α), ∀ (x : X), a # f z a x) :
    Z → NameAbs α X → Y :=
  fun z ↦ liftFCB (liftFreshParam_nfun_z f hEquiv z) (liftFreshParam_nfun_z_fcb f hEquiv hFresh z)

/-- **Computation rule for `liftFreshParam`** (cofinite form):
`(И a)(∀ x) liftFreshParam f hEquiv hFresh z (⟪a⟫ x) = f z a x`. -/
theorem liftFreshParam_abs (hFresh : ∀ (z : Z), И (a : α), ∀ (x : X), a # f z a x)
    (z : Z) : И (a : α), ∀ (x : X), liftFreshParam f hEquiv hFresh z ⟪a⟫x = f z a x := by
  let F := liftFreshParam_nfun_z f hEquiv z
  let hFCB := liftFreshParam_nfun_z_fcb f hEquiv hFresh z
  change И a, ∀ x, liftFCB F hFCB ⟪a⟫x = f z a x
  apply freshQuantifier_mono _ (liftFCB_abs F hFCB)
  intro a ha x
  exact Option.some_injective _ (by rw [ha x, liftFreshParam_nfun_z_apply])

/-- **Equivariance of `liftFreshParam`**: the lifted function is equivariant jointly in
the parameter and the abstraction. -/
theorem liftFreshParam_equivariant (hFresh : ∀ (z : Z), И (a : α), ∀ (x : X), a # f z a x) (π : FinitePerm α) (z : Z) (w : NameAbs α X) :
    liftFreshParam f hEquiv hFresh (π • z) (π • w) = π • liftFreshParam f hEquiv hFresh z w := by
  let F_z := liftFreshParam_nfun_z f hEquiv z
  let F_πz := liftFreshParam_nfun_z f hEquiv (π • z)
  let hFCB_z := liftFreshParam_nfun_z_fcb f hEquiv hFresh z
  let hFCB_πz := liftFreshParam_nfun_z_fcb f hEquiv hFresh (π • z)
  have hNFunEq : π • F_z = F_πz := by
    apply NFun.ext; intro ⟨a, x⟩
    simp only [NFun.smul_apply, PermType.prod_smul]
    change π • some (f z (π⁻¹ • a) (π⁻¹ • x)) = some (f (π • z) a x)
    rw [option_smul_some, ← hEquiv π z (π⁻¹ • a) (π⁻¹ • x), PermType.smul_inv_smul,
      PermType.smul_inv_smul]
  change liftFCB F_πz hFCB_πz (π • w) = π • liftFCB F_z hFCB_z w
  have hSmul := liftFCB_smul π F_z hFCB_z
  have hCongr := liftFCB_congr hNFunEq (FCB_smul π hFCB_z) hFCB_πz
  rw [← hCongr, ← hSmul, NFun.smul_apply_smul]

/-- Uniqueness of `liftFreshParam`: any function that agrees on cofinitely many representatives
must equal the parametric lift. -/
theorem liftFreshParam_unique (hFresh : ∀ (z : Z), И (a : α), ∀ (x : X), a # f z a x)
    (g : Z → NameAbs α X → Y) (hg : ∀ z, И a, ∀ x, g z ⟪a⟫x = f z a x) :
    g = liftFreshParam f hEquiv hFresh := by
  funext z w
  -- Pick a fresh for w satisfying both И conditions
  have hBoth : И a, (a # w) ∧ (∀ x, g z ⟪a⟫x = f z a x) ∧
      (∀ x, liftFreshParam f hEquiv hFresh z ⟪a⟫x = f z a x) :=
    freshQuantifier_and.mpr ⟨fresh_atom_cofinite w,
      freshQuantifier_and.mpr ⟨hg z, liftFreshParam_abs f hEquiv hFresh z⟩⟩
  obtain ⟨a, haw, hga, hla⟩ := freshQuantifier_exists hBoth
  obtain ⟨x, _, hw⟩ := abs_concreteAt_eq_forall a haw
  rw [hw, hga x, ← hla x]

end LiftFreshParam

end NameAbs

end NominalSets
