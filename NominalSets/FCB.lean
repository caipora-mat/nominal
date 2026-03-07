import NominalSets.NameAbstraction
import NominalSets.Concretion

/-!
# Freshness Condition for Binders

This file contains Theorem 4.15 (the general freshness condition for binders, FCB) and
Corollary 4.17 (its equivariant specialisation), together with structural isomorphisms
of the name abstraction functor `[A]_` and the adjunction with the separated product.

**Note:** The constructions in this file are works in progress. All definitions and
theorems whose bodies are `sorry` are present as stubs with correct signatures; their
proofs are deferred.

## Main definitions

* `NameAbs.FCB F` — the freshness condition for binders predicate: `И a, ∀ x, a # F (a, x)`
  (equation 4.32). (Implemented.)
* `NameAbs.liftFCB F hFCB` — the unique finitely supported function `[A]X →ᶠˢ Y` extending
  `F` (Theorem 4.15). (sorry-stub.)
* `NameAbs.liftFresh f hEquiv hFresh` — the equivariant elimination principle `[A]X → Y`
  (Corollary 4.17). (sorry-stub.)
* `NameAbs.absAtomEquiv` — the equivalence `[A]A ≃ A ⊕ Unit` (Example 4.18). (sorry-stub.)
* `NameAbs.prodEquiv` — the equivalence `[A](X × Y) ≃ [A]X × [A]Y` (eq. 4.28). (sorry-stub.)
* `NameAbs.sumEquiv` — the equivalence `[A](X ⊕ Y) ≃ [A]X ⊕ [A]Y` (eq. 4.27). (sorry-stub.)
* `NameAbs.discreteEquiv hdisc` — `[A]X ≃ X` when every element of `X` has empty support
  (eq. 4.12). (sorry-stub.)
* `NameAbs.expEquiv` — the equivalence `[A](X →ᶠˢ Y) ≃ [A]X →ᶠˢ [A]Y` (Proposition 4.14).
  (sorry-stub.)
* `NameAbs.SepProd α X` — the separated product `{ (x, a) | x # a }` (left adjoint to `[A]_`).
  (Implemented.)
* `NameAbs.adjCounit` — the counit `SepProd α ([A]X) → X` of the left adjunction
  (Theorem 4.12, eq. 4.20). (sorry-stub.)
* `NameAbs.adjCurry` — the currying map of the left adjunction (eq. 4.22). (sorry-stub.)
* `NameAbs.sepProdAbsEquiv` — `SepProd α ([A]X) ≃ α × X` (Exercise 4.2). (sorry-stub.)
* `NameAbs.RightAdj α X` — the right adjoint `{ f : α →ᶠˢ X | ∀ a, a # f a }` (eq. 4.23).
  (Implemented.)
* `NameAbs.rightAdjCounit` — the counit `[A](R X) → X` of the right adjunction
  (Theorem 4.13, eq. 4.24). (sorry-stub.)
* `NameAbs.rightAdjUnit` — the unit `Y → R([A]Y)` of the right adjunction
  (eq. 4.26). (sorry-stub.)

## Main results

### Freshness condition for binders (Pitts, Theorem 4.15)
* `liftFCB_abs` — `И a, ∀ x, liftFCB F hFCB (⟪a⟫ x) = F (a, x)` (property 4.33). (sorry-stub.)
* `liftFCB_abs_of_fresh` — `a # F → liftFCB F hFCB (⟪a⟫ x) = F (a, x)` (from 4.36). (sorry-stub.)
* `supp_liftFCB_le` — `supp (liftFCB F hFCB) ⊆ supp F`. (sorry-stub.)
* `liftFCB_unique` — uniqueness of `liftFCB`. (sorry-stub.)

### Equivariant specialisation (Pitts, Corollary 4.17)
* `liftFresh_abs` — `liftFresh f _ _ (⟪a⟫ x) = f a x`. (sorry-stub.)
* `liftFresh_equivariant` — `liftFresh f _ _` is equivariant. (sorry-stub.)
* `liftFresh_unique` — uniqueness of `liftFresh`. (sorry-stub.)

### Structural isomorphisms
* `absAtomEquiv_abs_eq` — `absAtomEquiv (abs a a) = Sum.inr ()`. (sorry-stub.)
* `absAtomEquiv_abs_ne` — `a ≠ a' → absAtomEquiv (abs a a') = Sum.inl a'`. (sorry-stub.)
* `absAtomEquiv_equivariant` — equivariance of `absAtomEquiv`. (sorry-stub.)
* `prodEquiv_abs` — `prodEquiv (abs a (x, y)) = (abs a x, abs a y)`. (sorry-stub.)
* `prodEquiv_equivariant` — equivariance of `prodEquiv`. (sorry-stub.)
* `sumEquiv_inl` — `sumEquiv (abs a (Sum.inl x)) = Sum.inl (abs a x)`. (sorry-stub.)
* `sumEquiv_inr` — `sumEquiv (abs a (Sum.inr y)) = Sum.inr (abs a y)`. (sorry-stub.)
* `sumEquiv_equivariant` — equivariance of `sumEquiv`. (sorry-stub.)
* `discreteEquiv_abs` — `discreteEquiv hdisc (abs a x) = x`. (sorry-stub.)
* `discreteEquiv_equivariant` — equivariance of `discreteEquiv`. (sorry-stub.)
* `abs_self_eq` — `abs a a = abs a' a'` (all self-bindings in `[A]A` are equal). (sorry-stub.)
* `abs_abs_ne` — `a ≠ a' → abs a (abs a a) ≠ abs a (abs a' a)`. (sorry-stub.)

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
  have hc₃F : c₃ # F := (fresh_prod_right.mp hc₃fresh).1
  have hc₃z : c₃ # z := (fresh_prod_right.mp hc₃fresh).2
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
      have key := NFun.smul_apply_smul (swap c c₃) F (c₃, y₃)
      simp only [PermType.prod_smul, swap_apply_right, hFixF] at key
      rw [hweq, key]
      apply fresh_swap
      · rw [fresh_atom_left]; intro hcmem
        have := NFun.supp_apply_le F (c₃, y₃) hcmem
        rw [supp_prod, supp_atom, Finset.mem_union, Finset.mem_union, Finset.mem_singleton] at this
        rcases this with hF | hc₃eq | hy₃mem
        · exact (fresh_atom_left c F).mp hcF hF
        · exact heq hc₃eq
        · exact (fresh_atom_left c y₃).mp (fresh_prod_right.mp hfreshc).2 hy₃mem
      · exact hc₃FCB y₃

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
        conv_lhs => rw [← hπz]
        exact (concreteAt_equivariant π z a).symm]
      cases z ⊙ a with
      | none => rfl
      | some x =>
        change F (π • a, π • x) = π • F (a, x)
        have := NFun.smul_apply_smul π F (a, x)
        rw [hπF] at this
        exact this)

/-- **Freshness condition for `liftFCB_nfun`**: the partial function `G = liftFCB_nfun F z`
satisfies the hypothesis of the partial freshness theorem (FC), i.e., `И a, ∃ y, G(a) = some y ∧ a # y`.

**Proof:** For `a # (F, z)`, concretise `z` at `a` via `abs_concreteAt_eq_forall` to get
`z ⊙ a = some x` with `z = ⟪a⟫x`. Then `G(a) = F(a, x)`, and the FCB condition on `F` gives `∃ y, F(a, x) = some y ∧ a # y`.

This is the proof term that, paired with `liftFCB_nfun F z`, feeds into `freshF` to
define `liftFCB_fun`. -/
private theorem liftFCB_nfun_fc (F : NFun α (α × X) (Option Y)) (hFCB : FCB F) (z : NameAbs α X) : FC (liftFCB_nfun F z) := by
  have hBoth : И a, a # (F, z) ∧ (∀ x : X, ∃ y : Y, F (a, x) = some y ∧ a # y) :=
    freshQuantifier_and.mpr ⟨fresh_atom_cofinite (F, z), hFCB⟩
  apply freshQuantifier_mono _ hBoth
  intro a ⟨hafz, hfcb⟩
  have haz : a # z := (fresh_prod_right.mp hafz).2
  obtain ⟨x, hconc, _⟩ := abs_concreteAt_eq_forall a haz
  obtain ⟨y, hFax, hay⟩ := hfcb x
  exact ⟨y, by simp only [liftFCB_nfun, NFun.ofSupports_apply, PFun.coe_mk, hconc]; exact hFax, hay⟩

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
    have hbF : b # F := (fresh_prod_right.mp hbfz).1
    have hbz : b # z := (fresh_prod_right.mp hbfz).2
    obtain ⟨y, hconc, hzb⟩ := abs_concreteAt_eq_forall b hbz
    have heval : (liftFCB_nfun F z) b = F (b, y) := by
      simp only [liftFCB_nfun, NFun.ofSupports_apply, PFun.coe_mk, hconc]; rfl
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
        _ = π • F (a, x) := by have := NFun.smul_apply_smul π F (a, x); rw [hπF] at this; simp only [PermType.prod_smul] at this; exact this
        _ = π • some (liftFCB_fun F hFCB z) := by rw [hrhs]
        _ = some (π • liftFCB_fun F hFCB z) := by simp)

/-- `liftFCB` agrees with `F` on representatives with a fresh binder: if `a # F`, then `liftFCB F hFCB (⟪a⟫ x) = F (a, x)` for all `x`. (From 4.36.) -/
theorem liftFCB_abs_of_fresh (F : NFun α (α × X) (Option Y)) (hFCB : FCB F)
    {a : α} (ha : a # F) (x : X) : liftFCB F hFCB (⟪a⟫x) = F (a, x) := by
  change liftFCB_fun F hFCB (abs a x) = F (a, x); exact liftFCB_fun_eq hFCB ha rfl

/-- `liftFCB` agrees with `F` on representatives: for cofinitely many `a` and all `x`, `liftFCB F hFCB (⟪a⟫ x) = F (a, x)`. (Property 4.33.) -/
theorem liftFCB_abs (F : NFun α (α × X) (Option Y)) (hFCB : FCB F) : И a, ∀ x : X, liftFCB F hFCB (⟪a⟫x) = F (a, x) :=
  freshQuantifier_mono (fun _ ha x ↦ liftFCB_abs_of_fresh F hFCB ha x) (fresh_atom_cofinite F)

/-- Support bound: `supp (liftFCB F hFCB) ⊆ supp F`. -/
theorem supp_liftFCB_le (F : NFun α (α × X) (Option Y)) (hFCB : FCB F) : supp (liftFCB F hFCB) ⊆ supp F :=
  -- liftFCB is defined via NFun.ofSupports with support set `supp F`, so `supports (supp F) (liftFCB F hFCB)` holds by construction.
  supp_le (NFun.ofSupports_supports _ _ _)

/-- Uniqueness of `liftFCB`: any finitely supported function `G : [A]X →ᶠˢ Y` satisfying property (4.33) must equal `liftFCB F hFCB`. -/
theorem liftFCB_unique (F : NFun α (α × X) (Option Y)) (hFCB : FCB F)
    (G : NFun α (NameAbs α X) Y) (hG : И a, ∀ x : X, G (⟪a⟫x) = F (a, x)) : G = liftFCB F hFCB := by
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
    have key_F := NFun.smul_apply_smul (swap b c) F (b, x)
    rw [hswapF] at key_F
    simp only [PermType.prod_smul, swap_apply_left] at key_F
    apply smul_injective (swap b c)
    simp only [option_smul_some]
    rw [← key_G, hGc', key_F]
  apply Option.some_injective
  rw [hGbx, ← liftFCB_abs_of_fresh F hFCB hbF x]

end FCB

/-! ### Corollary 4.17 (Pitts, Section 4.5) -/

section LiftFresh

/- **Corollary 4.17 (Pitts, Section 4.5)**

A simpler form of Theorem 4.15 for **equivariant** functions with a parameter. Given `X, Y, Z ∈ Nom` and an equivariant function `f : α → X → Y` such that
`∀ a x, a # f a x`, there is a unique equivariant function `f̄ : [A]X → Y` satisfying `(Иa)(∀x) f̄(⟪a⟫x) = f a x`.

This is the main elimination principle for defining functions out of `NameAbs`. -/

variable {Y : Type u} [Nominal α Y]

/-- **Corollary 4.17**: Given an equivariant function `f : α → X → Y` satisfying the
freshness condition `∀ a x, a # f a x`, produce the unique function `[A]X → Y`
satisfying `f̄(⟪a⟫ x) = f a x`. -/
def liftFresh (f : α → X → Y)
    (hEquiv : ∀ (π : FinitePerm α) (a : α) (x : X), f (π • a) (π • x) = π • f a x)
    (hFresh : ∀ (a : α) (x : X), a # f a x) :
    NameAbs α X → Y := sorry

@[simp]
theorem liftFresh_abs (f : α → X → Y)
    (hEquiv : ∀ (π : FinitePerm α) (a : α) (x : X), f (π • a) (π • x) = π • f a x)
    (hFresh : ∀ (a : α) (x : X), a # f a x)
    (a : α) (x : X) :
    liftFresh f hEquiv hFresh (abs a x) = f a x := sorry

theorem liftFresh_equivariant (f : α → X → Y)
    (hEquiv : ∀ (π : FinitePerm α) (a : α) (x : X), f (π • a) (π • x) = π • f a x)
    (hFresh : ∀ (a : α) (x : X), a # f a x)
    (π : FinitePerm α) (F : NameAbs α X) :
    liftFresh f hEquiv hFresh (π • F) = π • liftFresh f hEquiv hFresh F := sorry

/-- Uniqueness of `liftFresh`: any function that agrees on representatives must equal
`liftFresh f`. -/
theorem liftFresh_unique (f : α → X → Y)
    (hEquiv : ∀ (π : FinitePerm α) (a : α) (x : X), f (π • a) (π • x) = π • f a x)
    (hFresh : ∀ (a : α) (x : X), a # f a x)
    (g : NameAbs α X → Y)
    (hg : ∀ (a : α) (x : X), g (abs a x) = f a x) :
    g = liftFresh f hEquiv hFresh := sorry

end LiftFresh

/-! ### Structural properties -/

section Structural

variable {Y : Type u} [Nominal α Y]

/-! #### `[A]A ≅ A ⊕ Unit` (Pitts, Example 4.18, eq. 4.40) -/

/-- The name abstraction of atoms: `[A]A ≅ A ⊕ Unit`.
Sends `⟪a⟫ a ↦ inr ()` (self-binding) and `⟪a⟫ a' ↦ inl a'` (when `a ≠ a'`). -/
noncomputable def absAtomEquiv : NameAbs α α ≃ (α ⊕ Unit) where
  toFun := sorry
  invFun := sorry
  left_inv := sorry
  right_inv := sorry

@[simp]
theorem absAtomEquiv_abs_eq (a : α) :
    absAtomEquiv (abs a a) = Sum.inr () := sorry

@[simp]
theorem absAtomEquiv_abs_ne {a a' : α} (h : a ≠ a') :
    absAtomEquiv (abs a a') = Sum.inl a' := sorry

/-- `absAtomEquiv` commutes with the permutation action (equivariance). -/
theorem absAtomEquiv_equivariant (π : FinitePerm α) (F : NameAbs α α) :
    absAtomEquiv (π • F) = Sum.map (π • ·) id (absAtomEquiv F) := sorry

/-! #### Preservation of products (Pitts, eq. 4.28, Exercise 4.4) -/

/-- `[A](X × Y) ≅ [A]X × [A]Y` (eq. 4.28).
Since `[A]_` is a right adjoint, it preserves limits — in particular products. -/
noncomputable def prodEquiv :
    NameAbs α (X × Y) ≃ NameAbs α X × NameAbs α Y where
  toFun := sorry
  invFun := sorry
  left_inv := sorry
  right_inv := sorry

@[simp]
theorem prodEquiv_abs (a : α) (x : X) (y : Y) :
    prodEquiv (abs a (x, y)) = (abs a x, abs a y) := sorry

/-- `prodEquiv` commutes with the permutation action (equivariance). -/
theorem prodEquiv_equivariant (π : FinitePerm α) (F : NameAbs α (X × Y)) :
    prodEquiv (π • F) = π • prodEquiv F := sorry

/-! #### Preservation of coproducts (Pitts, eq. 4.27, Exercise 4.5) -/

/-- `[A](X ⊕ Y) ≅ [A]X ⊕ [A]Y` (eq. 4.27).
Since `[A]_` has a right adjoint (Theorem 4.13), it preserves colimits — in particular
coproducts. -/
noncomputable def sumEquiv :
    NameAbs α (X ⊕ Y) ≃ NameAbs α X ⊕ NameAbs α Y where
  toFun := sorry
  invFun := sorry
  left_inv := sorry
  right_inv := sorry

@[simp]
theorem sumEquiv_inl (a : α) (x : X) :
    sumEquiv (abs a (Sum.inl x) : NameAbs α (X ⊕ Y)) = Sum.inl (abs a x) := sorry

@[simp]
theorem sumEquiv_inr (a : α) (y : Y) :
    sumEquiv (abs a (Sum.inr y) : NameAbs α (X ⊕ Y)) = Sum.inr (abs a y) := sorry

/-- `sumEquiv` commutes with the permutation action (equivariance). -/
theorem sumEquiv_equivariant (π : FinitePerm α) (F : NameAbs α (X ⊕ Y)) :
    sumEquiv (π • F) = π • sumEquiv F := sorry

/-! #### Discrete nominal sets (Pitts, Example 4.6) -/

/-- For discrete `X` (empty support for all elements), `[A]X ≅ X` (eq. 4.12). -/
noncomputable def discreteEquiv (hdisc : ∀ (x : X), supp x = ∅) :
    NameAbs α X ≃ X where
  toFun := sorry
  invFun := sorry
  left_inv := sorry
  right_inv := sorry

@[simp]
theorem discreteEquiv_abs (hdisc : ∀ (x : X), supp x = ∅) (a : α) (x : X) :
    discreteEquiv hdisc (abs a x) = x := sorry

/-- `discreteEquiv` commutes with the permutation action (equivariance). -/
theorem discreteEquiv_equivariant (hdisc : ∀ (x : X), supp x = ∅)
    (π : FinitePerm α) (F : NameAbs α X) :
    discreteEquiv hdisc (π • F) = π • discreteEquiv hdisc F := sorry

/-! #### Nested abstractions (Pitts, Exercise 4.1) -/

/-- All self-bindings in `[A]A` are equal: `⟪a⟫a = ⟪a'⟫a'`. This is the unique element
mapping to `Sum.inr ()` under `absAtomEquiv`. -/
theorem abs_self_eq (a a' : α) : abs a a = abs a' (a' : α) := sorry

/-- `⟪a⟫(⟪a⟫a) ≠ ⟪a⟫(⟪a'⟫a)` when `a ≠ a'` (Exercise 4.1). -/
theorem abs_abs_ne {a a' : α} (h : a ≠ a') :
    abs a (abs a a) ≠ abs a (abs a' a) := sorry

end Structural

/-! ### Preservation of exponentials (Pitts, Proposition 4.14) -/

/-- `[A](X →ᶠˢ Y) ≅ [A]X →ᶠˢ [A]Y` (Proposition 4.14). -/
noncomputable def expEquiv {Y : Type u} [Nominal α Y] :
    NameAbs α (NFun α X Y) ≃ NFun α (NameAbs α X) (NameAbs α Y) where
  toFun := sorry
  invFun := sorry
  left_inv := sorry
  right_inv := sorry

/-! ### Separated product and adjunction (Pitts, Theorem 4.12) -/

section Adjunction

variable {Y : Type u} [Nominal α Y]

/-- The **separated product**: pairs `(x, a)` where `x # a`. This is the left adjoint
to the name abstraction functor `[A]_`. -/
def SepProd (α : Type u) [Name α] (X : Type u) [Nominal α X] :=
  { p : X × α // p.1 # p.2 }

noncomputable instance SepProd.instPermType : PermType α (SepProd α X) := sorry

noncomputable instance SepProd.instNominal : Nominal α (SepProd α X) := sorry

/-- The counit of the adjunction `_ * A ⊣ [A]_` (Theorem 4.12, eq. 4.20):
concretion as a function `SepProd α ([A]X) → X`, sending `(z, a)` with `a # z`
to `z @ a`. -/
noncomputable def adjCounit (p : SepProd α (NameAbs α X)) : X := sorry

/-- `adjCounit` is equivariant. -/
theorem adjCounit_equivariant (π : FinitePerm α) (p : SepProd α (NameAbs α X)) :
    adjCounit (π • p) = π • adjCounit p := sorry

/-- The currying map of the adjunction `_ * A ⊣ [A]_` (Theorem 4.12, eq. 4.22):
given an equivariant `f : SepProd α X → Y`, produce `X → [A]Y` by
`y ↦ fresh a in ⟪a⟫(f(y, a))`. -/
noncomputable def adjCurry (f : SepProd α X → Y)
    (hf : ∀ (π : FinitePerm α) (p : SepProd α X), f (π • p) = π • f p) :
    X → NameAbs α Y := sorry

/-- `adjCurry` is equivariant. -/
theorem adjCurry_equivariant (f : SepProd α X → Y)
    (hf : ∀ (π : FinitePerm α) (p : SepProd α X), f (π • p) = π • f p)
    (π : FinitePerm α) (x : X) :
    adjCurry f hf (π • x) = π • adjCurry f hf x := sorry

/-- Round-trip: `adjCounit ∘ (adjCurry f × id) = f` (Theorem 4.12). -/
theorem adjCounit_adjCurry (f : SepProd α X → Y)
    (hf : ∀ (π : FinitePerm α) (p : SepProd α X), f (π • p) = π • f p)
    (p : SepProd α X) :
    adjCounit ⟨(adjCurry f hf p.val.1, p.val.2), sorry⟩ = f p := sorry

/-! #### Exercise 4.2: `A * [A]X ≅ A × X` -/

/-- `SepProd α ([A]X) ≅ α × X` (Exercise 4.2): the separated product of atoms with
name abstractions is isomorphic to the ordinary product. The forward map sends
`(F, a)` with `a # F` to `(a, F @ a)`, and the backward map sends `(a, x)` to
`(⟪a⟫x, a)`. -/
noncomputable def sepProdAbsEquiv :
    SepProd α (NameAbs α X) ≃ α × X where
  toFun := sorry
  invFun := sorry
  left_inv := sorry
  right_inv := sorry

end Adjunction

/-! ### Right adjoint (Pitts, Theorem 4.13) -/

section RightAdjoint

variable {Y : Type u} [Nominal α Y]

/-- `R X = { f ∈ A →ᶠˢ X | ∀ a, a # f a }` (eq. 4.23). This is the right adjoint
to the name abstraction functor `[A]_`. -/
def RightAdj (α : Type u) [Name α] (X : Type u) [Nominal α X] :=
  { f : NFun α α X // ∀ a, a # f a }

noncomputable instance RightAdj.instPermType : PermType α (RightAdj α X) := sorry

noncomputable instance RightAdj.instNominal : Nominal α (RightAdj α X) := sorry

/-- The counit of the right adjunction `[A]_ ⊣ R` (Theorem 4.13, eq. 4.24):
`ε_X : [A](R X) → X` defined by `z ↦ fresh a in (z @ a) a`. -/
noncomputable def rightAdjCounit (z : NameAbs α (RightAdj α X)) : X := sorry

/-- `rightAdjCounit` is equivariant. -/
theorem rightAdjCounit_equivariant (π : FinitePerm α)
    (z : NameAbs α (RightAdj α X)) :
    rightAdjCounit (π • z) = π • rightAdjCounit z := sorry

/-- The unit of the right adjunction `[A]_ ⊣ R` (Theorem 4.13, eq. 4.26):
`η_Y : Y → R([A]Y)` defined by `y ↦ (a ↦ ⟪a⟫y)`. -/
noncomputable def rightAdjUnit (y : Y) : RightAdj α (NameAbs α Y) := sorry

/-- `rightAdjUnit` is equivariant. -/
theorem rightAdjUnit_equivariant (π : FinitePerm α) (y : Y) :
    rightAdjUnit (π • y) = π • (rightAdjUnit y : RightAdj α (NameAbs α Y)) := sorry

end RightAdjoint

end NameAbs

end NominalSets
