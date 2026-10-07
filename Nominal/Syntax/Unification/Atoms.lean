import Nominal.Syntax.Unification.NominalSet
import Nominal.Syntax.Unification.Mgu

/-!
# The algorithm introduces no new atoms

Every atom occurring in the output of `UnifProblem.solve`, in the substitution or in the freshness
context, already occurs in the problem (`UnifProblem.solve_atoms_subset`).
-/

namespace Nominal

open Core

variable {F X 𝔸 : Type*} [DecidableEq F] [DecidableEq X] [Name 𝔸]

/-! ### Atoms of permuted and substituted terms -/

lemma swapApply_mem (b c a : 𝔸) : swapApply (b, c) a ∈ ({a, b, c} : Finset 𝔸) := by
  simp only [swapApply]
  split_ifs <;> simp

/-- A permutation sends an atom to itself or to one of its own atoms. -/
lemma LPermApply_mem_insert_atoms (π : LPerm 𝔸) (a : 𝔸) :
    LPermApply π a ∈ insert a (LPerm.atoms π) := by
  induction π generalizing a with
  | nil => simp [LPermApply_nil]
  | cons s π ih =>
    obtain ⟨b, c⟩ := s
    rw [LPermApply_cons]
    have h1 := ih (swapApply (b, c) a)
    have h2 := swapApply_mem b c a
    simp only [LPerm.atoms, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton] at h1 h2 ⊢
    rcases h1 with h1 | h1
    · rw [h1]; tauto
    · exact Or.inr (Or.inr h1)

mutual
  lemma ntm.atoms_permute_subset (π : LPerm 𝔸) :
      ∀ t : ntm F X 𝔸, (t.permute π).atoms ⊆ t.atoms ∪ LPerm.atoms π
    | .atm a => by
        intro z hz
        simp only [ntm.permute, ntm.atoms, Finset.mem_singleton] at hz
        subst hz
        have := LPermApply_mem_insert_atoms π a
        simpa [ntm.atoms] using this
    | .mvar σ x => by simp [ntm.permute, ntm.atoms, LPerm.atoms_append]
    | .fapp f ts => by
        simp only [ntm.permute, ntm.atoms]
        exact ntmList.atoms_permute_subset π ts
    | .abs a t => by
        intro z hz
        simp only [ntm.permute, ntm.atoms, Finset.mem_insert] at hz
        rcases hz with rfl | hz
        · have := LPermApply_mem_insert_atoms π a
          simp only [Finset.mem_insert] at this
          simp only [ntm.atoms, Finset.mem_union, Finset.mem_insert]
          tauto
        · have := ntm.atoms_permute_subset π t hz
          simp only [ntm.atoms, Finset.mem_union, Finset.mem_insert] at this ⊢
          tauto

  lemma ntmList.atoms_permute_subset (π : LPerm 𝔸) :
      ∀ ts : List (ntm F X 𝔸),
        ntmList.atoms (ts.map (ntm.permute π)) ⊆ ntmList.atoms ts ∪ LPerm.atoms π
    | [] => by simp [ntmList.atoms]
    | t :: ts => by
        intro z hz
        simp only [List.map_cons, ntmList.atoms, Finset.mem_union] at hz
        rcases hz with hz | hz
        · have := ntm.atoms_permute_subset π t hz
          simp only [ntmList.atoms, Finset.mem_union] at this ⊢
          tauto
        · have := ntmList.atoms_permute_subset π ts hz
          simp only [ntmList.atoms, Finset.mem_union] at this ⊢
          tauto
end

lemma ntmList.atoms_subset_of_mem {t : ntm F X 𝔸} {ts : List (ntm F X 𝔸)} (h : t ∈ ts) :
    t.atoms ⊆ ntmList.atoms ts := by
  induction ts with
  | nil => cases h
  | cons t' ts' ih =>
    simp only [ntmList.atoms]
    rcases List.mem_cons.mp h with rfl | h
    · exact Finset.subset_union_left
    · exact (ih h).trans Finset.subset_union_right

/-- Every atom of a term bound by `σ` lies in `V`. -/
def Subst.AtomsIn (σ : Subst F X 𝔸) (V : Finset 𝔸) : Prop :=
  ∀ p ∈ σ, p.2.atoms ⊆ V

/-- Every atom of a constraint of `Pr` lies in `V`. -/
def UnifProblem.AtomsIn (Pr : UnifProblem F X 𝔸) (V : Finset 𝔸) : Prop :=
  ∀ c ∈ Pr, c.atoms ⊆ V

lemma Subst.atoms_subset_iff (σ : Subst F X 𝔸) (V : Finset 𝔸) :
    σ.atoms ⊆ V ↔ σ.AtomsIn V := by
  induction σ with
  | nil => simp [Subst.atoms, Subst.AtomsIn]
  | cons p σ ih =>
    simp only [Subst.atoms, List.foldr_cons, Finset.union_subset_iff, Subst.AtomsIn,
      List.mem_cons, forall_eq_or_imp] at ih ⊢
    rw [ih]

lemma UnifProblem.atoms_subset_iff (Pr : UnifProblem F X 𝔸) (V : Finset 𝔸) :
    Pr.atoms ⊆ V ↔ Pr.AtomsIn V := by
  induction Pr with
  | nil => simp [UnifProblem.atoms, UnifProblem.AtomsIn]
  | cons c Pr ih =>
    simp only [UnifProblem.atoms, List.foldr_cons, Finset.union_subset_iff, UnifProblem.AtomsIn,
      List.mem_cons, forall_eq_or_imp] at ih ⊢
    rw [ih]

mutual
  lemma ntm.atoms_subst_subset {σ : Subst F X 𝔸} {V : Finset 𝔸} (hσ : σ.AtomsIn V) :
      ∀ t : ntm F X 𝔸, t.atoms ⊆ V → (t.subst σ).atoms ⊆ V
    | .atm a, h => by simpa using h
    | .mvar π x, h => by
        rw [ntm.subst_mvar]
        refine (ntm.atoms_permute_subset π _).trans (Finset.union_subset ?_ ?_)
        · rw [ntm.subst_mvar_nil]
          cases hl : σ.lookup x with
          | none => simp [ntm.atoms, LPerm.atoms]
          | some s => exact hσ _ (Subst.lookup_mem hl)
        · simpa [ntm.atoms] using h
    | .fapp f ts, h => by
        simp only [ntm.subst_fapp, ntm.atoms] at h ⊢
        exact ntmList.atoms_subst_subset hσ ts h
    | .abs a t, h => by
        simp only [ntm.subst_abs, ntm.atoms, Finset.insert_subset_iff] at h ⊢
        exact ⟨h.1, ntm.atoms_subst_subset hσ t h.2⟩

  lemma ntmList.atoms_subst_subset {σ : Subst F X 𝔸} {V : Finset 𝔸} (hσ : σ.AtomsIn V) :
      ∀ ts : List (ntm F X 𝔸), ntmList.atoms ts ⊆ V →
        ntmList.atoms (ts.map (·.subst σ)) ⊆ V
    | [], _ => by simp [ntmList.atoms]
    | t :: ts, h => by
        simp only [List.map_cons, ntmList.atoms] at h ⊢
        exact Finset.union_subset
          (ntm.atoms_subst_subset hσ t (Finset.union_subset_left h))
          (ntmList.atoms_subst_subset hσ ts (Finset.union_subset_right h))
end

lemma Subst.AtomsIn.comp_singleton {σ : Subst F X 𝔸} {V : Finset 𝔸} (hσ : σ.AtomsIn V)
    (x : X) {u : ntm F X 𝔸} (hu : u.atoms ⊆ V) : (σ.comp [(x, u)]).AtomsIn V := by
  have hτ : Subst.AtomsIn [(x, u)] V := by
    intro p hp
    simp only [List.mem_singleton] at hp
    subst hp
    exact hu
  intro p hp
  simp only [Subst.comp, List.mem_append, List.mem_map] at hp
  rcases hp with ⟨q, hq, rfl⟩ | hp
  · exact ntm.atoms_subst_subset hτ q.2 (hσ q hq)
  · exact hτ p hp

lemma UnifProblem.AtomsIn.applySubst {Pr : UnifProblem F X 𝔸} {σ : Subst F X 𝔸}
    {V : Finset 𝔸} (hPr : Pr.AtomsIn V) (hσ : σ.AtomsIn V) : (Pr.applySubst σ).AtomsIn V := by
  intro c hc
  simp only [UnifProblem.applySubst, List.mem_map] at hc
  obtain ⟨c₀, hc₀, rfl⟩ := hc
  have h := hPr c₀ hc₀
  cases c₀ with
  | fresh a t =>
    simp only [UnifConstraint.applySubst, UnifConstraint.atoms, Finset.insert_subset_iff] at h ⊢
    exact ⟨h.1, ntm.atoms_subst_subset hσ t h.2⟩
  | unif s t =>
    simp only [UnifConstraint.applySubst, UnifConstraint.atoms, Finset.union_subset_iff] at h ⊢
    exact ⟨ntm.atoms_subst_subset hσ s h.1, ntm.atoms_subst_subset hσ t h.2⟩

/-! ### Freshness decomposition -/

mutual
  lemma simplifyFresh_atoms_subset (a : 𝔸) :
      ∀ (t : ntm F X 𝔸) (cs : Problem F X 𝔸),
        simplifyFresh a t = some cs →
        ∀ c ∈ cs, c.toUnif.atoms ⊆ insert a t.atoms
    | .atm b, cs, h, c, hc => by
      simp only [simplifyFresh] at h
      by_cases hab : a = b
      · rw [if_pos hab] at h; cases h
      · rw [if_neg hab] at h
        injection h with heq; subst heq
        nomatch hc
    | .mvar π y, cs, h, c, hc => by
      simp only [simplifyFresh] at h
      injection h with heq; subst heq
      rw [List.mem_singleton] at hc
      subst hc
      intro z hz
      simp only [Constraint.toUnif, UnifConstraint.atoms, ntm.atoms, LPerm.atoms,
        Finset.mem_insert, Finset.notMem_empty, or_false] at hz
      subst hz
      have := LPermApply_mem_insert_atoms π.reverse a
      rwa [LPerm.atoms_reverse] at this
    | .fapp _ ts, cs, h, c, hc => by
      simp only [simplifyFresh] at h
      exact simplifyFreshList_atoms_subset a ts cs h c hc
    | .abs b t', cs, h, c, hc => by
      simp only [simplifyFresh] at h
      by_cases hab : a = b
      · rw [if_pos hab] at h
        injection h with heq; subst heq
        nomatch hc
      · rw [if_neg hab] at h
        refine (simplifyFresh_atoms_subset a t' cs h c hc).trans ?_
        intro z hz
        simp only [ntm.atoms, Finset.mem_insert] at hz ⊢
        tauto

  lemma simplifyFreshList_atoms_subset (a : 𝔸) :
      ∀ (ts : List (ntm F X 𝔸)) (cs : Problem F X 𝔸),
        simplifyFreshList a ts = some cs →
        ∀ c ∈ cs, c.toUnif.atoms ⊆ insert a (ntmList.atoms ts)
    | [], cs, h, c, hc => by
      simp only [simplifyFreshList] at h
      injection h with heq; subst heq; nomatch hc
    | t :: ts', cs, h, c, hc => by
      simp only [simplifyFreshList] at h
      cases hf : simplifyFresh a t with
      | none => rw [hf] at h; cases h
      | some cs₁ =>
        cases hg : simplifyFreshList a ts' with
        | none => rw [hf, hg] at h; cases h
        | some cs₂ =>
          rw [hf, hg] at h
          injection h with heq; subst heq
          intro z hz
          rcases List.mem_append.mp hc with hc | hc
          · have := simplifyFresh_atoms_subset a t cs₁ hf c hc hz
            simp only [ntmList.atoms, Finset.mem_insert, Finset.mem_union] at this ⊢
            tauto
          · have := simplifyFreshList_atoms_subset a ts' cs₂ hg c hc hz
            simp only [ntmList.atoms, Finset.mem_insert, Finset.mem_union] at this ⊢
            tauto
end

/-! ### The algorithm -/

/-- One step keeps the atoms of the problem and of the substitution in `V`. -/
lemma unifStep_next_atoms {c : UnifConstraint F X 𝔸} {rest Pr' : UnifProblem F X 𝔸}
    {σ σ' : Subst F X 𝔸} {V : Finset 𝔸}
    (h : unifStep c rest σ = .next Pr' σ')
    (hV : UnifProblem.AtomsIn (c :: rest) V) (hσ : σ.AtomsIn V) :
    Pr'.AtomsIn V ∧ σ'.AtomsIn V := by
  have hc : c.atoms ⊆ V := hV c List.mem_cons_self
  have hrest : rest.AtomsIn V := fun c' hc' => hV c' (List.mem_cons_of_mem _ hc')
  cases UnifRule.of_unifStep h with
  | fresh a t cs ht hcs =>
    refine ⟨fun c' hc' => ?_, hσ⟩
    rcases List.mem_append.mp hc' with hc' | hc'
    · exact hrest c' hc'
    · obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.mp hc'
      exact (simplifyFresh_atoms_subset a t cs hcs c₀ hc₀).trans hc
  | atm a => exact ⟨hrest, hσ⟩
  | mvarSame π π' x =>
    refine ⟨fun c' hc' => ?_, hσ⟩
    rcases List.mem_append.mp hc' with hc' | hc'
    · exact hrest c' hc'
    · obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hc'
      have hn' := (mem_dsList_iff_mem_ds n π π').mp hn
      simp only [ds, Finset.mem_filter, Finset.mem_union] at hn'
      intro z hz
      simp only [UnifConstraint.atoms, ntm.atoms, LPerm.atoms, Finset.mem_insert,
        Finset.notMem_empty, or_false] at hz
      subst hz
      exact hc (by simpa [UnifConstraint.atoms, ntm.atoms] using hn'.1)
  | instL π x u hocc =>
    have hu : (u.permute π.reverse).atoms ⊆ V := by
      refine (ntm.atoms_permute_subset π.reverse u).trans ?_
      rw [LPerm.atoms_reverse]
      intro z hz
      exact hc (by simpa [UnifConstraint.atoms, ntm.atoms, or_comm] using hz)
    have hτ : Subst.AtomsIn [(x, u.permute π.reverse)] V := by
      intro p hp
      simp only [List.mem_singleton] at hp
      subst hp
      exact hu
    exact ⟨hrest.applySubst hτ, hσ.comp_singleton x hu⟩
  | instR π x u hocc =>
    have hu : (u.permute π.reverse).atoms ⊆ V := by
      refine (ntm.atoms_permute_subset π.reverse u).trans ?_
      rw [LPerm.atoms_reverse]
      intro z hz
      exact hc (by simpa [UnifConstraint.atoms, ntm.atoms] using hz)
    have hτ : Subst.AtomsIn [(x, u.permute π.reverse)] V := by
      intro p hp
      simp only [List.mem_singleton] at hp
      subst hp
      exact hu
    exact ⟨hrest.applySubst hτ, hσ.comp_singleton x hu⟩
  | fapp f ss ts hlen =>
    refine ⟨fun c' hc' => ?_, hσ⟩
    rcases List.mem_append.mp hc' with hc' | hc'
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc'
      obtain ⟨hp1, hp2⟩ := List.of_mem_zip hp
      simp only [UnifConstraint.atoms, ntm.atoms, Finset.union_subset_iff] at hc ⊢
      exact ⟨(ntmList.atoms_subset_of_mem hp1).trans hc.1,
        (ntmList.atoms_subset_of_mem hp2).trans hc.2⟩
    · exact hrest c' hc'
  | absSame a s t =>
    refine ⟨fun c' hc' => ?_, hσ⟩
    rcases List.mem_cons.mp hc' with rfl | hc'
    · intro z hz
      apply hc
      simp only [UnifConstraint.atoms, ntm.atoms, Finset.mem_union, Finset.mem_insert] at hz ⊢
      tauto
    · exact hrest c' hc'
  | absDiff a b s t hab =>
    refine ⟨fun c' hc' => ?_, hσ⟩
    rcases List.mem_cons.mp hc' with rfl | hc'
    · intro z hz
      apply hc
      simp only [UnifConstraint.atoms, Finset.mem_union] at hz
      simp only [UnifConstraint.atoms, ntm.atoms, Finset.mem_union, Finset.mem_insert]
      rcases hz with hz | hz
      · have := ntm.atoms_permute_subset [(b, a)] s hz
        simp only [LPerm.atoms, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
          Finset.notMem_empty, or_false] at this
        tauto
      · tauto
    · rcases List.mem_cons.mp hc' with rfl | hc'
      · intro z hz
        apply hc
        simp only [UnifConstraint.atoms, ntm.atoms, Finset.mem_union, Finset.mem_insert] at hz ⊢
        tauto
      · exact hrest c' hc'

/-- The first stage keeps the atoms of the substitution and of the deferred obligations in
    `V`. -/
lemma unify_atoms {V : Finset 𝔸} :
    ∀ (Pr : UnifProblem F X 𝔸) (σ : Subst F X 𝔸) (ds : List (𝔸 × X))
      (ds' : List (𝔸 × X)) (σ' : Subst F X 𝔸),
      unify Pr σ ds = some (ds', σ') →
      Pr.AtomsIn V → σ.AtomsIn V → (∀ p ∈ ds, p.1 ∈ V) →
      σ'.AtomsIn V ∧ ∀ p ∈ ds', p.1 ∈ V := by
  intro Pr σ ds
  induction Pr, σ, ds using unify.induct with
  | case1 σ ds =>
    intro ds' σ' h _ hσ hds
    simp only [unify, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hσ, hds⟩
  | case2 σ ds c rest hfail =>
    intro ds' σ' h _ _ _
    rw [unify, hfail] at h
    cases h
  | case3 σ ds c rest a x hctx ih =>
    intro ds' σ' h hV hσ hds
    rw [unify, hctx] at h
    obtain ⟨b, π, rfl, rfl⟩ := unifStep_ctx_inv c rest σ a x hctx
    have ha : LPermApply π.reverse b ∈ V := by
      have h1 := LPermApply_mem_insert_atoms π.reverse b
      rw [LPerm.atoms_reverse] at h1
      exact hV _ List.mem_cons_self (by simpa [UnifConstraint.atoms, ntm.atoms] using h1)
    refine ih ds' σ' h (fun c' hc' => hV c' (List.mem_cons_of_mem _ hc')) hσ (fun p hp => ?_)
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ha
    · exact hds p hp
  | case4 σ ds c rest Pr' σ_next hnext ih =>
    intro ds' σ' h hV hσ hds
    rw [unify, hnext] at h
    obtain ⟨hV', hσ'⟩ := unifStep_next_atoms hnext hV hσ
    exact ih ds' σ' h hV' hσ' hds

/-- Collecting primitive obligations with atoms in `V` keeps the context in `V`. -/
lemma foldl_ctxStep_atoms {V : Finset 𝔸} (cs : Problem F X 𝔸) :
    ∀ Γ₀ : Context 𝔸 X, (∀ p ∈ Γ₀, p.1 ∈ V) →
      (∀ c ∈ cs, c.toUnif.atoms ⊆ V) →
      ∀ p ∈ cs.foldl ctxStep Γ₀, p.1 ∈ V := by
  induction cs with
  | nil => intro Γ₀ hΓ₀ _ p hp; exact hΓ₀ p hp
  | cons c cs ih =>
    intro Γ₀ hΓ₀ hcs p hp
    rw [List.foldl_cons] at hp
    refine ih _ ?_ (fun c' hc' => hcs c' (List.mem_cons_of_mem _ hc')) p hp
    have hc := hcs c List.mem_cons_self
    cases c with
    | fresh a' t =>
      cases t with
      | mvar π x' =>
        cases π with
        | nil =>
          intro q hq
          rcases Finset.mem_insert.mp hq with rfl | hq
          · exact hc (by simp [Constraint.toUnif, UnifConstraint.atoms])
          · exact hΓ₀ q hq
        | cons _ _ => exact hΓ₀
      | atm _ => exact hΓ₀
      | fapp _ _ => exact hΓ₀
      | abs _ _ => exact hΓ₀
    | alpha _ _ => exact hΓ₀

/-- The second stage keeps the atoms of the context in `V`. -/
lemma finalizeDeferred_atoms {V : Finset 𝔸} {σ : Subst F X 𝔸} (hσ : σ.AtomsIn V) :
    ∀ (ds : List (𝔸 × X)) (Γ₀ Γ : Context 𝔸 X),
      finalizeDeferred ds σ Γ₀ = some Γ →
      (∀ p ∈ ds, p.1 ∈ V) → (∀ p ∈ Γ₀, p.1 ∈ V) → ∀ p ∈ Γ, p.1 ∈ V
  | [], Γ₀, Γ, h, _, hΓ₀ => by
    simp only [finalizeDeferred, Option.some.injEq] at h
    subst h
    exact hΓ₀
  | (a, x) :: tl, Γ₀, Γ, h, hds, hΓ₀ => by
    simp only [finalizeDeferred] at h
    cases hcs : simplifyFresh a ((ntm.mvar (F := F) [] x).subst σ) with
    | none => rw [hcs] at h; cases h
    | some cs =>
      rw [hcs] at h
      have ha : a ∈ V := hds (a, x) List.mem_cons_self
      have ht : ((ntm.mvar (F := F) [] x).subst σ).atoms ⊆ V :=
        ntm.atoms_subst_subset hσ _ (by simp [ntm.atoms, LPerm.atoms])
      exact finalizeDeferred_atoms hσ tl (cs.foldl ctxStep Γ₀) Γ h
        (fun p hp => hds p (List.mem_cons_of_mem _ hp))
        (foldl_ctxStep_atoms cs Γ₀ hΓ₀ (fun c hc =>
          (simplifyFresh_atoms_subset a _ cs hcs c hc).trans
            (Finset.insert_subset ha ht)))

/-- **The algorithm introduces no new atoms**: those of the computed substitution and of the
    computed freshness context all occur in the problem. -/
theorem UnifProblem.solve_atoms_subset (Pr : UnifProblem F X 𝔸) (Γ : Context 𝔸 X)
    (σ : Subst F X 𝔸) (h : Pr.solve = some (Γ, σ)) :
    σ.atoms ⊆ Pr.atoms ∧ Γ.atoms ⊆ Pr.atoms := by
  simp only [UnifProblem.solve] at h
  cases hu : unify Pr [] [] with
  | none => rw [hu] at h; cases h
  | some result =>
    rw [hu] at h
    obtain ⟨ds, σ_u⟩ := result
    simp only at h
    cases hf : finalizeDeferred ds σ_u ∅ with
    | none => rw [hf] at h; cases h
    | some Γ_fin =>
      rw [hf] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨hσ, hds⟩ := unify_atoms Pr [] [] ds σ_u hu
        ((UnifProblem.atoms_subset_iff Pr _).mp (Finset.Subset.refl _))
        (by intro p hp; cases hp) (by intro p hp; cases hp)
      refine ⟨(Subst.atoms_subset_iff _ _).mpr hσ, ?_⟩
      intro a ha
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
      exact finalizeDeferred_atoms hσ ds ∅ Γ_fin hf hds (by intro p hp; simp at hp) p hp

end Nominal
