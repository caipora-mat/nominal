import Nominal.Syntax.Unification.Completeness
import Nominal.Syntax.Unification.SimSubst

namespace Nominal

open Core

variable {F X 𝔸 : Type*} [DecidableEq F] [DecidableEq X] [Name 𝔸]

/-- A member of a list on which `occursIn z` is false itself has `occursIn z` false. -/
lemma ntmList.not_occursIn_of_mem {z : X} {t : ntm F X 𝔸} {ts : List (ntm F X 𝔸)}
    (ht : t ∈ ts) (h : ntmList.occursIn z ts = false) : t.occursIn z = false := by
  induction ts with
  | nil => simp at ht
  | cons a as ih =>
      simp only [ntmList.occursIn, Bool.or_eq_false_iff] at h
      rcases List.mem_cons.mp ht with rfl | ht'
      · exact h.1
      · exact ih ht' h.2

/-- A successful lookup exhibits the binding as a member of the substitution. -/
lemma Subst.lookup_mem {σ : Subst F X 𝔸} {y : X} {s : ntm F X 𝔸}
    (h : Subst.lookup σ y = some s) : (y, s) ∈ σ := by
  induction σ with
  | nil => simp [Subst.lookup] at h
  | cons p σ' ih =>
      obtain ⟨Y, t⟩ := p
      simp only [Subst.lookup_cons] at h
      split at h
      · rename_i he; subst he; simp only [Option.some.injEq] at h; subst h; simp
      · exact List.mem_cons_of_mem _ (ih h)

-- ===========================================================================
-- Explicit most-general-unifier mediator.
--
-- The completeness proof shows the algorithm's substitution `σ` is principal by
-- using each competing solution `θ` as its own mediator (`θ` absorbs itself).
-- Here we build the *canonical* mediator instead: for a solution `θ`, the
-- substitution `σ' := θ` with the bindings whose variable is already in
-- `dom σ` removed.  We prove `σ'` has domain disjoint from `σ` and still
-- witnesses `Xσσ' ≈α Xθ`.  This is the "`θ` is `σ` composed with a further,
-- independent instantiation `σ'`" statement expected in unification theory.
--
-- Throughout, `Xσ` abbreviates `(ntm.mvar [] X).subst σ`.  The delicate point
-- is that substitutions are *sequential lists*: dropping bindings from `θ` is
-- only harmless because the dropped variables do not reappear, which follows
-- from `σ` and `θ` being idempotent with no trivial (identity) bindings.
-- ===========================================================================

-- If a term `v` is fixed by `σ` and a variable `z` occurs in `v`, then `σ` also
-- fixes the bare metavariable `z`.  (Contrapositive: a variable that `σ` moves
-- cannot occur in any `σ`-fixed term.)  Proved by induction on `v`; the `mvar`
-- case cancels the suspended permutation using that `permute` preserves the
-- metavariable and its suspension list.
mutual
  lemma ntm.subst_fixed_of_occurs {σ : Subst F X 𝔸} {z : X} :
      ∀ {v : ntm F X 𝔸}, v.subst σ = v → v.occursIn z = true →
        (ntm.mvar (F := F) [] z).subst σ = ntm.mvar [] z
    | .atm _, _, hocc => by simp [ntm.occursIn] at hocc
    | .mvar π y, hfix, hocc => by
        simp only [ntm.occursIn, beq_iff_eq] at hocc
        subst hocc
        rw [ntm.subst_mvar] at hfix
        -- hfix : ntm.permute π ((mvar [] z).subst σ) = mvar π z ; goal : (mvar [] z).subst σ = mvar [] z
        generalize hm : (ntm.mvar (F := F) [] z).subst σ = m at hfix ⊢
        -- `permute π m` is a metavariable, so `m` is a metavariable.
        cases m with
        | atm _ => simp [ntm.permute] at hfix
        | fapp _ _ => simp [ntm.permute] at hfix
        | abs _ _ => simp [ntm.permute] at hfix
        | mvar ρ x =>
            simp only [ntm.permute] at hfix
            -- hfix : mvar (π ++ ρ) x = mvar π z
            injection hfix with hlist hx
            -- hlist : π ++ ρ = π, hx : x = z
            have hρ : ρ = [] := by
              have hlen := congrArg List.length hlist
              simp only [List.length_append] at hlen
              have : ρ.length = 0 := by omega
              exact List.length_eq_zero_iff.mp this
            rw [hρ, hx]
    | .fapp f ts, hfix, hocc => by
        rw [ntm.subst_fapp] at hfix
        injection hfix with _ hts
        simp only [ntm.occursIn] at hocc
        exact ntmList.subst_fixed_of_occurs hts hocc
    | .abs a t', hfix, hocc => by
        rw [ntm.subst_abs] at hfix
        injection hfix with _ ht'
        simp only [ntm.occursIn] at hocc
        exact ntm.subst_fixed_of_occurs ht' hocc

  lemma ntmList.subst_fixed_of_occurs {σ : Subst F X 𝔸} {z : X} :
      ∀ {ts : List (ntm F X 𝔸)}, ts.map (·.subst σ) = ts →
        ntmList.occursIn z ts = true →
        (ntm.mvar (F := F) [] z).subst σ = ntm.mvar [] z
    | [], _, hocc => by simp [ntmList.occursIn] at hocc
    | t :: ts', hfix, hocc => by
        rw [List.map_cons] at hfix
        injection hfix with ht hts'
        simp only [ntmList.occursIn, Bool.or_eq_true] at hocc
        rcases hocc with hocc | hocc
        · exact ntm.subst_fixed_of_occurs ht hocc
        · exact ntmList.subst_fixed_of_occurs hts' hocc
end

-- A substitution is in *solved form* when no variable of its domain occurs in
-- any of its (raw) binding values, i.e. `dom σ ∩ range σ = ∅`.  For sequential
-- (list) substitutions this is strictly stronger than idempotence of the action
-- (`IsIdempotent`): `[Y ↦ X, X ↦ a]` is idempotent as an action but not in
-- solved form (`X` is in the domain and in the value `X` of `Y`).  Solved form
-- is what makes dropping bindings safe; the unification algorithm outputs it.
def Subst.SolvedForm (σ : Subst F X 𝔸) : Prop :=
  ∀ p ∈ σ, ∀ z ∈ σ.dom, p.2.occursIn z = false

-- `applyOne Y s` does not introduce an occurrence of `z ≠ Y`, as long as `z`
-- occurs in neither the term nor `s`.
mutual
  lemma ntm.occursIn_applyOne_of_ne {Y : X} {s : ntm F X 𝔸} {z : X}
      (hzY : z ≠ Y) (hs : s.occursIn z = false) :
      ∀ {t : ntm F X 𝔸}, t.occursIn z = false → (t.applyOne Y s).occursIn z = false
    | .atm _, _ => by simp [ntm.applyOne, ntm.occursIn]
    | .mvar π w, ht => by
        simp only [ntm.applyOne]
        by_cases hw : w = Y
        · subst hw; rw [if_pos rfl, ntm.occursIn_permute]; exact hs
        · rw [if_neg hw]; exact ht
    | .fapp f ts, ht => by
        simp only [ntm.applyOne, ntm.occursIn] at ht ⊢
        exact ntmList.occursIn_applyOne_of_ne hzY hs ht
    | .abs a t', ht => by
        simp only [ntm.applyOne, ntm.occursIn] at ht ⊢
        exact ntm.occursIn_applyOne_of_ne hzY hs ht

  lemma ntmList.occursIn_applyOne_of_ne {Y : X} {s : ntm F X 𝔸} {z : X}
      (hzY : z ≠ Y) (hs : s.occursIn z = false) :
      ∀ {ts : List (ntm F X 𝔸)}, ntmList.occursIn z ts = false →
        ntmList.occursIn z (ts.map (·.applyOne Y s)) = false
    | [], _ => rfl
    | t :: ts', ht => by
        simp only [List.map_cons, ntmList.occursIn, Bool.or_eq_false_iff] at ht ⊢
        exact ⟨ntm.occursIn_applyOne_of_ne hzY hs ht.1,
               ntmList.occursIn_applyOne_of_ne hzY hs ht.2⟩
end

-- Substituting by `σ` cannot introduce a variable `w` that all of `σ`'s values
-- avoid, if the term already avoids `w`.  Induction on the term `v`: at a
-- metavariable, the value (from `lookup`) avoids `w` by hypothesis, and the
-- suspended permutation does not affect `occursIn`.
mutual
lemma ntm.occursIn_subst_of_avoid {w : X} {σ : Subst F X 𝔸}
    (hσ : ∀ p ∈ σ, p.2.occursIn w = false) :
    ∀ {v : ntm F X 𝔸}, v.occursIn w = false → (v.subst σ).occursIn w = false
  | .atm _, _ => by simp [ntm.subst, ntm.occursIn]
  | .mvar π y, hv => by
      rw [ntm.subst_mvar]
      rw [ntm.occursIn_permute]
      rw [ntm.subst_mvar_nil]
      cases hl : Subst.lookup σ y with
      | none => simpa using hv
      | some s =>
          simp only [Option.getD_some]
          exact hσ (y, s) (Subst.lookup_mem hl)
  | .fapp f ts, hv => by
      rw [ntm.subst_fapp]
      simp only [ntm.occursIn] at hv ⊢
      exact ntmList.occursIn_substList_of_avoid hσ hv
  | .abs a t, hv => by
      rw [ntm.subst_abs]
      simp only [ntm.occursIn] at hv ⊢
      exact ntm.occursIn_subst_of_avoid hσ hv

lemma ntmList.occursIn_substList_of_avoid {w : X} {σ : Subst F X 𝔸}
    (hσ : ∀ p ∈ σ, p.2.occursIn w = false) :
    ∀ {ts : List (ntm F X 𝔸)}, ntmList.occursIn w ts = false →
      ntmList.occursIn w (ts.map (·.subst σ)) = false
  | [], _ => rfl
  | t :: ts', hv => by
      simp only [List.map_cons, ntmList.occursIn, Bool.or_eq_false_iff] at hv ⊢
      exact ⟨ntm.occursIn_subst_of_avoid hσ hv.1,
             ntmList.occursIn_substList_of_avoid hσ hv.2⟩
end

-- For a solved-form `σ`, the result `t.subst σ` avoids every variable of
-- `dom σ`: the domain variable is either removed (occurs-check on its binding)
-- or was never there, and no value reintroduces it (solved form).  Induction on
-- `σ`.
mutual
lemma ntm.subst_avoids_dom_of_solved (σ : Subst F X 𝔸) (hσ : σ.SolvedForm)
    (z : X) (hz : z ∈ σ.dom) :
    ∀ (t : ntm F X 𝔸), (t.subst σ).occursIn z = false
  | .atm _ => by simp [ntm.subst, ntm.occursIn]
  | .mvar π y => by
      rw [ntm.subst_mvar, ntm.occursIn_permute, ntm.subst_mvar_nil]
      cases hl : Subst.lookup σ y with
      | none =>
          simp only [Option.getD_none, ntm.occursIn, beq_eq_false_iff_ne]
          intro rfl
          exact ((Subst.lookup_eq_none_iff_not_mem_dom σ z).mp hl) hz
      | some s =>
          simp only [Option.getD_some]
          exact hσ (y, s) (Subst.lookup_mem hl) z hz
  | .fapp f ts => by
      rw [ntm.subst_fapp]; simp only [ntm.occursIn]
      exact ntmList.substList_avoids_dom_of_solved σ hσ z hz ts
  | .abs a t => by
      rw [ntm.subst_abs]; simp only [ntm.occursIn]
      exact ntm.subst_avoids_dom_of_solved σ hσ z hz t

lemma ntmList.substList_avoids_dom_of_solved (σ : Subst F X 𝔸) (hσ : σ.SolvedForm)
    (z : X) (hz : z ∈ σ.dom) :
    ∀ (ts : List (ntm F X 𝔸)), ntmList.occursIn z (ts.map (·.subst σ)) = false
  | [] => rfl
  | t :: ts' => by
      simp only [List.map_cons, ntmList.occursIn, Bool.or_eq_false_iff]
      exact ⟨ntm.subst_avoids_dom_of_solved σ hσ z hz t,
             ntmList.substList_avoids_dom_of_solved σ hσ z hz ts'⟩
end

-- Looking up in `θ` filtered by "key ∉ dom σ": a key in `dom σ` is dropped
-- (misses), otherwise the lookup is unchanged.
lemma Subst.lookup_filter_not_mem_dom {σ : Subst F X 𝔸} (θ : Subst F X 𝔸) (y : X) :
    Subst.lookup (θ.filter (fun p => decide (p.1 ∉ σ.dom))) y
      = if y ∈ σ.dom then none else Subst.lookup θ y := by
  induction θ with
  | nil => simp [Subst.lookup]
  | cons p θ₀ ih =>
      obtain ⟨Y, s⟩ := p
      simp only [List.filter_cons]
      by_cases hY : Y ∈ σ.dom
      · simp only [hY, not_true, decide_false, Bool.false_eq_true, if_false, ih]
        by_cases hy : y = Y
        · subst hy; simp [hY]
        · simp only [Subst.lookup_cons, if_neg hy]
      · simp only [hY, not_false_iff, decide_true, if_true, Subst.lookup_cons]
        by_cases hy : y = Y
        · subst hy; simp [hY]
        · simp only [if_neg hy, ih]

-- Drop lemma: bindings of `θ` whose variable lies in `dom σ` are redundant when
-- acting on a term `u` free of the shared variables `dom σ ∩ dom θ`.  Induction
-- on `u`: at a metavariable `y`, either `y ∉ dom σ` (lookup unchanged) or
-- `y ∈ dom σ ∩ dom θ`, which `u` avoids — so `y` is not this metavariable.
lemma ntm.subst_drop_dom {σ : Subst F X 𝔸} (θ : Subst F X 𝔸) :
    ∀ (u : ntm F X 𝔸),
      (∀ z ∈ σ.dom, z ∈ θ.dom → u.occursIn z = false) →
      u.subst (θ.filter (fun p => decide (p.1 ∉ σ.dom))) = u.subst θ
  | .atm _, _ => by simp [ntm.subst]
  | .mvar π y, hu => by
      rw [ntm.subst_mvar, ntm.subst_mvar]
      congr 1
      rw [ntm.subst_mvar_nil, ntm.subst_mvar_nil, Subst.lookup_filter_not_mem_dom]
      by_cases hy : y ∈ σ.dom
      · by_cases hyθ : y ∈ θ.dom
        · exact absurd (by simp [ntm.occursIn] : (ntm.mvar (F := F) [] y).occursIn y = true)
            (by rw [hu y hy hyθ])
        · rw [if_pos hy, (Subst.lookup_eq_none_iff_not_mem_dom θ y).mpr hyθ]
      · rw [if_neg hy]
  | .fapp f ts, hu => by
      rw [ntm.subst_fapp, ntm.subst_fapp]
      congr 1
      apply List.map_congr_left
      intro t ht
      exact ntm.subst_drop_dom θ t (fun z hz hzθ => by
        have := hu z hz hzθ
        simp only [ntm.occursIn] at this
        exact ntmList.not_occursIn_of_mem ht this)
  | .abs a t, hu => by
      rw [ntm.subst_abs, ntm.subst_abs]
      rw [ntm.subst_drop_dom θ t (fun z hz hzθ => by
        have := hu z hz hzθ; simpa only [ntm.occursIn] using this)]

-- Explicit most-general-unifier mediator (`θ ∖ dom σ`).
-- If `σ` and `θ` are both in solved form and `θ` is absorbed by `σ` in `Δ`,
-- then `σ' := θ` with the `dom σ` bindings removed is a mediator: its domain is
-- disjoint from `dom σ`, and `Xσσ' ≈α Xθ` for every metavariable `X`.  This is
-- the canonical "`θ` is `σ` followed by an independent instantiation `σ'`" form;
-- the disjoint domain is what makes it non-trivial (unlike the witness `σ' := θ`).
theorem Subst.solvedForm_mediator {Δ : Context 𝔸 X} {σ θ : Subst F X 𝔸}
    (hσ : σ.SolvedForm) (hθ : θ.SolvedForm) (habs : Subst.absorbedBy Δ σ θ) :
    ∃ σ' : Subst F X 𝔸,
      (∀ z ∈ σ'.dom, z ∉ σ.dom) ∧
      (∀ x : X, (Δ ⊢ ((ntm.mvar (F := F) [] x).subst σ).subst σ'
                  ≈α (ntm.mvar (F := F) [] x).subst θ) = true) := by
  refine ⟨θ.filter (fun p => decide (p.1 ∉ σ.dom)), ?_, ?_⟩
  · -- The filter keeps only bindings whose variable avoids `dom σ`.
    intro z hz
    simp only [Subst.dom, List.mem_toFinset, List.mem_map] at hz
    obtain ⟨p, hpf, hpz⟩ := hz
    rw [List.mem_filter] at hpf
    have hp : p.1 ∉ σ.dom := by
      have h2 := hpf.2
      simp only [decide_eq_true_eq, Subst.dom, List.mem_toFinset, List.mem_map] at h2 ⊢
      exact h2
    rw [← hpz]; exact hp
  · intro x
    have hu : ∀ z ∈ σ.dom, z ∈ Subst.dom θ →
        ((ntm.mvar (F := F) [] x).subst σ).occursIn z = false :=
      fun z hz _ => ntm.subst_avoids_dom_of_solved σ hσ z hz _
    rw [ntm.subst_drop_dom θ ((ntm.mvar (F := F) [] x).subst σ) hu]
    exact habs x

-- `normalize σ` is in solved form, when `σ` is idempotent and genuinely moves
-- every variable of its domain (no trivial `z ↦ z` chains — guaranteed by the
-- occurs-check in the algorithm).  Each value of `normalize σ` is a full image
-- `y.subst σ`, which is `σ`-fixed by idempotence; if a domain variable `z`
-- occurred in it, `subst_fixed_of_occurs` would force `σ` to fix `z`,
-- contradicting that `σ` moves `z`.  Combined with `subst_eq_substSim_normalize`,
-- this shows the algorithm's sequential `σ` computes the simultaneous action of a
-- *solved-form* substitution — exactly the classical picture.
theorem Subst.solvedForm_normalize {σ : Subst F X 𝔸} (hσ : σ.IsIdempotent)
    (hmove : ∀ z ∈ σ.dom, (ntm.mvar (F := F) [] z).subst σ ≠ ntm.mvar [] z) :
    Subst.SolvedForm σ.normalize := by
  intro p hp z hz
  rw [Subst.dom_normalize] at hz
  simp only [Subst.normalize, List.mem_map] at hp
  obtain ⟨q, _, rfl⟩ := hp
  by_contra hocc
  simp only [Bool.not_eq_false] at hocc
  have hfix : ((ntm.mvar (F := F) [] q.1).subst σ).subst σ
      = (ntm.mvar (F := F) [] q.1).subst σ := ntm.subst_idempotent hσ _
  exact hmove z hz (ntm.subst_fixed_of_occurs hfix hocc)

-- ===========================================================================
-- The algorithm's output moves every domain variable (`MovesDom`), so its
-- `normalize` is in solved form (via `solvedForm_normalize`).
--
-- `MovesDom σ` = every `z ∈ dom σ` is genuinely changed by `σ` (`z.subst σ ≠ z`).
-- The occurs-check guarantees this for each binding; we thread it through the
-- recursion `unify`, mirroring `unify_preserves_idempotent`.
-- ===========================================================================

/-- `σ` moves every variable of its domain. -/
def Subst.MovesDom (σ : Subst F X 𝔸) : Prop :=
  ∀ z ∈ σ.dom, (ntm.mvar (F := F) [] z).subst σ ≠ ntm.mvar [] z

/-- Appending an occurs-check-passing, `σ`-fixed binding preserves `MovesDom`.
    For the new variable `x`, the value `u` avoids `x` (occurs-check), so
    `x.subst = u ≠ x`.  For an old `z ∈ dom σ`, apply `subst σ` to a would-be
    equation `(z.subst σ).applyOne x u = z`: the left side is `σ`-stable, so it
    collapses to `z.subst σ = z`, contradicting `MovesDom σ`. -/
lemma Subst.MovesDom.comp_singleton {σ : Subst F X 𝔸} {x : X} {u : ntm F X 𝔸}
    (hmove : σ.MovesDom) (hσ : σ.IsIdempotent) (hx : x ∉ σ.dom)
    (hu_fixed : u.subst σ = u) (hxu : u.occursIn x = false) :
    (σ.comp [(x, u)]).MovesDom := by
  intro z hz
  have hexp : (ntm.mvar (F := F) [] z).subst (σ.comp [(x, u)])
      = ((ntm.mvar (F := F) [] z).subst σ).applyOne x u := by
    rw [ntm.subst_mvar_nil_comp, ntm.subst_singleton]
  rw [hexp, Subst.dom_comp, Subst.dom_singleton, Finset.mem_union,
      Finset.mem_singleton] at *
  rcases hz with hz | rfl
  · intro heq
    have hr_fixed := ntm.subst_idempotent hσ (ntm.mvar (F := F) [] z)
    have hstable := ntm.applyOne_subst_of_stable
      ((ntm.mvar (F := F) [] z).subst σ) x u σ hr_fixed hu_fixed
    rw [heq] at hstable
    exact hmove z hz hstable
  · rw [ntm.subst_mvar_nil_of_not_mem_dom hx]
    simp only [ntm.applyOne, beq_self_eq_true, if_true, ntm.permute_nil]
    intro heq
    rw [heq] at hxu
    simp [ntm.occursIn] at hxu

/-- For an instantiation step, the three side-conditions on the new binding:
    the variable is outside `dom σ`, the value is `σ`-fixed, and passes the
    occurs-check.  Extracted uniformly from the invariants (mirrors the setup
    inside `instantiation_invariant`). -/
lemma instantiation_binding_props
    (σ : Subst F X 𝔸) (rest : UnifProblem F X 𝔸) (c : UnifConstraint F X 𝔸)
    (x : X) (u_perm : ntm F X 𝔸)
    (hdisj : σ.disjointPr (c :: rest))
    (hx_in_c : x ∈ c.metavars)
    (hu_perm_in_c : ∀ z ∈ u_perm.metavars, z ∈ c.metavars)
    (hocc : u_perm.occursIn x = false) :
    x ∉ σ.dom ∧ u_perm.subst σ = u_perm ∧ u_perm.occursIn x = false := by
  refine ⟨?_, ?_, hocc⟩
  · apply hdisj; simp [UnifProblem.allMetavars_cons]; left; exact hx_in_c
  · apply ntm.subst_of_disjoint_dom
    intro y hy
    rw [ntm.occursIn_false_iff_not_mem_metavars]
    intro hy_in
    have hy_all : y ∈ UnifProblem.allMetavars (c :: rest) := by
      simp only [UnifProblem.allMetavars_cons, Finset.mem_union]
      left; exact hu_perm_in_c y hy_in
    exact hdisj y hy_all hy

/-- Every `.next` step either leaves `σ` unchanged (non-instantiation steps) or
    appends a single binding satisfying the three side-conditions.  This is the
    uniform classifier used to thread `MovesDom` (and reusable for any other
    binding-level invariant), mirroring the case split of
    `unifStep_next_idempotent_and_disjoint`. -/
lemma unifStep_next_binding_props
    (c : UnifConstraint F X 𝔸) (rest : UnifProblem F X 𝔸) (σ : Subst F X 𝔸)
    (Pr' : UnifProblem F X 𝔸) (σ_next : Subst F X 𝔸)
    (h : unifStep c rest σ = .next Pr' σ_next)
    (hdisj : σ.disjointPr (c :: rest)) :
    σ_next = σ ∨ ∃ (x : X) (u : ntm F X 𝔸), σ_next = σ.comp [(x, u)] ∧
      x ∉ σ.dom ∧ u.subst σ = u ∧ u.occursIn x = false := by
  cases c with
  | fresh a t =>
    cases t with
    | mvar π x => simp [unifStep] at h
    | atm b =>
      simp only [unifStep, simplifyFresh] at h
      by_cases hab : a = b
      · rw [if_pos hab] at h; cases h
      · simp only [if_neg hab, List.map_nil, List.append_nil,
                   StepResult.next.injEq] at h
        obtain ⟨_, rfl⟩ := h; exact Or.inl rfl
    | fapp f ts =>
      simp only [unifStep, simplifyFresh] at h
      cases hcs : simplifyFreshList a ts with
      | none => rw [hcs] at h; cases h
      | some cs =>
        rw [hcs] at h; simp only [StepResult.next.injEq] at h
        obtain ⟨_, rfl⟩ := h; exact Or.inl rfl
    | abs b t =>
      simp only [unifStep, simplifyFresh] at h
      by_cases hab : a = b
      · simp only [if_pos hab, List.map_nil, List.append_nil,
                   StepResult.next.injEq] at h
        obtain ⟨_, rfl⟩ := h; exact Or.inl rfl
      · rw [if_neg hab] at h
        cases hcs : simplifyFresh a t with
        | none => rw [hcs] at h; cases h
        | some cs =>
          rw [hcs] at h; simp only [StepResult.next.injEq] at h
          obtain ⟨_, rfl⟩ := h; exact Or.inl rfl
  | unif s t =>
    cases s with
    | atm a =>
      cases t with
      | atm b =>
        simp only [unifStep] at h
        by_cases hab : a = b
        · simp only [if_pos hab, StepResult.next.injEq] at h
          obtain ⟨_, rfl⟩ := h; exact Or.inl rfl
        · simp only [if_neg hab] at h; cases h
      | mvar π x =>
        simp only [unifStep, ntm.occursIn, Bool.false_eq_true, if_false,
                   StepResult.next.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine Or.inr ⟨x, (ntm.atm (X := X) (F := F) a).permute π.reverse, rfl,
          instantiation_binding_props σ rest
            (UnifConstraint.unif (ntm.atm a) (ntm.mvar π x)) x
            ((ntm.atm (X := X) (F := F) a).permute π.reverse) hdisj ?_ ?_ ?_⟩
        · simp [UnifConstraint.metavars, ntm.metavars]
        · intro z hz; simp [ntm.permute, ntm.metavars] at hz
        · simp [ntm.permute, ntm.occursIn]
      | fapp _ _ | abs _ _ => simp [unifStep] at h
    | mvar π x =>
      cases t with
      | atm a =>
        simp only [unifStep, ntm.occursIn, Bool.false_eq_true, if_false,
                   StepResult.next.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine Or.inr ⟨x, (ntm.atm (X := X) (F := F) a).permute π.reverse, rfl,
          instantiation_binding_props σ rest
            (UnifConstraint.unif (ntm.mvar π x) (ntm.atm a)) x
            ((ntm.atm (X := X) (F := F) a).permute π.reverse) hdisj ?_ ?_ ?_⟩
        · simp [UnifConstraint.metavars, ntm.metavars]
        · intro z hz; simp [ntm.permute, ntm.metavars] at hz
        · simp [ntm.permute, ntm.occursIn]
      | mvar π' y =>
        simp only [unifStep] at h
        by_cases hxy : x = y
        · subst hxy
          simp only [if_pos rfl, StepResult.next.injEq] at h
          obtain ⟨_, rfl⟩ := h; exact Or.inl rfl
        · simp only [if_neg hxy, StepResult.next.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine Or.inr ⟨x, (ntm.mvar (F := F) π' y).permute π.reverse, rfl,
            instantiation_binding_props σ rest
              (UnifConstraint.unif (ntm.mvar π x) (ntm.mvar π' y)) x
              ((ntm.mvar (F := F) π' y).permute π.reverse) hdisj ?_ ?_ ?_⟩
          · simp [UnifConstraint.metavars, ntm.metavars]
          · intro z hz
            simp [UnifConstraint.metavars, ntm.metavars]
            right
            rw [ntm.permute_metavars] at hz
            simp [ntm.metavars] at hz; exact hz
          · rw [ntm.occursIn_permute]
            simp only [ntm.occursIn, beq_eq_false_iff_ne]
            exact hxy
      | fapp g ts =>
        simp only [unifStep] at h
        split_ifs at h with hocc
        simp only [StepResult.next.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [Bool.not_eq_true] at hocc
        refine Or.inr ⟨x, (ntm.fapp (X := X) (𝔸 := 𝔸) g ts).permute π.reverse, rfl,
          instantiation_binding_props σ rest
            (UnifConstraint.unif (ntm.mvar π x) (ntm.fapp g ts)) x
            ((ntm.fapp (X := X) (𝔸 := 𝔸) g ts).permute π.reverse) hdisj ?_ ?_ ?_⟩
        · simp [UnifConstraint.metavars, ntm.metavars]
        · intro z hz
          simp [UnifConstraint.metavars, ntm.metavars]
          right
          rw [ntm.permute_metavars] at hz
          exact hz
        · rw [ntm.occursIn_permute]; exact hocc
      | abs b t =>
        simp only [unifStep] at h
        split_ifs at h with hocc
        simp only [StepResult.next.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [Bool.not_eq_true] at hocc
        refine Or.inr ⟨x, (ntm.abs (X := X) b t).permute π.reverse, rfl,
          instantiation_binding_props σ rest
            (UnifConstraint.unif (ntm.mvar π x) (ntm.abs b t)) x
            ((ntm.abs (X := X) b t).permute π.reverse) hdisj ?_ ?_ ?_⟩
        · simp [UnifConstraint.metavars, ntm.metavars]
        · intro z hz
          simp [UnifConstraint.metavars, ntm.metavars]
          right
          rw [ntm.permute_metavars] at hz
          exact hz
        · rw [ntm.occursIn_permute]; exact hocc
    | fapp f ss =>
      cases t with
      | atm _    => simp [unifStep] at h
      | mvar π' y =>
        simp only [unifStep] at h
        split_ifs at h with hocc
        simp only [StepResult.next.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [Bool.not_eq_true] at hocc
        refine Or.inr ⟨y, (ntm.fapp (X := X) (𝔸 := 𝔸) f ss).permute π'.reverse, rfl,
          instantiation_binding_props σ rest
            (UnifConstraint.unif (ntm.fapp f ss) (ntm.mvar π' y)) y
            ((ntm.fapp (X := X) (𝔸 := 𝔸) f ss).permute π'.reverse) hdisj ?_ ?_ ?_⟩
        · show y ∈ (UnifConstraint.unif (X := X) (𝔸 := 𝔸)
              (ntm.fapp f ss) (ntm.mvar π' y)).metavars
          simp only [UnifConstraint.metavars]
          exact Finset.mem_union_right _ (by simp [ntm.metavars])
        · intro z hz
          rw [ntm.permute_metavars] at hz
          show z ∈ (UnifConstraint.unif (X := X) (𝔸 := 𝔸)
              (ntm.fapp f ss) (ntm.mvar π' y)).metavars
          simp only [UnifConstraint.metavars]
          exact Finset.mem_union_left _ hz
        · rw [ntm.occursIn_permute]; exact hocc
      | abs _ _  => simp [unifStep] at h
      | fapp g ts =>
        simp only [unifStep] at h
        by_cases hfg : f = g ∧ ss.length = ts.length
        · simp only [if_pos hfg, StepResult.next.injEq] at h
          obtain ⟨_, rfl⟩ := h; exact Or.inl rfl
        · simp only [if_neg hfg] at h; cases h
    | abs a s' =>
      cases t with
      | atm _    => simp [unifStep] at h
      | fapp _ _ => simp [unifStep] at h
      | mvar π' y =>
        simp only [unifStep] at h
        split_ifs at h with hocc
        simp only [StepResult.next.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [Bool.not_eq_true] at hocc
        refine Or.inr ⟨y, (ntm.abs (F := F) a s').permute π'.reverse, rfl,
          instantiation_binding_props σ rest
            (UnifConstraint.unif (ntm.abs a s') (ntm.mvar π' y)) y
            ((ntm.abs (F := F) a s').permute π'.reverse) hdisj ?_ ?_ ?_⟩
        · show y ∈ (UnifConstraint.unif (X := X) (𝔸 := 𝔸)
              (ntm.abs a s') (ntm.mvar π' y)).metavars
          simp only [UnifConstraint.metavars]
          exact Finset.mem_union_right _ (by simp [ntm.metavars])
        · intro z hz
          rw [ntm.permute_metavars] at hz
          show z ∈ (UnifConstraint.unif (X := X) (𝔸 := 𝔸)
              (ntm.abs a s') (ntm.mvar π' y)).metavars
          simp only [UnifConstraint.metavars]
          exact Finset.mem_union_left _ hz
        · rw [ntm.occursIn_permute]; exact hocc
      | abs b t' =>
        simp only [unifStep] at h
        by_cases hab : a = b
        · simp only [if_pos hab, StepResult.next.injEq] at h
          obtain ⟨_, rfl⟩ := h; exact Or.inl rfl
        · simp only [if_neg hab, StepResult.next.injEq] at h
          obtain ⟨_, rfl⟩ := h; exact Or.inl rfl

/-- `unifStep` preserves `MovesDom` under the idempotence/disjointness invariant. -/
lemma unifStep_next_movesDom
    (c : UnifConstraint F X 𝔸) (rest : UnifProblem F X 𝔸) (σ : Subst F X 𝔸)
    (Pr' : UnifProblem F X 𝔸) (σ_next : Subst F X 𝔸)
    (h : unifStep c rest σ = .next Pr' σ_next)
    (hσ : σ.IsIdempotent) (hdisj : σ.disjointPr (c :: rest))
    (hmove : σ.MovesDom) : σ_next.MovesDom := by
  rcases unifStep_next_binding_props c rest σ Pr' σ_next h hdisj with rfl | ⟨x, u, rfl, hx, hu, hxu⟩
  · exact hmove
  · exact hmove.comp_singleton hσ hx hu hxu

/-- `unify` preserves `MovesDom`, mirroring `unify_preserves_idempotent`. -/
theorem unify_preserves_movesDom :
    ∀ (Pr : UnifProblem F X 𝔸) (σ : Subst F X 𝔸) (ds : List (𝔸 × X))
      (ds' : List (𝔸 × X)) (σ' : Subst F X 𝔸),
      unify Pr σ ds = some (ds', σ') →
      σ.IsIdempotent → σ.disjointPr Pr → σ.MovesDom → σ'.MovesDom := by
  intro Pr σ ds
  induction Pr, σ, ds using unify.induct with
  | case1 σ ds =>
      intro ds' σ' h _ _ hmove
      simp only [unify, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨_, rfl⟩ := h; exact hmove
  | case2 σ ds c rest hfail =>
      intro ds' σ' h _ _ _
      rw [unify, hfail] at h; cases h
  | case3 σ ds c rest a x hctx ih =>
      intro ds' σ' h hσ hdisj hmove
      rw [unify, hctx] at h
      exact ih ds' σ' h hσ (Subst.disjointPr_cons hdisj) hmove
  | case4 σ ds c rest Pr' σ_next hnext ih =>
      intro ds' σ' h hσ hdisj hmove
      rw [unify, hnext] at h
      obtain ⟨hσ_next, hdisj_next⟩ :=
        unifStep_next_idempotent_and_disjoint c rest σ Pr' σ_next hnext hσ hdisj
      exact ih ds' σ' h hσ_next hdisj_next
        (unifStep_next_movesDom c rest σ Pr' σ_next hnext hσ hdisj hmove)

/-- The substitution produced by `solve` moves every variable of its domain. -/
theorem UnifProblem.solve_movesDom (Pr : UnifProblem F X 𝔸) (Γ : Context 𝔸 X)
    (σ : Subst F X 𝔸) (h : Pr.solve = some (Γ, σ)) : σ.MovesDom := by
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
      obtain ⟨_, hσeq⟩ := h
      subst hσeq
      have hσ_empty : Subst.IsIdempotent ([] : Subst F X 𝔸) := fun x => by simp
      have hdisj_empty : Subst.disjointPr ([] : Subst F X 𝔸) Pr := by
        intro x _; simp [Subst.dom]
      have hmove_empty : Subst.MovesDom ([] : Subst F X 𝔸) := by
        intro z hz; simp [Subst.dom] at hz
      exact unify_preserves_movesDom Pr [] [] ds σ_u hu hσ_empty hdisj_empty hmove_empty

/-- The `normalize` of `solve`'s output is in solved form: the algorithm's
    sequential substitution computes the simultaneous action of a solved-form
    substitution (`subst_eq_substSim_normalize` + `solvedForm_normalize`). -/
theorem UnifProblem.solve_normalize_solvedForm (Pr : UnifProblem F X 𝔸)
    (Γ : Context 𝔸 X) (σ : Subst F X 𝔸) (h : Pr.solve = some (Γ, σ)) :
    Subst.SolvedForm σ.normalize :=
  Subst.solvedForm_normalize (UnifProblem.solve_idempotent Pr Γ σ h)
    (UnifProblem.solve_movesDom Pr Γ σ h)

-- ===========================================================================
-- End-to-end explicit mediator for the algorithm's output.
--
-- On a *solved-form* substitution sequential and simultaneous substitution
-- coincide, so `normalize σ` acts exactly as `σ` and the explicit mediator
-- `θ ∖ dom σ` applies to the algorithm's output.  Assembled below into a single
-- statement: for `solve`'s output and any solved-form solution `θ`, the guessed
-- mediator works.
-- ===========================================================================

/-- A sub-substitution of a solved-form substitution is in solved form. -/
lemma Subst.SolvedForm.of_cons {p : X × ntm F X 𝔸} {ρ : Subst F X 𝔸}
    (h : Subst.SolvedForm (p :: ρ)) : Subst.SolvedForm ρ :=
  fun q hq z hz => h q (List.mem_cons_of_mem _ hq) z
    (by rw [Subst.dom_cons]; exact Finset.mem_insert_of_mem hz)

/-- On a solved-form `ρ`, the sequential value of a metavariable is exactly its
    one-shot lookup: no re-scanning happens because values avoid the domain. -/
lemma ntm.subst_mvar_eq_lookupSim :
    ∀ (ρ : Subst F X 𝔸), Subst.SolvedForm ρ → ∀ (x : X),
      (ntm.mvar (F := F) [] x).subst ρ = ρ.lookupSim x
  | [], _, x => by simp [Subst.lookupSim, ntm.subst_nil]
  | (y, s) :: ρ₀, hsolved, x => by
      rw [ntm.subst_singleton]
      unfold Subst.lookupSim
      rw [List.find?_cons]
      by_cases hxy : x = y
      · subst hxy
        simp only [ntm.applyOne, beq_self_eq_true, if_true, ntm.permute_nil,
                   Option.elim_some]
        apply ntm.subst_of_disjoint_dom
        intro z hz
        exact hsolved (x, s) (by simp) z
          (by rw [Subst.dom_cons]; exact Finset.mem_insert_of_mem hz)
      · have hyx : (y == x) = false := by
          simp only [beq_eq_false_iff_ne]; exact fun h => hxy h.symm
        rw [hyx]
        simp only [ntm.applyOne, if_neg hxy]
        exact ntm.subst_mvar_eq_lookupSim ρ₀ hsolved.of_cons x

/-- On a solved-form substitution, sequential and simultaneous substitution
    agree outright: `t.subst ρ = t.substSim ρ`. -/
lemma ntm.subst_eq_substSim_of_solved (ρ : Subst F X 𝔸) (hρ : Subst.SolvedForm ρ) :
    ∀ t : ntm F X 𝔸, t.subst ρ = t.substSim ρ
  | .atm a => by simp [ntm.substSim, ntm.subst_atm]
  | .mvar π x => by
      rw [ntm.substSim, ntm.subst_mvar, ntm.subst_mvar_eq_lookupSim ρ hρ x]
  | .fapp f ts => by
      rw [ntm.substSim, ntm.subst_fapp]
      congr 1
      exact List.map_congr_left (fun t _ => ntm.subst_eq_substSim_of_solved ρ hρ t)
  | .abs a t => by
      rw [ntm.substSim, ntm.subst_abs, ntm.subst_eq_substSim_of_solved ρ hρ t]

/-- The algorithm's output `σ` and its normalisation act identically:
    `t.subst σ = t.subst (normalize σ)` for every term.  (Sequential `σ` =
    simultaneous `normalize σ` by `subst_eq_substSim_normalize`; and on the
    solved-form `normalize σ`, sequential = simultaneous.) -/
theorem UnifProblem.solve_subst_eq_normalize (Pr : UnifProblem F X 𝔸)
    (Γ : Context 𝔸 X) (σ : Subst F X 𝔸) (h : Pr.solve = some (Γ, σ))
    (t : ntm F X 𝔸) : t.subst σ = t.subst σ.normalize := by
  rw [ntm.subst_eq_substSim_normalize σ t,
      ntm.subst_eq_substSim_of_solved σ.normalize
        (UnifProblem.solve_normalize_solvedForm Pr Γ σ h) t]

/-- Every solution `(Δ, θ)` is absorbed by the algorithm's output `σ`.  This is
    the absorption invariant established inside `solve_principal`, isolated here
    so the explicit mediator can be assembled. -/
theorem UnifProblem.solve_absorbedBy (Pr : UnifProblem F X 𝔸) (Γ : Context 𝔸 X)
    (σ : Subst F X 𝔸) (h : Pr.solve = some (Γ, σ)) (Δ : Context 𝔸 X)
    (θ : Subst F X 𝔸) (hq : (Δ, θ) ∈ Pr.Solutions) : Subst.absorbedBy Δ σ θ := by
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
      obtain ⟨_, hσeq⟩ := h
      subst hσeq
      have habs0 : Subst.absorbedBy Δ ([] : Subst F X 𝔸) θ := Subst.absorbedBy_nil Δ θ
      have hds0 : ∀ p ∈ ([] : List (𝔸 × X)),
          (Δ ⊢ p.1 # (ntm.mvar (F := F) [] p.2).subst θ) = true := by
        intros _ hp; cases hp
      exact (unify_le Pr [] [] ds σ_u Δ θ hu hq habs0 hds0).1

-- ===========================================================================
-- Removing the solved-form hypothesis on θ (ressalva b).
--
-- A competing solution θ need only be idempotent-as-an-action (Definition 27),
-- not in solved form: e.g. `[z ↦ x, x ↦ z]` acts as `z ↦ z, x ↦ z`.  Its
-- *reduction* `reduce θ` — normalise, then drop the now-trivial bindings
-- `z ↦ z` — is always in solved form (no `MovesDom` needed) and has the same
-- action as θ.  So the explicit mediator applies to any solution.
-- ===========================================================================

/-- Auxiliary: if every element satisfying `P` also satisfies `Q`, then filtering
    by `Q` first does not change `find? P`. -/
private lemma find?_and_of_imp {α : Type*} {P Q : α → Bool} :
    ∀ {L : List α}, (∀ a ∈ L, P a → Q a) →
      L.find? (fun a => P a && Q a) = L.find? P
  | [], _ => rfl
  | a :: L₀, h => by
      simp only [List.find?_cons]
      by_cases hp : P a = true
      · have hq : Q a = true := h a (by simp) hp
        simp [hp, hq]
      · simp only [hp, Bool.false_and, Bool.false_eq_true]
        exact find?_and_of_imp (fun a' ha' => h a' (by simp [ha']))

/-- A binding is *trivial* when it maps its variable to itself (`x ↦ x`).
    Structural test — avoids needing `DecidableEq` on terms. -/
def Subst.isTrivialBinding (p : X × ntm F X 𝔸) : Bool :=
  match p.2 with
  | .mvar [] y => decide (y = p.1)
  | _          => false

lemma Subst.not_isTrivial_iff {p : X × ntm F X 𝔸} :
    (!Subst.isTrivialBinding p) = true ↔ p.2 ≠ ntm.mvar [] p.1 := by
  obtain ⟨y0, t0⟩ := p
  simp only [Subst.isTrivialBinding]
  cases t0 with
  | atm _ => simp
  | fapp _ _ => simp
  | abs _ _ => simp
  | mvar π z =>
      cases π with
      | nil => simp [decide_eq_false_iff_not, ntm.mvar.injEq]
      | cons b π' => simp [ntm.mvar.injEq]

/-- The reduction of `σ`: its simultaneous normalisation with the now-trivial
    self-bindings removed.  Always in solved form and equivalent in action. -/
def Subst.reduce (σ : Subst F X 𝔸) : Subst F X 𝔸 :=
  σ.normalize.filter (fun p => !Subst.isTrivialBinding p)

lemma Subst.mem_reduce {σ : Subst F X 𝔸} {p : X × ntm F X 𝔸} :
    p ∈ σ.reduce ↔ p ∈ σ.normalize ∧ p.2 ≠ ntm.mvar [] p.1 := by
  unfold Subst.reduce
  rw [List.mem_filter]
  constructor
  · exact fun h => ⟨h.1, Subst.not_isTrivial_iff.mp h.2⟩
  · exact fun h => ⟨h.1, Subst.not_isTrivial_iff.mpr h.2⟩

/-- The reduction looks up each variable to its full image `x.subst θ` — same as
    `normalize`, since dropping a trivial binding `x ↦ x` leaves the default `x`. -/
lemma Subst.lookupSim_reduce (θ : Subst F X 𝔸) (x : X) :
    θ.reduce.lookupSim x = (ntm.mvar (F := F) [] x).subst θ := by
  have hn := Subst.lookupSim_normalize θ x
  unfold Subst.lookupSim at hn ⊢
  unfold Subst.reduce
  rw [List.find?_filter]
  by_cases hx : (ntm.mvar (F := F) [] x).subst θ = ntm.mvar [] x
  · have hnone : θ.normalize.find?
        (fun a => decide (((!Subst.isTrivialBinding a) = true) ∧ ((a.1 == x) = true)))
        = none := by
      rw [List.find?_eq_none]
      intro p hp
      simp only [decide_eq_true_eq, beq_iff_eq, not_and]
      intro hnt hpx
      have hne := Subst.not_isTrivial_iff.mp hnt
      simp only [Subst.normalize, List.mem_map] at hp
      obtain ⟨q, _, rfl⟩ := hp
      simp only at hpx
      exact hne (by rw [hpx, hx])
    rw [hnone, Option.elim_none, hx]
  · have himp : ∀ a ∈ θ.normalize, (a.1 == x) = true → (!Subst.isTrivialBinding a) = true := by
      intro a ha hax
      simp only [beq_iff_eq] at hax
      apply Subst.not_isTrivial_iff.mpr
      simp only [Subst.normalize, List.mem_map] at ha
      obtain ⟨q, _, rfl⟩ := ha
      simp only at hax ⊢
      rwa [hax]
    have hcomm : (fun a : X × ntm F X 𝔸 =>
          decide (((!Subst.isTrivialBinding a) = true) ∧ ((a.1 == x) = true)))
        = (fun a : X × ntm F X 𝔸 => (a.1 == x) && (!Subst.isTrivialBinding a)) := by
      funext a
      cases hb : (!Subst.isTrivialBinding a) <;> cases hc : (a.1 == x) <;> simp [hb, hc]
    rw [hcomm, find?_and_of_imp himp, hn]

/-- `reduce θ` is in solved form whenever θ is idempotent (no `MovesDom` needed:
    the trivial self-bindings have been dropped). -/
lemma Subst.solvedForm_reduce (θ : Subst F X 𝔸) (hθ : θ.IsIdempotent) :
    Subst.SolvedForm θ.reduce := by
  intro p hp z hz
  rw [Subst.mem_reduce] at hp
  obtain ⟨hp_norm, _⟩ := hp
  simp only [Subst.normalize, List.mem_map] at hp_norm
  obtain ⟨q, _, rfl⟩ := hp_norm
  by_contra hocc
  simp only [Bool.not_eq_false] at hocc
  have hfix : ((ntm.mvar (F := F) [] q.1).subst θ).subst θ
      = (ntm.mvar (F := F) [] q.1).subst θ := ntm.subst_idempotent hθ _
  have hzfix : (ntm.mvar (F := F) [] z).subst θ = ntm.mvar [] z :=
    ntm.subst_fixed_of_occurs hfix hocc
  -- z ∈ dom (reduce θ) means z's binding is non-trivial: z.subst θ ≠ z.
  rw [Subst.dom, List.mem_toFinset, List.mem_map] at hz
  obtain ⟨p', hp'_mem, hp'1⟩ := hz
  rw [Subst.mem_reduce] at hp'_mem
  obtain ⟨hp'_norm, hp'_ne⟩ := hp'_mem
  simp only [Subst.normalize, List.mem_map] at hp'_norm
  obtain ⟨q', _, rfl⟩ := hp'_norm
  simp only at hp'1
  rw [hp'1] at hp'_ne
  exact hp'_ne hzfix

/-- Sequential substitution by θ equals simultaneous substitution by its
    reduction: `t.subst θ = t.substSim (reduce θ)` (from `lookupSim_reduce`;
    no hypothesis on θ). -/
lemma Subst.subst_eq_substSim_reduce (θ : Subst F X 𝔸) :
    ∀ t : ntm F X 𝔸, t.subst θ = t.substSim θ.reduce
  | .atm a => by simp [ntm.substSim, ntm.subst_atm]
  | .mvar π x => by rw [ntm.substSim, Subst.lookupSim_reduce, ntm.subst_mvar]
  | .fapp f ts => by
      rw [ntm.substSim, ntm.subst_fapp]
      congr 1
      exact List.map_congr_left (fun t _ => Subst.subst_eq_substSim_reduce θ t)
  | .abs a t => by rw [ntm.substSim, ntm.subst_abs, Subst.subst_eq_substSim_reduce θ t]

/-- On any idempotent θ, sequential substitution equals that of its (solved-form)
    reduction: `t.subst θ = t.subst (reduce θ)`. -/
lemma Subst.subst_eq_reduce (θ : Subst F X 𝔸) (hθ : θ.IsIdempotent)
    (t : ntm F X 𝔸) : t.subst θ = t.subst θ.reduce := by
  rw [Subst.subst_eq_substSim_reduce θ t,
      ← ntm.subst_eq_substSim_of_solved θ.reduce (Subst.solvedForm_reduce θ hθ) t]

/-- End-to-end explicit mediator: for `solve`'s output `(Γ, σ)` and *any*
    solution `(Δ, θ)`, the guessed mediator works.  The mediator is
    `σ' = (reduce θ) ∖ dom σ` — built from the solved-form reduction of θ, since
    a raw idempotent θ need not be in solved form.  It has domain disjoint from
    `dom σ` and factors θ through σ up to `≈α` (`Xσσ' ≈α Xθ`). -/
theorem UnifProblem.solve_mediator_explicit (Pr : UnifProblem F X 𝔸)
    (Γ : Context 𝔸 X) (σ : Subst F X 𝔸) (h : Pr.solve = some (Γ, σ))
    (Δ : Context 𝔸 X) (θ : Subst F X 𝔸) (hq : (Δ, θ) ∈ Pr.Solutions) :
    ∃ σ' : Subst F X 𝔸,
      (∀ z ∈ σ'.dom, z ∉ σ.dom) ∧
      (∀ x : X, (Δ ⊢ ((ntm.mvar (F := F) [] x).subst σ).subst σ'
                  ≈α (ntm.mvar (F := F) [] x).subst θ) = true) := by
  have hθ_idem : θ.IsIdempotent := hq.2
  have hσ_norm := UnifProblem.solve_normalize_solvedForm Pr Γ σ h
  have hθ_red := Subst.solvedForm_reduce θ hθ_idem
  have habs := UnifProblem.solve_absorbedBy Pr Γ σ h Δ θ hq
  -- Transport absorption to (normalize σ, reduce θ): both act as (σ, θ).
  have habs_red : Subst.absorbedBy Δ σ.normalize θ.reduce := by
    intro x
    rw [← UnifProblem.solve_subst_eq_normalize Pr Γ σ h,
        ← Subst.subst_eq_reduce θ hθ_idem,
        ← Subst.subst_eq_reduce θ hθ_idem]
    exact habs x
  obtain ⟨σ', hdisj, hmed⟩ := Subst.solvedForm_mediator hσ_norm hθ_red habs_red
  refine ⟨σ', ?_, ?_⟩
  · intro z hz
    have hz' := hdisj z hz
    rwa [Subst.dom_normalize] at hz'
  · intro x
    rw [UnifProblem.solve_subst_eq_normalize Pr Γ σ h, Subst.subst_eq_reduce θ hθ_idem]
    exact hmed x

end Nominal
