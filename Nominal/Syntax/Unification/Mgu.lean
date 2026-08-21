import Nominal.Syntax.Unification.Completeness

namespace Nominal

open Core

variable {F X 𝔸 : Type*} [DecidableEq F] [DecidableEq X] [Name 𝔸]

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
-- avoid, if the term already avoids `w`.  Induction on `σ`.
lemma ntm.occursIn_subst_of_avoid {w : X} :
    ∀ (σ : Subst F X 𝔸), (∀ p ∈ σ, p.2.occursIn w = false) →
    ∀ {v : ntm F X 𝔸}, v.occursIn w = false → (v.subst σ).occursIn w = false
  | [], _, v, hv => by simpa using hv
  | (y, s) :: σ₀, hσ, v, hv => by
      rw [ntm.subst_cons]
      have hs : s.occursIn w = false := hσ (y, s) (by simp)
      have hv' : (v.applyOne y s).occursIn w = false := by
        by_cases hwy : w = y
        · subst hwy; exact ntm.occursIn_applyOne_self v w s hs
        · exact ntm.occursIn_applyOne_of_ne hwy hs hv
      exact ntm.occursIn_subst_of_avoid σ₀
        (fun p hp => hσ p (List.mem_cons_of_mem _ hp)) hv'

-- For a solved-form `σ`, the result `t.subst σ` avoids every variable of
-- `dom σ`: the domain variable is either removed (occurs-check on its binding)
-- or was never there, and no value reintroduces it (solved form).  Induction on
-- `σ`.
lemma ntm.subst_avoids_dom_of_solved :
    ∀ (σ : Subst F X 𝔸), σ.SolvedForm →
    ∀ (t : ntm F X 𝔸) (z : X), z ∈ σ.dom → (t.subst σ).occursIn z = false
  | [], _, t, z, hz => by simp [Subst.dom_nil] at hz
  | (x, s) :: σ₀, hσ, t, z, hz => by
      rw [ntm.subst_cons]
      rw [Subst.dom_cons] at hz
      have hval : ∀ p ∈ (x, s) :: σ₀, p.2.occursIn z = false :=
        fun p hp => hσ p hp z (by rw [Subst.dom_cons]; exact hz)
      rcases Finset.mem_insert.mp hz with hzx | hz₀
      · subst hzx
        exact ntm.occursIn_subst_of_avoid σ₀
          (fun p hp => hval p (List.mem_cons_of_mem _ hp))
          (ntm.occursIn_applyOne_self t z s (hval (z, s) (by simp)))
      · have hσ₀ : Subst.SolvedForm σ₀ := fun p hp w hw =>
          hσ p (List.mem_cons_of_mem _ hp) w
            (by rw [Subst.dom_cons]; exact Finset.mem_insert_of_mem hw)
        exact ntm.subst_avoids_dom_of_solved σ₀ hσ₀ (t.applyOne x s) z hz₀

-- Drop lemma: a binding of `θ` whose variable lies in `dom σ` is redundant when
-- acting on a term `u` free of the shared variables `dom σ ∩ dom θ`, provided no
-- `θ`-value reintroduces such a variable.  So filtering out the `dom σ` bindings
-- does not change the action of `θ` on `u`.  Only the *shared* variables matter,
-- since a `dom σ` variable not bound by `θ` is untouched by both.  Induction on `θ`.
lemma ntm.subst_drop_dom {σ : Subst F X 𝔸} :
    ∀ (θ : Subst F X 𝔸) (u : ntm F X 𝔸),
      (∀ z ∈ σ.dom, z ∈ θ.dom → u.occursIn z = false) →
      (∀ p ∈ θ, ∀ z ∈ σ.dom, z ∈ θ.dom → p.2.occursIn z = false) →
      u.subst (θ.filter (fun p => decide (p.1 ∉ σ.dom))) = u.subst θ
  | [], u, _, _ => by simp
  | (Y, s) :: θ₀, u, hu, hrange => by
      have hθmem : Y ∈ Subst.dom ((Y, s) :: θ₀) := by
        rw [Subst.dom_cons]; exact Finset.mem_insert_self _ _
      have hsub : ∀ z, z ∈ Subst.dom θ₀ → z ∈ Subst.dom ((Y, s) :: θ₀) :=
        fun z hz => by rw [Subst.dom_cons]; exact Finset.mem_insert_of_mem hz
      have hu₀ : ∀ z ∈ σ.dom, z ∈ Subst.dom θ₀ → u.occursIn z = false :=
        fun z hz hzθ => hu z hz (hsub z hzθ)
      have hrange₀ : ∀ p ∈ θ₀, ∀ z ∈ σ.dom, z ∈ Subst.dom θ₀ → p.2.occursIn z = false :=
        fun p hp z hz hzθ => hrange p (List.mem_cons_of_mem _ hp) z hz (hsub z hzθ)
      by_cases hY : Y ∈ σ.dom
      · -- Dropped binding: `u.applyOne Y s = u` since `u` avoids `Y`.
        simp only [List.filter_cons, hY, not_true, decide_false, Bool.false_eq_true,
                   if_false]
        rw [ntm.subst_drop_dom θ₀ u hu₀ hrange₀, ntm.subst_cons,
            ntm.applyOne_of_not_occursIn u Y s (hu Y hY hθmem)]
      · -- Kept binding: recurse on `u.applyOne Y s`.
        have hzY : ∀ z ∈ σ.dom, z ≠ Y := fun z hz h => hY (h ▸ hz)
        simp only [List.filter_cons, decide_eq_true_eq, hY, not_false_iff, if_pos,
                   ntm.subst_cons]
        apply ntm.subst_drop_dom θ₀ (u.applyOne Y s)
        · intro z hz hzθ
          exact ntm.occursIn_applyOne_of_ne (hzY z hz)
            (hrange (Y, s) (by simp) z hz (hsub z hzθ)) (hu z hz (hsub z hzθ))
        · exact hrange₀

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
      fun z hz _ => ntm.subst_avoids_dom_of_solved σ hσ _ z hz
    have hrange : ∀ p ∈ θ, ∀ z ∈ σ.dom, z ∈ Subst.dom θ → p.2.occursIn z = false :=
      fun p hp z _ hzθ => hθ p hp z hzθ
    rw [ntm.subst_drop_dom θ ((ntm.mvar (F := F) [] x).subst σ) hu hrange]
    exact habs x

end Nominal
