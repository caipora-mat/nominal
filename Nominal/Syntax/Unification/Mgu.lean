import Nominal.Syntax.Unification.Completeness

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


mutual
  lemma ntm.subst_fixed_of_occurs {σ : Subst F X 𝔸} {z : X} :
      ∀ {v : ntm F X 𝔸}, v.subst σ = v → v.occursIn z = true →
        (ntm.mvar (F := F) [] z).subst σ = ntm.mvar [] z
    | .atm _, _, hocc => by simp [ntm.occursIn] at hocc
    | .mvar π y, hfix, hocc => by
        simp only [ntm.occursIn, beq_iff_eq] at hocc
        subst hocc
        rw [ntm.subst_mvar] at hfix
        generalize hm : (ntm.mvar (F := F) [] z).subst σ = m at hfix ⊢
        cases m with
        | atm _ => simp [ntm.permute] at hfix
        | fapp _ _ => simp [ntm.permute] at hfix
        | abs _ _ => simp [ntm.permute] at hfix
        | mvar ρ x =>
            simp only [ntm.permute] at hfix
            injection hfix with hlist hx
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

def Subst.SolvedForm (σ : Subst F X 𝔸) : Prop :=
  ∀ p ∈ σ, ∀ z ∈ σ.dom, p.2.occursIn z = false

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

lemma ntm.subst_drop_dom {σ : Subst F X 𝔸} (θ : Subst F X 𝔸) :
    ∀ (u : ntm F X 𝔸),
      (∀ z ∈ σ.dom, z ∈ θ.dom → u.occursIn z = false) →
      u.subst (θ.filter (fun p => decide (p.1 ∉ σ.dom))) = u.subst θ
  | .atm _, _ => by simp [ntm.subst]
  | .mvar π y, hu => by
      have hbare : (ntm.mvar (F := F) [] y).subst (θ.filter (fun p => decide (p.1 ∉ σ.dom)))
          = (ntm.mvar (F := F) [] y).subst θ := by
        rw [ntm.subst_mvar_nil, ntm.subst_mvar_nil, Subst.lookup_filter_not_mem_dom]
        by_cases hy : y ∈ σ.dom
        · rw [if_pos hy]
          by_cases hyθ : y ∈ θ.dom
          · exact absurd (by simp [ntm.occursIn] : ntm.occursIn y (ntm.mvar (F := F) π y) = true)
              (by rw [hu y hy hyθ]; simp)
          · rw [(Subst.lookup_eq_none_iff_not_mem_dom θ y).mpr hyθ]
        · rw [if_neg hy]
      rw [ntm.subst_mvar, hbare, ← ntm.subst_mvar]
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

/-- The mediator `θ ∖ dom σ` has domain disjoint from `dom σ` by construction. -/
lemma Subst.filter_avoid_dom (σ θ : Subst F X 𝔸) :
    ∀ z ∈ Subst.dom (θ.filter (fun p => decide (p.1 ∉ σ.dom))), z ∉ σ.dom := by
  intro z hz
  simp only [Subst.dom, List.mem_toFinset, List.mem_map] at hz
  obtain ⟨p, hpf, hpz⟩ := hz
  rw [List.mem_filter] at hpf
  rw [← hpz]
  have h2 := hpf.2
  simp only [decide_eq_true_eq, Subst.dom, List.mem_toFinset, List.mem_map] at h2 ⊢
  exact h2

/-- The mediator `θ ∖ dom σ` factors an absorbed solution through `σ`:
    `(Xσ)(θ ∖ dom σ) ≈α Xθ` (solved `σ` fixes its image away from `dom σ`). -/
lemma Subst.absorbedBy_filter_clause1 {Δ : Context 𝔸 X} {σ θ : Subst F X 𝔸}
    (hσ : σ.SolvedForm) (habs : Subst.absorbedBy Δ σ θ) :
    ∀ x : X, (Δ ⊢ ((ntm.mvar (F := F) [] x).subst σ).subst
                  (θ.filter (fun p => decide (p.1 ∉ σ.dom)))
                ≈α (ntm.mvar (F := F) [] x).subst θ) = true := by
  intro x
  have hu : ∀ z ∈ σ.dom, z ∈ Subst.dom θ →
      ((ntm.mvar (F := F) [] x).subst σ).occursIn z = false :=
    fun z hz _ => ntm.subst_avoids_dom_of_solved σ hσ z hz _
  rw [ntm.subst_drop_dom θ ((ntm.mvar (F := F) [] x).subst σ) hu]
  exact habs x

theorem Subst.solvedForm_mediator {Δ : Context 𝔸 X} {σ θ : Subst F X 𝔸}
    (hσ : σ.SolvedForm) (habs : Subst.absorbedBy Δ σ θ) :
    ∃ σ' : Subst F X 𝔸,
      (∀ z ∈ σ'.dom, z ∉ σ.dom) ∧
      (∀ x : X, (Δ ⊢ ((ntm.mvar (F := F) [] x).subst σ).subst σ'
                  ≈α (ntm.mvar (F := F) [] x).subst θ) = true) :=
  ⟨θ.filter (fun p => decide (p.1 ∉ σ.dom)),
   Subst.filter_avoid_dom σ θ,
   Subst.absorbedBy_filter_clause1 hσ habs⟩

/-- Restricting `θ` to variables outside `dom σ` preserves entailment of a
    context whose recorded metavariables all avoid `dom σ`. -/
lemma Context.entailsUnder_filter_of_avoid {σ : Subst F X 𝔸}
    {Γ Δ : Context 𝔸 X} {θ : Subst F X 𝔸}
    (hvars : ∀ p ∈ Γ, p.2 ∉ σ.dom)
    (hΓ : Γ.EntailsUnder Δ θ = true) :
    Γ.EntailsUnder Δ (θ.filter (fun p => decide (p.1 ∉ σ.dom))) = true := by
  simp only [Context.EntailsUnder, decide_eq_true_eq] at hΓ ⊢
  intro p hp
  rw [ntm.subst_drop_dom θ (ntm.mvar (F := F) [] p.2) (by
    intro z hz _
    simp only [ntm.occursIn, beq_eq_false_iff_ne]
    rintro rfl
    exact (hvars p hp) hz)]
  exact hΓ p hp

/-- Under a solved `σ`, every metavariable recorded in the finalised context
    avoids `dom σ`: the residual freshness leaves from `simplifyFresh a (Xσ)`
    live outside `dom σ`, since `σ`'s image already avoids its own domain. -/
lemma finalizeDeferred_vars_avoid_dom (σ : Subst F X 𝔸) (hσ : σ.SolvedForm) :
    ∀ (ds : List (𝔸 × X)) (Γ_init Γ : Context 𝔸 X),
      finalizeDeferred ds σ Γ_init = some Γ →
      (∀ p ∈ Γ_init, p.2 ∉ σ.dom) →
      ∀ p ∈ Γ, p.2 ∉ σ.dom
  | [], Γ_init, Γ, h, hinit => by
      simp only [finalizeDeferred, Option.some.injEq] at h
      subst h; exact hinit
  | (a, x) :: tl, Γ_init, Γ, h, hinit => by
      simp only [finalizeDeferred] at h
      cases hsf : simplifyFresh a ((ntm.mvar (F := F) [] x).subst σ) with
      | none => rw [hsf] at h; cases h
      | some cs =>
        rw [hsf] at h
        have hleaf : ∀ a' x', Constraint.fresh a' (ntm.mvar (F := F) [] x') ∈ cs →
            x' ∉ σ.dom := by
          intro a' x' hc hx'dom
          have hmem : x' ∈ ((ntm.mvar (F := F) [] x).subst σ).metavars :=
            simplifyFresh_metavars_subset a _ cs hsf _ hc x'
              (by simp [Constraint.toUnif, UnifConstraint.metavars, ntm.metavars])
          have havoid := ntm.subst_avoids_dom_of_solved σ hσ x' hx'dom
            (ntm.mvar (F := F) [] x)
          exact ((ntm.occursIn_false_iff_not_mem_metavars x' _).mp havoid) hmem
        have hfold : ∀ (cs_pre : Problem F X 𝔸) (Γ₀ : Context 𝔸 X),
            (∀ p ∈ Γ₀, p.2 ∉ σ.dom) →
            (∀ a' x', Constraint.fresh a' (ntm.mvar (F := F) [] x') ∈ cs_pre →
              x' ∉ σ.dom) →
            ∀ p ∈ cs_pre.foldl ctxStep Γ₀, p.2 ∉ σ.dom := by
          intro cs_pre
          induction cs_pre with
          | nil => intro Γ₀ hΓ₀ _ p hp; exact hΓ₀ p hp
          | cons c0 cs_rest ih =>
            intro Γ₀ hΓ₀ hleaf' p hp
            simp only [List.foldl] at hp
            apply ih _ ?_ ?_ p hp
            · cases c0 with
              | fresh a' t' =>
                cases t' with
                | mvar π x' =>
                  cases π with
                  | nil =>
                    intro q hq
                    rcases Finset.mem_insert.mp hq with rfl | hq'
                    · exact hleaf' a' x' List.mem_cons_self
                    · exact hΓ₀ q hq'
                  | cons _ _ => intro q hq; exact hΓ₀ q hq
                | atm _ => intro q hq; exact hΓ₀ q hq
                | fapp _ _ => intro q hq; exact hΓ₀ q hq
                | abs _ _ => intro q hq; exact hΓ₀ q hq
              | alpha _ _ => intro q hq; exact hΓ₀ q hq
            · intro a'' x'' hmem
              exact hleaf' a'' x'' (List.mem_cons_of_mem _ hmem)
        exact finalizeDeferred_vars_avoid_dom σ hσ tl _ Γ h (hfold cs Γ_init hinit hleaf)


/-- `σ` moves every variable of its domain. -/
def Subst.MovesDom (σ : Subst F X 𝔸) : Prop :=
  ∀ z ∈ σ.dom, (ntm.mvar (F := F) [] z).subst σ ≠ ntm.mvar [] z

/-- Appending an occurs-check-passing, `σ`-fixed binding preserves `MovesDom`. -/
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

/-- A `σ`-fixed value avoids every variable `σ` moves. -/
lemma Subst.MovesDom.value_avoids_dom {σ : Subst F X 𝔸} {u : ntm F X 𝔸}
    (hmove : σ.MovesDom) (hu_fixed : u.subst σ = u) :
    ∀ z ∈ σ.dom, u.occursIn z = false := by
  intro z hz
  by_contra hocc
  simp only [Bool.not_eq_false] at hocc
  exact hmove z hz (ntm.subst_fixed_of_occurs hu_fixed hocc)

/-- `comp σ [(x, u)]` is in solved form under the algorithm's invariants
    (`σ` solved and moving its domain, `x ∉ dom σ`, `u` fixed by `σ` and
    passing occurs-check). -/
lemma Subst.SolvedForm.comp_singleton {σ : Subst F X 𝔸} {x : X} {u : ntm F X 𝔸}
    (hσ_solved : σ.SolvedForm) (hmove : σ.MovesDom) (hx : x ∉ σ.dom)
    (hu_fixed : u.subst σ = u) (hxu : u.occursIn x = false) :
    (σ.comp [(x, u)]).SolvedForm := by
  have hu_avoids : ∀ z ∈ Subst.dom (σ.comp [(x, u)]), u.occursIn z = false := by
    intro z hz
    rw [Subst.dom_comp, Subst.dom_singleton, Finset.mem_union, Finset.mem_singleton] at hz
    rcases hz with hz | rfl
    · exact hmove.value_avoids_dom hu_fixed z hz
    · exact hxu
  intro p hp z hz
  simp only [Subst.comp, List.mem_append, List.map, List.mem_map, List.mem_singleton] at hp
  rcases hp with ⟨q, hq, rfl⟩ | rfl
  · rw [ntm.subst_singleton]
    by_cases hzx : z = x
    · subst hzx; exact ntm.occursIn_applyOne_self q.2 z u hxu
    · have hsz : q.2.occursIn z = false := by
        rw [Subst.dom_comp, Subst.dom_singleton, Finset.mem_union,
            Finset.mem_singleton] at hz
        rcases hz with hz | rfl
        · exact hσ_solved q hq z hz
        · exact absurd rfl hzx
      exact ntm.occursIn_applyOne_of_ne hzx (hu_avoids z hz) hsz
  · exact hu_avoids z hz

/-- General form: composing two substitutions in solved form whose composition
    has disjoint domain and range yields a substitution in solved form.  The
    disjointness hypothesis `hdr` states `dom σ ∩ range τ = ∅`, i.e. no domain
    variable of `σ` occurs in any value of `τ`.  The single-binding case used by
    the loop, `SolvedForm.comp_singleton`, is the instance `τ = [(x, u)]`. -/
lemma Subst.SolvedForm.comp {σ τ : Subst F X 𝔸}
    (hσ : σ.SolvedForm) (hτ : τ.SolvedForm)
    (hdr : ∀ z ∈ σ.dom, ∀ p ∈ τ, p.2.occursIn z = false) :
    (σ.comp τ).SolvedForm := by
  intro p hp z hz
  rw [Subst.dom_comp, Finset.mem_union] at hz
  rw [Subst.comp, List.mem_append] at hp
  rcases hp with hpσ | hpτ
  · rw [List.mem_map] at hpσ
    obtain ⟨q, hqσ, rfl⟩ := hpσ
    rcases hz with hzσ | hzτ
    · exact ntm.occursIn_subst_of_avoid (fun r hr => hdr z hzσ r hr) (hσ q hqσ z hzσ)
    · exact ntm.subst_avoids_dom_of_solved τ hτ z hzτ q.2
  · rcases hz with hzσ | hzτ
    · exact hdr z hzσ p hpτ
    · exact hτ p hpτ z hzτ

/-- The three side-conditions on the new binding of an instantiation step:
    variable outside `dom σ`, value fixed by `σ`, occurs-check passing. -/
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

/-- Every `.next` step either leaves `σ` unchanged (non-instantiation steps)
    or appends a single binding satisfying the three side-conditions.
    Uniform classifier used to thread `MovesDom` and similar invariants. -/
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

/-- `unifStep` preserves `SolvedForm` under the full invariant. -/
lemma unifStep_next_solvedForm
    (c : UnifConstraint F X 𝔸) (rest : UnifProblem F X 𝔸) (σ : Subst F X 𝔸)
    (Pr' : UnifProblem F X 𝔸) (σ_next : Subst F X 𝔸)
    (h : unifStep c rest σ = .next Pr' σ_next)
    (hσ : σ.IsIdempotent) (hdisj : σ.disjointPr (c :: rest))
    (hmove : σ.MovesDom) (hsolved : σ.SolvedForm) : σ_next.SolvedForm := by
  rcases unifStep_next_binding_props c rest σ Pr' σ_next h hdisj with rfl | ⟨x, u, rfl, hx, hu, hxu⟩
  · exact hsolved
  · exact hsolved.comp_singleton hmove hx hu hxu

/-- `unify` preserves `SolvedForm`, threading the full invariant. -/
theorem unify_preserves_solvedForm :
    ∀ (Pr : UnifProblem F X 𝔸) (σ : Subst F X 𝔸) (ds : List (𝔸 × X))
      (ds' : List (𝔸 × X)) (σ' : Subst F X 𝔸),
      unify Pr σ ds = some (ds', σ') →
      σ.IsIdempotent → σ.disjointPr Pr → σ.MovesDom → σ.SolvedForm → σ'.SolvedForm := by
  intro Pr σ ds
  induction Pr, σ, ds using unify.induct with
  | case1 σ ds =>
      intro ds' σ' h _ _ _ hsolved
      simp only [unify, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨_, rfl⟩ := h; exact hsolved
  | case2 σ ds c rest hfail =>
      intro ds' σ' h _ _ _ _
      rw [unify, hfail] at h; cases h
  | case3 σ ds c rest a x hctx ih =>
      intro ds' σ' h hσ hdisj hmove hsolved
      rw [unify, hctx] at h
      exact ih ds' σ' h hσ (Subst.disjointPr_cons hdisj) hmove hsolved
  | case4 σ ds c rest Pr' σ_next hnext ih =>
      intro ds' σ' h hσ hdisj hmove hsolved
      rw [unify, hnext] at h
      obtain ⟨hσ_next, hdisj_next⟩ :=
        unifStep_next_idempotent_and_disjoint c rest σ Pr' σ_next hnext hσ hdisj
      exact ih ds' σ' h hσ_next hdisj_next
        (unifStep_next_movesDom c rest σ Pr' σ_next hnext hσ hdisj hmove)
        (unifStep_next_solvedForm c rest σ Pr' σ_next hnext hσ hdisj hmove hsolved)

/-- The substitution produced by `solve` is in solved form (idempotent,
    `dom ∩ range = ∅`) — the mediator applies to `σ` directly, without
    normalisation. -/
theorem UnifProblem.solve_solvedForm (Pr : UnifProblem F X 𝔸) (Γ : Context 𝔸 X)
    (σ : Subst F X 𝔸) (h : Pr.solve = some (Γ, σ)) : σ.SolvedForm := by
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
      have hsolved_empty : Subst.SolvedForm ([] : Subst F X 𝔸) := by
        intro p hp; simp at hp
      exact unify_preserves_solvedForm Pr [] [] ds σ_u hu hσ_empty hdisj_empty
        hmove_empty hsolved_empty


/-- `Subst.lookup` (recursive) agrees with `Subst.lookupSim` (`find?`-based). -/
lemma Subst.lookup_getD_eq_lookupSim (ρ : Subst F X 𝔸) (x : X) :
    (Subst.lookup ρ x).getD (ntm.mvar [] x) = ρ.lookupSim x := by
  unfold Subst.lookupSim
  induction ρ with
  | nil => simp [Subst.lookup]
  | cons p ρ₀ ih =>
      obtain ⟨y, s⟩ := p
      rw [Subst.lookup_cons, List.find?_cons]
      by_cases hxy : x = y
      · subst hxy; simp
      · have hyx : (y == x) = false := by
          simp only [beq_eq_false_iff_ne]; exact fun h => hxy h.symm
        rw [if_neg hxy, hyx, ih]

/-- Every solution `(Δ, θ)` is absorbed by the algorithm's output `σ`.
    Isolated from `solve_principal` so the explicit mediator can be assembled. -/
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
      · simp only [hp, Bool.false_and]
        exact find?_and_of_imp (fun a' ha' => h a' (by simp [ha']))

/-- A binding is *trivial* when it maps its variable to itself (`x ↦ x`). -/
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

/-- The reduction of `σ`: simultaneous normalisation with trivial
    self-bindings removed. -/
def Subst.reduce (σ : Subst F X 𝔸) : Subst F X 𝔸 :=
  σ.normalize.filter (fun p => !Subst.isTrivialBinding p)

/-- The reduction looks up each variable to its full image `x.subst θ`. -/
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
      cases hb : (!Subst.isTrivialBinding a) <;> cases hc : (a.1 == x) <;> simp
    rw [hcomm, find?_and_of_imp himp, hn]

/-- `t.subst θ = t.subst θ.reduce` (both simultaneous; no hypothesis on θ). -/
lemma Subst.subst_eq_reduce (θ : Subst F X 𝔸) :
    ∀ t : ntm F X 𝔸, t.subst θ = t.subst θ.reduce
  | .atm a => by simp [ntm.subst_atm]
  | .mvar π y => by
      conv_rhs => rw [ntm.subst_mvar, ntm.subst_mvar_nil, Subst.lookup_getD_eq_lookupSim,
                      Subst.lookupSim_reduce, ← ntm.subst_mvar]
  | .fapp f ts => by
      rw [ntm.subst_fapp, ntm.subst_fapp]
      congr 1
      exact List.map_congr_left (fun t _ => Subst.subst_eq_reduce θ t)
  | .abs a t => by rw [ntm.subst_abs, ntm.subst_abs, Subst.subst_eq_reduce θ t]

theorem UnifProblem.solve_factors_comp (Pr : UnifProblem F X 𝔸)
    (Γ : Context 𝔸 X) (σ : Subst F X 𝔸) (h : Pr.solve = some (Γ, σ))
    (Δ : Context 𝔸 X) (θ : Subst F X 𝔸) (hq : (Δ, θ) ∈ Pr.Solutions) :
    ∃ σ' : Subst F X 𝔸,
      (∀ z ∈ σ'.dom, z ∉ σ.dom) ∧
      (∀ x : X, (Δ ⊢ (ntm.mvar (F := F) [] x).subst (σ.comp σ')
                  ≈α (ntm.mvar (F := F) [] x).subst θ) = true) := by
  have hσ_solved := UnifProblem.solve_solvedForm Pr Γ σ h
  have habs := UnifProblem.solve_absorbedBy Pr Γ σ h Δ θ hq
  have habs_red : Subst.absorbedBy Δ σ θ.reduce := by
    intro x
    rw [← Subst.subst_eq_reduce θ, ← Subst.subst_eq_reduce θ]
    exact habs x
  obtain ⟨σ', hdisj, hmed⟩ := Subst.solvedForm_mediator hσ_solved habs_red
  refine ⟨σ', hdisj, fun x => ?_⟩
  rw [ntm.subst_mvar_nil_comp, Subst.subst_eq_reduce θ]
  exact hmed x

theorem Subst.absorbedBy_of_factors {Δ : Context 𝔸 X} {σ θ : Subst F X 𝔸}
    (σ' : Subst F X 𝔸) (hidem : σ.IsIdempotent)
    (hfact : ∀ x : X, (Δ ⊢ (ntm.mvar (F := F) [] x).subst (σ.comp σ')
                        ≈α (ntm.mvar (F := F) [] x).subst θ) = true) :
    Subst.absorbedBy Δ σ θ := by
  intro x
  have hcongr := ntm.alphaEquiv_subst_pointwise Δ (σ.comp σ') θ hfact
    ((ntm.mvar (F := F) [] x).subst σ)
  rw [ntm.subst_comp, ntm.subst_idempotent hidem] at hcongr
  have hf := hfact x
  rw [ntm.subst_mvar_nil_comp] at hf
  exact alphaEquiv_trans Δ _ _ _ (alphaEquiv_symm Δ _ _ hcongr) hf

theorem Subst.absorbedBy_iff_factors {Δ : Context 𝔸 X} {σ θ : Subst F X 𝔸}
    (hidem : σ.IsIdempotent) :
    Subst.absorbedBy Δ σ θ ↔
      ∃ σ' : Subst F X 𝔸, ∀ x : X,
        (Δ ⊢ (ntm.mvar (F := F) [] x).subst (σ.comp σ')
           ≈α (ntm.mvar (F := F) [] x).subst θ) = true := by
  constructor
  · intro habs
    refine ⟨θ, fun x => ?_⟩
    rw [ntm.subst_mvar_nil_comp]
    exact habs x
  · rintro ⟨σ', hfact⟩
    exact Subst.absorbedBy_of_factors σ' hidem hfact

/-- A solved-form substitution is idempotent. -/
lemma Subst.SolvedForm.isIdempotent {σ : Subst F X 𝔸} (hσ : σ.SolvedForm) :
    σ.IsIdempotent := fun x =>
  (ntm.subst_of_disjoint_dom ((ntm.mvar (F := F) [] x).subst σ) σ
    (fun z hz => ntm.subst_avoids_dom_of_solved σ hσ z hz _)).symm

theorem Subst.absorbedBy_iff_factors_indep {Δ : Context 𝔸 X} {σ θ : Subst F X 𝔸}
    (hσ : σ.SolvedForm) :
    Subst.absorbedBy Δ σ θ ↔
      ∃ σ' : Subst F X 𝔸, (∀ z ∈ σ'.dom, z ∉ σ.dom) ∧
        ∀ x : X, (Δ ⊢ (ntm.mvar (F := F) [] x).subst (σ.comp σ')
                    ≈α (ntm.mvar (F := F) [] x).subst θ) = true := by
  constructor
  · intro habs
    obtain ⟨σ', hdisj, hmed⟩ := Subst.solvedForm_mediator hσ habs
    exact ⟨σ', hdisj, fun x => by rw [ntm.subst_mvar_nil_comp]; exact hmed x⟩
  · rintro ⟨σ', _, hfact⟩
    exact Subst.absorbedBy_of_factors σ' hσ.isIdempotent hfact

/-- The finalised context `Γ` is entailed by every solution `(Δ, θ)` under `θ`
    itself (the `SolutionLe` context clause with the trivial mediator). -/
theorem UnifProblem.solve_entailsUnder (Pr : UnifProblem F X 𝔸) (Γ : Context 𝔸 X)
    (σ : Subst F X 𝔸) (h : Pr.solve = some (Γ, σ)) (Δ : Context 𝔸 X)
    (θ : Subst F X 𝔸) (hq : (Δ, θ) ∈ Pr.Solutions) : Γ.EntailsUnder Δ θ = true := by
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
      obtain ⟨hΓeq, hσeq⟩ := h
      subst hΓeq; subst hσeq
      have habs0 : Subst.absorbedBy Δ ([] : Subst F X 𝔸) θ := Subst.absorbedBy_nil Δ θ
      have hds0 : ∀ p ∈ ([] : List (𝔸 × X)),
          (Δ ⊢ p.1 # (ntm.mvar (F := F) [] p.2).subst θ) = true := by
        intros _ hp; cases hp
      obtain ⟨habs_u, hds_u⟩ := unify_le Pr [] [] ds σ_u Δ θ hu hq habs0 hds0
      have hinit_empty : (∅ : Context 𝔸 X).EntailsUnder Δ θ = true := by
        simp [Context.EntailsUnder]
      exact finalizeDeferred_le ds σ_u ∅ Γ_fin Δ θ hf habs_u hds_u hinit_empty

/-- Every metavariable recorded in the algorithm's output context `Γ` avoids
    `dom σ` — `σ` being solved, its residual freshness leaves lie outside it. -/
theorem UnifProblem.solve_ctxVars_avoid_dom (Pr : UnifProblem F X 𝔸)
    (Γ : Context 𝔸 X) (σ : Subst F X 𝔸) (h : Pr.solve = some (Γ, σ)) :
    ∀ p ∈ Γ, p.2 ∉ σ.dom := by
  have hσ := UnifProblem.solve_solvedForm Pr Γ σ h
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
      obtain ⟨hΓeq, hσeq⟩ := h
      subst hΓeq; subst hσeq
      exact finalizeDeferred_vars_avoid_dom σ_u hσ ds ∅ Γ_fin hf (by intro p hp; simp at hp)

/-- Independent-mediator form of principality's `≤` (Def. 28): the output
    `(Γ, σ)` sits below any solution `(Δ, θ)` via a mediator disjoint from
    `dom σ` satisfying both `SolutionLe` clauses. Strengthens `solve_principal`
    (trivial mediator `σ' = θ`). -/
theorem UnifProblem.solve_le_indep (Pr : UnifProblem F X 𝔸)
    (Γ : Context 𝔸 X) (σ : Subst F X 𝔸) (h : Pr.solve = some (Γ, σ))
    (Δ : Context 𝔸 X) (θ : Subst F X 𝔸) (hq : (Δ, θ) ∈ Pr.Solutions) :
    ∃ σ' : Subst F X 𝔸,
      (∀ z ∈ σ'.dom, z ∉ σ.dom) ∧
      (∀ x : X, (Δ ⊢ ((ntm.mvar (F := F) [] x).subst σ).subst σ'
                  ≈α (ntm.mvar (F := F) [] x).subst θ) = true) ∧
      Γ.EntailsUnder Δ σ' = true := by
  have hσ_solved := UnifProblem.solve_solvedForm Pr Γ σ h
  have habs := UnifProblem.solve_absorbedBy Pr Γ σ h Δ θ hq
  have hΓθ := UnifProblem.solve_entailsUnder Pr Γ σ h Δ θ hq
  have hvars := UnifProblem.solve_ctxVars_avoid_dom Pr Γ σ h
  exact ⟨θ.filter (fun p => decide (p.1 ∉ σ.dom)),
    Subst.filter_avoid_dom σ θ,
    Subst.absorbedBy_filter_clause1 hσ_solved habs,
    Context.entailsUnder_filter_of_avoid hvars hΓθ⟩

end Nominal
