import Nominal.Syntax.Substitution.Properties

namespace Nominal

open Core

variable {F X 𝔸 : Type*} [DecidableEq F] [DecidableEq X] [Name 𝔸]

mutual
  /-- `x` occurs in `t`. -/
  def ntm.occursIn (x : X) : ntm F X 𝔸 → Bool
    | .atm _     => false
    | .mvar _ y  => x == y
    | .fapp _ ts => ntmList.occursIn x ts
    | .abs _ t   => t.occursIn x

  def ntmList.occursIn (x : X) : List (ntm F X 𝔸) → Bool
    | []      => false
    | t :: ts => t.occursIn x || ntmList.occursIn x ts
end


mutual
  lemma ntm.occursIn_permute (t : ntm F X 𝔸) (π : LPerm 𝔸) (x : X) :
      (t.permute π).occursIn x = t.occursIn x := by
    match t with
    | .atm _ => simp [ntm.permute, ntm.occursIn]
    | .mvar _ _ => simp [ntm.permute, ntm.occursIn]
    | .fapp _ ts =>
      simp only [ntm.permute, ntm.occursIn]
      exact ntmList.occursIn_permute ts π x
    | .abs _ t' =>
      simp only [ntm.permute, ntm.occursIn]
      exact ntm.occursIn_permute t' π x

  lemma ntmList.occursIn_permute (ts : List (ntm F X 𝔸)) (π : LPerm 𝔸) (x : X) :
      ntmList.occursIn x (ts.map (·.permute π)) = ntmList.occursIn x ts := by
    match ts with
    | [] => rfl
    | t :: ts' =>
      simp only [List.map_cons, ntmList.occursIn]
      rw [ntm.occursIn_permute t π x, ntmList.occursIn_permute ts' π x]
end


mutual
  /-- `applyOne x s` is a no-op when `x` does not occur in `t`. -/
  lemma ntm.applyOne_of_not_occursIn (t : ntm F X 𝔸) (x : X) (s : ntm F X 𝔸)
      (h : t.occursIn x = false) : t.applyOne x s = t := by
    match t with
    | .atm _ => simp [ntm.applyOne]
    | .mvar π y =>
      simp only [ntm.applyOne]
      split_ifs with hxy
      · subst hxy; simp [ntm.occursIn] at h
      · rfl
    | .fapp f ts =>
      simp only [ntm.occursIn] at h
      simp only [ntm.applyOne]
      congr 1
      exact ntmList.applyOne_of_not_occursIn ts x s h
    | .abs a t' =>
      simp only [ntm.occursIn] at h
      simp only [ntm.applyOne, ntm.applyOne_of_not_occursIn t' x s h]

  lemma ntmList.applyOne_of_not_occursIn (ts : List (ntm F X 𝔸)) (x : X) (s : ntm F X 𝔸)
      (h : ntmList.occursIn x ts = false) :
      ts.map (·.applyOne x s) = ts := by
    match ts with
    | [] => rfl
    | t :: ts' =>
      simp only [ntmList.occursIn, Bool.or_eq_false_iff] at h
      simp only [List.map_cons]
      rw [ntm.applyOne_of_not_occursIn t x s h.1,
          ntmList.applyOne_of_not_occursIn ts' x s h.2]
end

mutual
lemma ntm.subst_of_disjoint_dom : ∀ (t : ntm F X 𝔸) (σ : Subst F X 𝔸),
    (∀ x ∈ Subst.dom σ, t.occursIn x = false) → t.subst σ = t
  | .atm a, σ, _ => by simp
  | .mvar π x, σ, h => by
      rw [ntm.subst_mvar]
      have hx : x ∉ Subst.dom σ := by
        intro hmem
        have hocc := h x hmem
        simp [ntm.occursIn] at hocc
      rw [ntm.subst_mvar_nil, (Subst.lookup_eq_none_iff_not_mem_dom σ x).mpr hx]
      simp [ntm.permute]
  | .fapp f ts, σ, h => by
      rw [ntm.subst_fapp, ntmList.substList_of_disjoint_dom ts σ
        (fun x hx => by have := h x hx; simpa only [ntm.occursIn] using this)]
  | .abs a t, σ, h => by
      rw [ntm.subst_abs, ntm.subst_of_disjoint_dom t σ
        (fun x hx => by have := h x hx; simpa only [ntm.occursIn] using this)]

lemma ntmList.substList_of_disjoint_dom : ∀ (ts : List (ntm F X 𝔸)) (σ : Subst F X 𝔸),
    (∀ x ∈ Subst.dom σ, ntmList.occursIn x ts = false) → ts.map (·.subst σ) = ts
  | [], _, _ => rfl
  | t :: ts', σ, h => by
      simp only [List.map_cons]
      rw [ntm.subst_of_disjoint_dom t σ (fun x hx => by
            have := h x hx; simp only [ntmList.occursIn, Bool.or_eq_false_iff] at this
            exact this.1),
          ntmList.substList_of_disjoint_dom ts' σ (fun x hx => by
            have := h x hx; simp only [ntmList.occursIn, Bool.or_eq_false_iff] at this
            exact this.2)]
end

/-- If `x` doesn't occur in `u`, the singleton substitution `[(x, u)]` is idempotent. -/
lemma Subst.IsIdempotent.singleton_of_not_occursIn {x : X} {u : ntm F X 𝔸}
    (h : u.occursIn x = false) :
    Subst.IsIdempotent ([(x, u)] : Subst F X 𝔸) := by
  intro y
  by_cases hxy : y = x
  · subst hxy
    have h1 : (ntm.mvar (F := F) [] y).subst [(y, u)] = u := by
      rw [ntm.subst_mvar_nil]; simp [Subst.lookup_cons]
    rw [h1, ntm.subst_of_disjoint_dom u [(y, u)] (fun z hz => by
      simp only [Subst.dom_singleton, Finset.mem_singleton] at hz
      subst hz; exact h)]
  · have h1 : (ntm.mvar (F := F) [] y).subst [(x, u)] = ntm.mvar [] y := by
      rw [ntm.subst_mvar_nil]; simp [Subst.lookup_cons, if_neg hxy]
    rw [h1, h1]

/-- Corollary: if `x ∉ Subst.dom σ`, then `σ` fixes the bare metavariable `(mvar [] x)`. -/
lemma ntm.subst_mvar_nil_of_not_mem_dom {x : X} {σ : Subst F X 𝔸}
    (h : x ∉ Subst.dom σ) :
    (ntm.mvar (F := F) [] x).subst σ = ntm.mvar [] x := by
  apply ntm.subst_of_disjoint_dom
  intro z hz
  simp only [ntm.occursIn]
  by_contra hzx
  simp only [ne_eq, Bool.not_eq_false, beq_iff_eq] at hzx
  subst hzx
  exact h hz


mutual
  /-- `applyOne x u` commutes with `subst σ` when `x` is fresh for `σ`
      (out of `dom`, out of range) and `u` is `σ`-fixed. -/
  lemma ntm.applyOne_subst_comm (t : ntm F X 𝔸) (x : X) (u : ntm F X 𝔸) (σ : Subst F X 𝔸)
      (hx_dom : x ∉ Subst.dom σ)
      (hu_fixed : u.subst σ = u)
      (hx_img : ∀ y, ((ntm.mvar (F := F) [] y).subst σ).occursIn x = false) :
      (t.applyOne x u).subst σ = (t.subst σ).applyOne x u := by
    match t with
    | .atm a => simp [ntm.applyOne]
    | .mvar π z =>
      by_cases hz : z = x
      · obtain rfl := hz.symm
        have hap : (ntm.mvar π x : ntm F X 𝔸).applyOne x u = u.permute π := by
          simp [ntm.applyOne]
        have h1 : ((ntm.mvar π x : ntm F X 𝔸).applyOne x u).subst σ = u.permute π := by
          rw [hap, ntm.subst_permute, hu_fixed]
        have h2 : ((ntm.mvar π x : ntm F X 𝔸).subst σ).applyOne x u = u.permute π := by
          rw [ntm.subst_mvar, ntm.subst_mvar_nil_of_not_mem_dom hx_dom]
          simp [ntm.permute, ntm.applyOne]
        rw [h1, h2]
      · simp only [ntm.applyOne, if_neg hz]
        have hocc : ((ntm.mvar π z : ntm F X 𝔸).subst σ).occursIn x = false := by
          rw [ntm.subst_mvar, ntm.occursIn_permute]
          exact hx_img z
        rw [ntm.applyOne_of_not_occursIn _ x u hocc]
    | .fapp f ts =>
      simp only [ntm.applyOne, ntm.subst_fapp]
      congr 1
      exact ntmList.applyOne_subst_comm ts x u σ hx_dom hu_fixed hx_img
    | .abs a t' =>
      simp only [ntm.applyOne, ntm.subst_abs]
      rw [ntm.applyOne_subst_comm t' x u σ hx_dom hu_fixed hx_img]

  lemma ntmList.applyOne_subst_comm (ts : List (ntm F X 𝔸)) (x : X) (u : ntm F X 𝔸)
      (σ : Subst F X 𝔸)
      (hx_dom : x ∉ Subst.dom σ)
      (hu_fixed : u.subst σ = u)
      (hx_img : ∀ y, ((ntm.mvar (F := F) [] y).subst σ).occursIn x = false) :
      (ts.map (·.applyOne x u)).map (·.subst σ) =
      (ts.map (·.subst σ)).map (·.applyOne x u) := by
    match ts with
    | [] => rfl
    | t :: ts' =>
      simp only [List.map_cons]
      rw [ntm.applyOne_subst_comm t x u σ hx_dom hu_fixed hx_img,
          ntmList.applyOne_subst_comm ts' x u σ hx_dom hu_fixed hx_img]
end


mutual
  lemma ntm.occursIn_applyOne_self (t : ntm F X 𝔸) (x : X) (u : ntm F X 𝔸)
      (hu : u.occursIn x = false) :
      (t.applyOne x u).occursIn x = false := by
    match t with
    | .atm _ => simp [ntm.applyOne, ntm.occursIn]
    | .mvar π z =>
      by_cases hz : z = x
      · obtain rfl := hz.symm
        simp [ntm.applyOne, ntm.occursIn_permute, hu]
      · simp only [ntm.applyOne, if_neg hz, ntm.occursIn, beq_eq_false_iff_ne]
        exact fun heq => hz heq.symm
    | .fapp _ ts =>
      simp only [ntm.applyOne, ntm.occursIn]
      exact ntmList.occursIn_applyOne_self ts x u hu
    | .abs _ t' =>
      simp only [ntm.applyOne, ntm.occursIn]
      exact ntm.occursIn_applyOne_self t' x u hu

  lemma ntmList.occursIn_applyOne_self (ts : List (ntm F X 𝔸)) (x : X) (u : ntm F X 𝔸)
      (hu : u.occursIn x = false) :
      ntmList.occursIn x (ts.map (·.applyOne x u)) = false := by
    match ts with
    | [] => rfl
    | t :: ts' =>
      simp only [List.map_cons, ntmList.occursIn]
      rw [ntm.occursIn_applyOne_self t x u hu,
          ntmList.occursIn_applyOne_self ts' x u hu]
      rfl
end


mutual
  /-- `(t.applyOne x u).subst σ = t.applyOne x u` when both `t` and `u` are
      `σ`-fixed.  No hypothesis on `x` vs. `σ`. -/
  lemma ntm.applyOne_subst_of_stable (t : ntm F X 𝔸) (x : X) (u : ntm F X 𝔸)
      (σ : Subst F X 𝔸) (ht : t.subst σ = t) (hu : u.subst σ = u) :
      (t.applyOne x u).subst σ = t.applyOne x u := by
    match t with
    | .atm b => simp [ntm.applyOne]
    | .mvar π y =>
      simp only [ntm.applyOne]
      by_cases hy : y = x
      · rw [if_pos hy, ntm.subst_permute, hu]
      · rw [if_neg hy]; exact ht
    | .fapp f ts =>
      simp only [ntm.applyOne, ntm.subst_fapp]
      have hts : ts.map (·.subst σ) = ts := by
        have htmp := ht
        simp [ntm.subst_fapp] at htmp
        exact htmp
      congr 1
      exact ntmList.applyOne_subst_of_stable ts x u σ hts hu
    | .abs b t' =>
      simp only [ntm.applyOne, ntm.subst_abs]
      have ht' : t'.subst σ = t' := by
        have htmp := ht
        simp [ntm.subst_abs] at htmp
        exact htmp
      congr 1
      exact ntm.applyOne_subst_of_stable t' x u σ ht' hu

  lemma ntmList.applyOne_subst_of_stable (ts : List (ntm F X 𝔸)) (x : X) (u : ntm F X 𝔸)
      (σ : Subst F X 𝔸) (hts : ts.map (·.subst σ) = ts) (hu : u.subst σ = u) :
      (ts.map (·.applyOne x u)).map (·.subst σ) = ts.map (·.applyOne x u) := by
    match ts with
    | [] => rfl
    | t :: ts' =>
      simp only [List.map_cons] at hts
      injection hts with ht hts'
      simp only [List.map_cons]
      rw [ntm.applyOne_subst_of_stable t x u σ ht hu,
          ntmList.applyOne_subst_of_stable ts' x u σ hts' hu]
end

lemma ntm.subst_singleton : ∀ (t : ntm F X 𝔸) (x : X) (u : ntm F X 𝔸),
    t.subst [(x, u)] = t.applyOne x u
  | .atm a, x, u => by simp [ntm.applyOne]
  | .mvar π z, x, u => by
      rw [ntm.subst_mvar]
      simp only [ntm.applyOne]
      by_cases hz : z = x
      · subst hz; rw [ntm.subst_mvar_nil]; simp [Subst.lookup_cons]
      · rw [if_neg hz, ntm.subst_mvar_nil]
        simp [Subst.lookup_cons, if_neg hz, ntm.permute]
  | .fapp f ts, x, u => by
      rw [ntm.subst_fapp]; simp only [ntm.applyOne]
      congr 1; exact List.map_congr_left (fun t _ => ntm.subst_singleton t x u)
  | .abs a t, x, u => by
      rw [ntm.subst_abs]; simp only [ntm.applyOne]
      rw [ntm.subst_singleton t x u]


/-- `σ.comp [(x, u)]` is idempotent when `σ` is idempotent, `u` is `σ`-fixed,
    and `x ∉ u`. -/
lemma Subst.IsIdempotent.comp_singleton {σ : Subst F X 𝔸} {x : X} {u : ntm F X 𝔸}
    (hσ : σ.IsIdempotent)
    (hu_fixed : u.subst σ = u)
    (hxu : u.occursIn x = false) :
    Subst.IsIdempotent (σ.comp [(x, u)]) := by
  intro y
  set r := (ntm.mvar (F := F) [] y).subst σ with hr
  have hr_stable : r.subst σ = r := hr ▸ ntm.subst_idempotent hσ _
  have hStep1 : (r.applyOne x u).subst σ = r.applyOne x u :=
    ntm.applyOne_subst_of_stable r x u σ hr_stable hu_fixed
  have hA : (ntm.mvar (F := F) [] y).subst (σ.comp [(x, u)]) = r.applyOne x u := by
    rw [ntm.subst_mvar_nil_comp, ← hr, ntm.subst_singleton]
  rw [hA, ntm.subst_comp, ntm.subst_singleton, hStep1]
  exact (ntm.applyOne_of_not_occursIn _ x u (ntm.occursIn_applyOne_self r x u hxu)).symm

/-- When `x` is fresh for the range of `σ`, `σ.comp [(x, u)] = σ ++ [(x, u)]`. -/
lemma Subst.comp_singleton_eq_append {σ : Subst F X 𝔸} {x : X} {u : ntm F X 𝔸}
    (hx : ∀ p ∈ σ, p.2.occursIn x = false) :
    σ.comp [(x, u)] = σ ++ [(x, u)] := by
  unfold Subst.comp
  congr 1
  induction σ with
  | nil => rfl
  | cons p σ' ih =>
      obtain ⟨Y, s⟩ := p
      simp only [List.map_cons, List.cons.injEq]
      refine ⟨?_, ih (fun q hq => hx q (List.mem_cons_of_mem _ hq))⟩
      have hs : s.occursIn x = false := hx (Y, s) (by simp)
      rw [ntm.subst_singleton, ntm.applyOne_of_not_occursIn s x u hs]

end Nominal
