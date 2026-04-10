/-- Computable list of atoms in a permutation. -/
def LPerm.atomsList [Name 𝔸] : LPerm 𝔸 → List 𝔸
  | []           => []
  | (a, b) :: ps => a :: b :: LPerm.atomsList ps

/-- Computable difference list (may contain duplicates). -/
def dsList [Name 𝔸] (π π' : LPerm 𝔸) : List 𝔸 :=
  (LPerm.atomsList π ++ LPerm.atomsList π').filter fun n =>
    LPermApply π n ≠ LPermApply π' n

/-- A constraint is either a freshness question `a #? t` or an alpha-equivalence question `s ≈α? t`. -/
inductive Constraint (F X 𝔸 : Type*) [DecidableEq F] [DecidableEq X] [Name 𝔸] where
  | fresh : 𝔸 → ntm F X 𝔸 → Constraint F X 𝔸
  | alpha : ntm F X 𝔸 → ntm F X 𝔸 → Constraint F X 𝔸

/-- A constraint problem is a list of constraints. -/
abbrev Problem (F X 𝔸 : Type*) [DecidableEq F] [DecidableEq X] [Name 𝔸] :=
  List (Constraint F X 𝔸)

/-- Single-constraint simplification.
    Returns `none` if the constraint is already reduced,
    or `some cs` with the list of simpler constraints. -/
def simplifyOne : Constraint F X 𝔸 → Option (Problem F X 𝔸)
  -- Freshness rules
  | .fresh a (.atm b)       => if a = b then none else some []
  | .fresh a (.fapp _ ts)   => some (ts.map (.fresh a))
  | .fresh a (.abs b t)     => if a = b then some [] else some [.fresh a t]
  | .fresh a (.mvar π x)    =>
      if π = [] then none
      else some [.fresh (LPermApply π.reverse a) (.mvar [] x)]
      
  -- Alpha-equivalence rules
  | .alpha (.atm a) (.atm b)          => if a = b then some [] else none
  | .alpha (.fapp f ls) (.fapp g ss)  =>
      if f = g then some (List.zipWith .alpha ls ss)
      else none
  | .alpha (.abs a l) (.abs b s)      =>
      if a = b then some [.alpha l s]
      else some [.alpha (l.permute [(b, a)]) s, .fresh b l]
  | .alpha (.mvar π x) (.mvar π' y)   =>
      if x = y then some ((dsList π π').map fun n => .fresh n (.mvar [] x))
      else none
  | _ => none

mutual
  def ntmSize : ntm F X 𝔸 → Nat
    | .atm _      => 1
    | .mvar _ _   => 1
    | .fapp _ ts  => 1 + ntmSizeList ts
    | .abs _ t    => 1 + ntmSize t

  def ntmSizeList : List (ntm F X 𝔸) → Nat
    | []      => 0
    | t :: ts => ntmSize t + ntmSizeList ts
end

def constraintSize : Constraint F X 𝔸 → Nat
  | .fresh _ t  => ntmSize t
  | .alpha s t  => ntmSize s + ntmSize t

def problemMeasure (Pr : Problem F X 𝔸) : Multiset ℕ :=
  Multiset.ofList (Pr.map constraintSize)

mutual
  lemma ntmSize_permute (t : ntm F X 𝔸) (π : LPerm 𝔸) :
      ntmSize (t.permute π) = ntmSize t := by
    match t with
    | .atm _      => simp [ntm.permute, ntmSize]
    | .mvar _ _   => simp [ntm.permute, ntmSize]
    | .abs _ t    => simp [ntm.permute, ntmSize, ntmSize_permute t π]
    | .fapp _ ts  => simp [ntm.permute, ntmSize, ntmSizeList_permute ts π]
  termination_by sizeOf t

  lemma ntmSizeList_permute (ts : List (ntm F X 𝔸)) (π : LPerm 𝔸) :
      ntmSizeList (ts.map (ntm.permute π)) = ntmSizeList ts := by
    match ts with
    | []       => simp [ntmSizeList]
    | t :: ts  => simp [ntmSizeList, ntmSize_permute t π, ntmSizeList_permute ts π]
  termination_by sizeOf ts
end

lemma ntmSize_le_ntmSizeList (ts : List (ntm F X 𝔸)) {t : ntm F X 𝔸} (ht : t ∈ ts) :
    ntmSize t ≤ ntmSizeList ts := by
  induction ts with
  | nil  => exact absurd ht (List.not_mem_nil)
  | cons t' ts ih =>
    simp only [ntmSizeList]
    rcases List.mem_cons.mp ht with rfl | hmem
    · omega
    · have := ih hmem; omega

-- Fresh constraints are cheap relative to their term's size
lemma constraintSize_fresh_le (a : 𝔸) (t : ntm F X 𝔸) :
    constraintSize (.fresh a t) ≤ ntmSize t + 1 := by
  match t with
  | .mvar π _ =>
    simp only [constraintSize, ntmSize]
    omega
  | _ => simp [constraintSize]

lemma simplifyOne_lt (c : Constraint F X 𝔸) (cs : Problem F X 𝔸)
    (h : simplifyOne c = some cs) (c' : Constraint F X 𝔸) (hc' : c' ∈ cs) :
    constraintSize c' < constraintSize c := by
  match c with
  | .fresh a (.atm b) =>
    simp only [simplifyOne] at h
    split_ifs at h <;> simp_all

  | .fresh a (.fapp f ts) =>
    simp only [simplifyOne, Option.some.injEq] at h; subst h
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hc'
    simp only [constraintSize, ntmSize]
    simp [Nat.add_comm]
    apply Nat.lt_succ_iff.mpr
    exact ntmSize_le_ntmSizeList ts ht

  | .fresh a (.abs b t) =>
    simp only [simplifyOne] at h
    by_cases hab : a = b
    · simp_all
    · simp only [hab, ite_false, Option.some.injEq] at h; subst h
      simp only [List.mem_singleton] at hc'; subst hc'
      simp only [constraintSize, ntmSize]; omega

  | .fresh a (.mvar π x) =>
    simp only [simplifyOne] at h
    by_cases hπ : π = []
    · simp_all
    · simp only [hπ, ite_false, Option.some.injEq] at h; subst h
      simp only [List.mem_singleton] at hc'; subst hc'
      simp only [constraintSize]
      simp only [ntmSize]

  -- .alpha (.atm a) (.atm b): cs = [] when a = b
  | .alpha (.atm a) (.atm b) => sorry

  -- .alpha (.fapp f ls) (.fapp f ss): cs = zipWith .alpha ls ss
  | .alpha (.fapp f ls) (.fapp g ss) => sorry

  -- .alpha (.abs a l) (.abs b s): two sub-cases on a = b
  | .alpha (.abs a l) (.abs b s) => sorry
    
  -- .alpha (.mvar π x) (.mvar π' y): cs = dsList ... mapped to fresh constraints
  | .alpha (.mvar π x) (.mvar π' y) => sorry

  -- All remaining alpha combinations: simplifyOne returns none
  | .alpha (.atm _)  (.mvar _ _) | .alpha (.atm _)  (.fapp _ _) | .alpha (.atm _)  (.abs _ _)
  | .alpha (.mvar _ _) (.atm _)  | .alpha (.mvar _ _) (.fapp _ _)| .alpha (.mvar _ _) (.abs _ _)
  | .alpha (.fapp _ _) (.atm _)  | .alpha (.fapp _ _) (.mvar _ _)| .alpha (.fapp _ _) (.abs _ _)
  | .alpha (.abs _ _)  (.atm _)  | .alpha (.abs _ _)  (.mvar _ _)| .alpha (.abs _ _)  (.fapp _ _) =>
    simp [simplifyOne] at h

/-- Simplify all constraints in a problem until no more rules apply.
    Returns the reduced (normal form) problem. -/
partial def simplify : (Problem F X 𝔸) → (Problem F X 𝔸)
  | [] => []
  | c :: Pr =>
    match simplifyOne c with
    | some cs => (simplify cs) ++ (simplify Pr)
    | none    => c :: simplify Pr

