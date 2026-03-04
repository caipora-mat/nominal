import NominalSets.Nominal

import Mathlib.Data.Finset.Disjoint
import Mathlib.Order.Filter.Cofinite
import Mathlib.Data.Finite.Defs

/-!
# Freshness

The **freshness** relation between elements of nominal sets formalises the notion of
"having nothing in common" or "being independent." Given two elements `x : X` and
`y : Y` of nominal sets over the same atom type `α`, we write `x # y` to mean
that their least supports are disjoint: `Disjoint (supp x) (supp y)`.

When one of the arguments is an atom `a : α`, freshness reduces to non-membership:
`a # x ↔ a ∉ supp x`.

This file also provides the `choose_fresh` tactic (Choose-a-Fresh-Name Principle,
Pitts 3.1), which picks a fresh atom for a list of nominal-set elements and
introduces individual freshness hypotheses into the local context.

## Main definitions

* `Fresh x y` — `Disjoint (supp x) (supp y)`.

## Notation

* `x # y` — scoped infix notation for `Fresh x y`.

## Main results

### Basic API
* `fresh_iff` — unfolds `Fresh` to `Disjoint (supp x) (supp y)`.
* `fresh_comm` — freshness is symmetric.
* `fresh_equivariant` — freshness is preserved by the permutation action.
* `fresh_equivariant_iff` — `(π • x) # (π • y) ↔ x # y`.
* `fresh_swap` — swapping two atoms that are both fresh for `x` fixes `x`.
* `fresh_prod_right` — `x # (y, z) ↔ x # y ∧ x # z`.
* `fresh_prod_left` — `(x, y) # z ↔ x # z ∧ y # z`.
* `fresh_atom_left` — `a # x ↔ a ∉ supp x`.
* `fresh_atom_right` — `x # a ↔ a ∉ supp x`.
* `fresh_atoms` — `a # b ↔ a ≠ b` for atoms.
* `fresh_finitePerm` — `a # σ ↔ σ a = a` for finite permutations.
* `exists_fresh_atom` — for every `x`, there exists an atom fresh for it.
* `fresh_of_not_mem_support` — atoms outside a support are fresh.
* `fresh_of_supp_empty` — elements with empty support are fresh for every atom.
* `fresh_of_supp_empty_left` — elements with empty support are fresh for any nominal element.
* `fresh_of_supp_empty_right` — any nominal element is fresh for elements with empty support.
* `fresh_atom_finset` — `a # A ↔ a ∉ A` for a finite set of atoms `A`.
* `fresh_finset` — `A # B ↔ Disjoint A B` for finite sets of atoms.
* `fresh_none` — every atom is fresh for `none`.
* `fresh_some` — `a # some y ↔ a # y`.
* `fresh_inl` — `a # Sum.inl x ↔ a # x`.
* `fresh_inr` — `a # Sum.inr y ↔ a # y`.

### Cofinite filter API
* `fresh_atom_compl_eq_supp` — the complement of the fresh-atom set equals `supp x`.
* `fresh_cofinite` — `{a | a # x}` belongs to the cofinite filter.
* `fresh_atom_cofinite` — `∀ᶠ a in cofinite, a # x`.
* `fresh_atom_notin_iff_in_supp` — `w ∈ supp x ↔ w ∉ {a | a # x}`.

## Tactics

* `choose_fresh a from x₁ x₂ … xₙ` — introduces `a : α` and freshness hypotheses
  `a # x₁`, …, `a # xₙ` into the local context. The `from` clause also accepts types
  with a `Nominal` instance, expanding to all local declarations of that type. Omitting
  `from` scans the entire local context for `Nominal`-typed declarations.

## References

* [A. M. Pitts, *Nominal Sets*][Pitts2013], Chapter 3.
-/

namespace NominalSets

open MulAction

variable {α : Type*} [Name α]

/-! ### Freshness -/

section Fresh

variable {X Y Z : Type*} [Nominal α X] [Nominal α Y] [Nominal α Z]

/-- Two elements are **fresh** for each other if their least supports are disjoint. -/
def Fresh (x : X) (y : Y) : Prop := Disjoint (supp x) (supp y)

scoped infix:50 " # " => Fresh

/-- Unfold `Fresh` to disjointness of supports. -/
@[simp]
theorem fresh_iff {x : X} {y : Y} : x # y ↔ Disjoint (supp x) (supp y) :=
  Iff.rfl

/-- Freshness is symmetric. -/
theorem fresh_comm {x : X} {y : Y} : x # y ↔ y # x := by
  simp only [Fresh, disjoint_comm]

/-- Freshness is preserved by the permutation action. -/
theorem fresh_equivariant (π : FinitePerm α) {x : X} {y : Y} (h : x # y) : (π • x) # (π • y) := by
  rw [Fresh, ← supp_equivariant, ← supp_equivariant]
  rw [Fresh] at h
  rw [Finset.disjoint_left] at h ⊢
  intro a ha hy
  rw [PermType.mem_smul_finset_iff] at ha hy
  exact h ha hy

/-- Freshness is invariant under the permutation action. -/
@[simp]
theorem fresh_equivariant_iff (π : FinitePerm α) {x : X} {y : Y} : (π • x) # (π • y) ↔ x # y :=
  ⟨fun h ↦ by simpa using fresh_equivariant π⁻¹ h, fresh_equivariant π⟩

/-- An atom `a` is fresh for `x` if and only if `a ∉ supp x`. -/
@[simp]
theorem fresh_atom_left (a : α) (x : X) : a # x ↔ a ∉ supp x := by
  simp [Fresh, supp_atom, Finset.disjoint_singleton_left]

/-- `x` is fresh for an atom `a` if and only if `a ∉ supp x`. -/
@[simp]
theorem fresh_atom_right (x : X) (a : α) : x # a ↔ a ∉ supp x := by
  rw [fresh_comm]
  exact fresh_atom_left a x

/-- Two atoms are fresh for each other if and only if they are distinct. -/
@[simp]
theorem fresh_atoms (a b : α) : a # b ↔ a ≠ b := by
  simp [Fresh, supp_atom, Finset.disjoint_singleton_left, Finset.mem_singleton]

/-- If both `a` and `b` are fresh for `x`, then swapping them fixes `x`. -/
theorem fresh_swap {a b : α} {x : X} (ha : a # x) (hb : b # x) : swap a b • x = x := by
  rw [fresh_atom_left] at ha hb
  exact (supports_iff_swap.mp (supp_supports x)) a b ha hb

/-- Freshness distributes over products: `x # (y, z) ↔ x # y ∧ x # z`. -/
@[simp]
theorem fresh_prod_right {x : X} {y : Y} {z : Z} : x # (y, z) ↔ x # y ∧ x # z := by
  simp [Fresh, supp_prod, Finset.disjoint_union_right]

/-- Freshness distributes over products (left): `(x, y) # z ↔ x # z ∧ y # z`. -/
@[simp]
theorem fresh_prod_left {x : X} {y : Y} {z : Z} : (x, y) # z ↔ x # z ∧ y # z := by
  simp [Fresh, supp_prod, Finset.disjoint_union_left]

/-- For every `x` in a nominal set, there exists an atom fresh for it. -/
theorem exists_fresh_atom (x : X) : ∃ a : α, a # x := by
  pick_new a (supp x)
  exact ⟨a, (fresh_atom_left a x).mpr aNew⟩

/-- If `s` supports `x`, any atom outside `s` is fresh for `x`. -/
theorem fresh_of_not_mem_support {s : Finset α} {a : α} {x : X}
  (hs : supports s x) (ha : a ∉ s) : a # x := (fresh_atom_left a x).mpr (fun hmem ↦ ha (supp_le hs hmem))

/-- If `x` has empty support, every atom is fresh for it. -/
theorem fresh_of_supp_empty {x : X} (h : supp x = ∅) (a : α) : a # x := by
  simp [Fresh, h]

/-- If `x` has empty support, it is fresh for every element of any nominal set. -/
theorem fresh_of_supp_empty_left {x : X} (h : supp x = ∅) (y : Y) : x # y := by
  simp [Fresh, h]

/-- If `y` has empty support, every element of any nominal set is fresh for it. -/
theorem fresh_of_supp_empty_right {y : Y} (h : supp y = ∅) (x : X) : x # y := by
  simp [Fresh, h]

/-- An atom `a` is fresh for a finite set of atoms `A` if and only if `a ∉ A`. -/
@[simp]
theorem fresh_atom_finset {A : Finset α} {a : α} : a # A ↔ a ∉ A := by
  simp [Fresh, supp_atom, supp_finset, Finset.disjoint_singleton_left]

/-- A finite set of atoms `A` is fresh for `B` if and only if they are disjoint. -/
@[simp]
theorem fresh_finset {A B : Finset α} : A # B ↔ Disjoint A B := by
  simp [Fresh, supp_finset]

/-- An atom `a` is fresh for a permutation `σ` if and only if `σ` fixes `a`. -/
@[simp]
theorem fresh_finitePerm {σ : FinitePerm α} {a : α} : a # σ ↔ σ a = a := by
  rw [fresh_atom_left, supp_finitePerm, PermType.mem_movedFinset, not_not]

/-- Every atom is fresh for `none`. -/
@[simp]
theorem fresh_none (a : α) : a # (none : Option X) := by
  simp [supp_none]

/-- `a # some y ↔ a # y`. -/
@[simp]
theorem fresh_some {a : α} {x : X} : a # (some x) ↔ a # x := by
  simp [supp_some]

/-- `a # Sum.inl x ↔ a # x`. -/
@[simp]
theorem fresh_inl {a : α} {x : X} : a # (Sum.inl x : X ⊕ Y) ↔ a # x := by
  simp [supp_inl]

/-- `a # Sum.inr y ↔ a # y`. -/
@[simp]
theorem fresh_inr {a : α} {y : Y} : a # (Sum.inr y : X ⊕ Y) ↔ a # y := by
  simp [supp_inr]

section Filter

open Filter

-- TODO: these lemmas can be generalized for any nominal set, not only names (α)

/-- an atom belongs to `supp x` precisely when it is not fresh for `x`. -/
@[grind =]
theorem fresh_atom_compl_eq_supp (x : X) : supp x = {a : α | a # x}ᶜ := by
  ext a
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, fresh_atom_left, not_not, Finset.mem_coe]

/-- The set of atoms fresh for `x` belongs to the cofinite filter. -/
theorem fresh_cofinite (x : X) : {a : α | a # x} ∈ cofinite := by
  rw [mem_cofinite, ←fresh_atom_compl_eq_supp]
  exact (supp x).finite_toSet

/-- The set of atoms fresh for `x` is cofinite (its complement is `supp x`, which is finite). -/
theorem fresh_atom_cofinite (x : X) : ∀ᶠ (a : α) in cofinite, a # x := by
  change {a : α | a # x} ∈ cofinite
  apply fresh_cofinite

/-- An atom `w` belongs to `supp x` if and only if it is not fresh for `x`. -/
theorem fresh_atom_notin_iff_in_supp (w : α) (x : X) :
  w ∈ supp x ↔ w ∉ {a : α | a # x} := by simp

end Filter

end Fresh

/-! ### `split_fresh` tactic

`split_fresh h` takes a hypothesis `h : a # (b, c, ..., d)` (or `(a, b, ...) # c`) and
repeatedly applies `fresh_prod_right` / `fresh_prod_left` to split it into individual
freshness hypotheses. Optionally, `split_fresh h with h₁ h₂ …` names the resulting pieces.

- `split_fresh h`                — splits `h : a # (b, c)` into `h_1 : a # b`, `h_2 : a # c`
- `split_fresh h with hb hc`    — same, but with chosen names
- `split_fresh h`                — splits `h : (a, b) # c` into `h_1 : a # c`, `h_2 : b # c`

The original hypothesis `h` is replaced by the individual pieces.
-/

syntax "split_fresh" ident (" with " (colGt ident)+)? : tactic

macro_rules
  | `(tactic| split_fresh $h with $hs:ident*) => `(tactic| (simp only [fresh_prod_right, fresh_prod_left] at $h:ident; obtain ⟨$hs,*⟩ := $h))
  | `(tactic| split_fresh $h) => `(tactic| (simp only [fresh_prod_right, fresh_prod_left] at $h:ident; try obtain ⟨_, _⟩ := $h))

section SPLIT_FRESH_TEST
set_option linter.unusedVariables false

-- Basic right split
example {α X Y} [Name α] [Nominal α X] [Nominal α Y] (x : X) (y : Y)
    (h : x # (x, y)) : True := by
  split_fresh h
  -- h1 : x # x, h2 : x # y
  trivial

-- Right split with custom names
example {α X Y} [Name α] [Nominal α X] [Nominal α Y] (x : X) (y : Y)
    (h : x # (x, y)) : True := by
  split_fresh h with hx hy
  -- hx : x # x, hy : x # y
  trivial

-- Triple tuple (right-associated)
example {α X Y Z} [Name α] [Nominal α X] [Nominal α Y] [Nominal α Z]
    (x : X) (y : Y) (z : Z) (h : x # (x, y, z)) : True := by
  split_fresh h
  -- h1 : x # x, h2 : x # y, h3 : x # z
  trivial

-- Left split
example {α X Y} [Name α] [Nominal α X] [Nominal α Y] (x : X) (y : Y)
    (h : (x, y) # y) : True := by
  split_fresh h
  -- h1 : x # y, h2 : y # y
  trivial

-- Atom freshness in tuple
example {α X} [Name α] [Nominal α X] (a b : α) (x : X)
    (h : a # (b, x)) : True := by
  split_fresh h with hab hax
  -- hab : a # b, hax : a # x
  trivial

end SPLIT_FRESH_TEST

/-! ### `choose_fresh` tactic (Choose-a-Fresh-Name Principle Pitts 3.1)

`choose_fresh a from x₁ x₂ … xₙ` picks a fresh atom `a` for all listed nominal-set elements,
introducing `a : α` and individual freshness hypotheses into the local context.

- `choose_fresh a from x`           — introduces: `a : α`, `ha : a # x`
- `choose_fresh a from x with h`    — introduces: `a : α`, `h : a # x`
- `choose_fresh a from x y`         — introduces: `a : α`, `aFresh1 : a # x`, `aFresh2 : a # y`
- `choose_fresh a from x y with h`  — introduces: `a : α`, `h1 : a # x`, `h2 : a # y`
- `choose_fresh a`                  — scans the local context for all declarations whose type
                                      has a `Nominal` instance and picks `a` fresh for all of them.
- `choose_fresh a with h`           — same, but uses `h` as the hypothesis name.

The `from` clause also accepts **types** with a `Nominal` instance. When a type `X` is given,
it is expanded to all local declarations of type `X`:

- `choose_fresh a from X`           — if `x x' : X` are in context, introduces `a # x` and `a # x'`
- `choose_fresh a from X y`         — mix of types and terms is allowed
-/

syntax "choose_fresh" ident (" from " (colGt term:max)+)? (" with " ident)? : tactic

open Lean Meta Elab Elab.Tactic in
private def evalChooseFresh (a : TSyntax `ident) (xs : Array (TSyntax `term))
    (baseName : String) : TacticM Unit := do
  if xs.isEmpty then
    throwError "choose_fresh: no nominal-set elements found{""
      } (provide them explicitly with 'from' or ensure the local context contains declarations{""
      } whose types have a Nominal instance)"
  -- Reject if name already exists in the local context
  let aName := a.getId
  if (← getLCtx).findFromUserName? aName |>.isSome then
    throwError "choose_fresh: '{aName}' is already declared in the local context"
  let rawHId : TSyntax `ident := ⟨← withFreshMacroScope `(_pfresh)⟩
  -- Build the union `supp x₁ ∪ supp x₂ ∪ … ∪ supp xₙ`.
  let unionTerm ← xs[1:].foldlM (fun acc x ↦ `($acc ∪ NominalSets.supp $x)) (← `(NominalSets.supp $(xs[0]!)))
  -- Obtain a fresh atom outside the union
  evalTactic (← `(tactic| obtain ⟨$a, $rawHId⟩ := ($unionTerm : Finset _).exists_notMem))
  -- For each `xᵢ`, derive `a # xᵢ` using `fresh_atom_left`
  for h : i in [:xs.size] do
    let x := xs[i]
    let hi := mkIdent <| Name.mkSimple s!"{baseName}{i + 1}"
    evalTactic (← `(tactic|
      have $hi : $a # $x := by
        refine (NominalSets.fresh_atom_left $a $x).mpr ?_
        intro _hmem_i
        exact $rawHId (by simp [Finset.mem_union, _hmem_i])))
  -- Clean up the internal raw hypothesis
  evalTactic (← `(tactic| clear $rawHId))

open Lean Meta Elab Elab.Tactic in
/-- Scan the local context for declarations `(x : X)` where a `Nominal α X` instance
    already exists in the local context. Returns their `FVarId`s. -/
private def findNominalDecls : TacticM (Array FVarId) := do
  let lctx ← getLCtx
  let mut nominalTypes : Array Expr := #[]
  let mut result : Array FVarId := #[]
  -- First pass: collect all types X for which a `Nominal α X` instance lives in the context.
  for ldecl in lctx do
    let ty ← instantiateMVars ldecl.type
    -- Check if the type is an application of `Nominal`; if so, its last explicit argument is X.
    if ty.isAppOf ``NominalSets.Nominal then
      -- `Nominal α [Name α] X` — getAppArgs gives #[α, Name_α_inst, X]
      let args := ty.getAppArgs
      nominalTypes := nominalTypes.push args[2]!
  -- Second pass: collect
  for ldecl in lctx do
    let ty ← instantiateMVars ldecl.type
    let isNominal ← nominalTypes.anyM (fun nomTy ↦ isDefEq ty nomTy)
    if isNominal then result := result.push ldecl.fvarId
  return result

open Lean Meta Elab Elab.Tactic in
/-- Find all local declarations whose type is definitionally equal to `targetTy`.
    Skips auxiliary declarations and instance arguments. -/
private def findDeclsOfType (targetTy : Expr) : TacticM (Array FVarId) := do
  let lctx ← getLCtx
  let mut result : Array FVarId := #[]
  for ldecl in lctx do
    if ldecl.isAuxDecl then continue
    if ← isDefEq (← instantiateMVars ldecl.type) targetTy then
      result := result.push ldecl.fvarId
  return result

open Lean Meta Elab Elab.Tactic in
/-- Expand the `from` arguments: if an argument elaborates to a type (a `Sort`)
    with a `Nominal` instance, replace it with all local declarations of that type.
    Otherwise keep it as a plain term. -/
private def expandFromArgs (xs : Array (TSyntax `term)) : TacticM (Array (TSyntax `term)) := do
  pure (← xs.mapM expand).flatten
where
  isType x := do
    -- Try to elaborate the term and check whether it is a type (lives in `Sort _`).
    let e ← Term.elabTerm x none
    let eTy ← inferType e
    pure <| if eTy.isSort then some e else none
  expand x := do
    match (← isType x) with
    | some e => -- `x` elaborated to a type `X`. Find all local decls of type `X`.
      let fvarIds ← findDeclsOfType e
      if fvarIds.isEmpty then
        throwError "choose_fresh: no local declarations of type '{e}' found in context"
      let lctx ← getLCtx
      pure (← fvarIds.mapM fun fid ↦ `($(mkIdent <| lctx.get! fid |>.userName)))
    | none => pure #[x]

open Lean Meta Elab Elab.Tactic in
elab_rules : tactic
  | `(tactic| choose_fresh $a $[from $xs:term*]? $[with $h]?) => do
    let baseName := match h with
      | some h => h.getId.toString
      | none   => a.getId.toString ++ "Fresh"
    withMainContext do
      match xs with
      | some xs => -- Explicit `from` clause (may contain types)
        evalChooseFresh a (← expandFromArgs xs) baseName
      | none => -- No `from` clause: scan the local context for nominal-set declarations.
          let fvarIds ← findNominalDecls
          if fvarIds.isEmpty then
            throwError "choose_fresh: no Nominal instance found in the local context"
          let lctx ← getLCtx
          let xs ← fvarIds.mapM fun fid ↦ `($(mkIdent <| lctx.get! fid |>.userName))
          evalChooseFresh a xs baseName

section CHOOSE_FRESH_TEST
set_option linter.unusedVariables false

example {α X Y} [Name α] [Nominal α X] [Nominal α Y] (x x' : X) (y : Y) : True := by
  choose_fresh c
  trivial

example {α X Y} [Name α] [Nominal α X] [Nominal α Y] (x x' : X) (y : Y) : True := by
  choose_fresh c from x y
  trivial

example {α X Y} [Name α] [Nominal α X] [Nominal α Y] (x x' : X) (y : Y) : True := by
  choose_fresh c from y x with FREEEESH
  trivial

example {α X Y Z} [Name α] [Nominal α X] [Nominal α Y] [Nominal α Z] (x : X) (y : Y) (z : Z) : True := by
  choose_fresh c
  trivial

example {α X Y Z} [Name α] [Nominal α X] [Nominal α Y] [Nominal α Z] (x : X) (y : Y) (z : Z) : True := by
  choose_fresh c with OI
  trivial

example {α X Y Z} [Name α] [Nominal α X] [Nominal α Y] [Nominal α Z] (x : X) (y : Y) (z : Z) : True := by
  choose_fresh c from z
  trivial

example {α X Y} [Name α] [Nominal α X] [Nominal α Y] (x x' : X) (y : Y) : True := by
  choose_fresh a from X
  -- aFresh1 : a # x, aFresh2 : a # x'
  trivial

-- Mix types and terms in `from`
example {α X Y} [Name α] [Nominal α X] [Nominal α Y] (x x' : X) (y : Y) : True := by
  choose_fresh a from X y
  -- aFresh1 : a # x, aFresh2 : a # x', aFresh3 : a # y
  trivial

example {α X Y} [Name α] [Nominal α X] [Nominal α Y] (x x' : X) (y : Y) : True := by
  choose_fresh a from X with hf
  trivial

end CHOOSE_FRESH_TEST

end NominalSets
