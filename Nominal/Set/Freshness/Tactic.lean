import Nominal.Set.Freshness.Basic

/-!
# Freshness tactics

## Tactics

* `split_fresh h` — splits a hypothesis `h : a # (b, c, ..., d)` (or `(a, b, ...) # c`)
  into individual freshness hypotheses.

* `choose_fresh a from x₁ x₂ … xₙ` — introduces `a : α` and freshness hypotheses
  `a # x₁`, …, `a # xₙ` into the local context. The `from` clause also accepts types
  with a `Nominal` instance, expanding to all local declarations of that type. Omitting
  `from` scans the entire local context for `Nominal`-typed declarations.

## References

* [A. M. Pitts, *Nominal Sets*][Pitts2013], Chapter 3.
-/

namespace Nominal.Set
open Core

open MulAction

variable {α : Type*} [Name α]

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
  let unionTerm ← xs[1:].foldlM (fun acc x ↦ `($acc ∪ Nominal.Set.supp $x)) (← `(Nominal.Set.supp $(xs[0]!)))
  -- Obtain a fresh atom outside the union
  evalTactic (← `(tactic| obtain ⟨$a, $rawHId⟩ := ($unionTerm : Finset _).exists_notMem))
  -- For each `xᵢ`, derive `a # xᵢ` using `fresh_atom_left`.
  -- The union is left-associated: `((supp x₁ ∪ supp x₂) ∪ supp x₃) ∪ …`
  -- For index i (0-based), we build a proof that `c ∈ supp xᵢ → c ∈ union`.
  -- For the last element (i = n-1): use `Finset.mem_union_right`
  -- For earlier elements: wrap with `Finset.mem_union_left` from the outside in.
  let n := xs.size
  for h : i in [:n] do
    let x := xs[i]
    let hi := mkIdent <| Name.mkSimple s!"{baseName}{i + 1}"
    -- Build the embedding: start with `_hmem` and wrap with union lemmas
    -- Union structure (for n=3): (supp x₁ ∪ supp x₂) ∪ supp x₃
    -- i=0: mem_union_left _ (mem_union_left _ _hmem)
    -- i=1: mem_union_left _ (mem_union_right _ _hmem)
    -- i=2: mem_union_right _ _hmem
    let hmemId : TSyntax `ident := ⟨← withFreshMacroScope `(_hmem_i)⟩
    -- Build proof term: embed `_hmem_i : c ∈ supp xᵢ` into `c ∈ supp x₁ ∪ ... ∪ supp xₙ`.
    -- The union is left-associated: ((...(supp x₁ ∪ supp x₂) ∪ supp x₃) ... ∪ supp xₙ)
    -- Strategy: collect directions from root to leaf, then wrap from leaf outward.
    -- At each level, if i is the rightmost element go right (done),
    -- otherwise go left and recurse into the left sub-union.
    -- Directions are collected root→leaf, then applied leaf→root to build correct nesting.
    let mut directions : Array Bool := #[]  -- true = right, false = left
    let mut remaining := n
    while remaining > 1 do
      if i == remaining - 1 then
        directions := directions.push true
        remaining := 1
      else
        directions := directions.push false
        remaining := remaining - 1
    -- Apply directions in reverse (leaf to root) to build inside-out proof
    let mut proof : TSyntax `term ← `($hmemId)
    for dir in directions.reverse do
      if dir then
        proof ← `(Finset.mem_union_right _ $proof)
      else
        proof ← `(Finset.mem_union_left _ $proof)
    evalTactic (← `(tactic|
      have $hi : $a # $x :=
        (Nominal.Set.fresh_atom_left $a $x).mpr (fun $hmemId ↦ $rawHId $proof)))
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
    if ty.isAppOf ``Nominal.Set.Nominal then
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

end Nominal.Set
