import Nominal.Set.Freshness.Basic

/-!
# Freshness tactics

## Tactics

* `split_fresh h` — splits a hypothesis `h : a # (b, c, ..., d)` (or `(a, b, ...) # c`)
  into individual freshness hypotheses.

* `choose_fresh a from x₁ x₂ … xₙ` — introduces `a : α` and freshness hypotheses
  `a # x₁`, …, `a # xₙ` into the local context. The `from` clause also accepts types
  with a `Nominal` instance, expanding to eligible local declarations of that type.
  Omitting `from` scans eligible locals using instance synthesis; see the rules below.

## References

* [A. M. Pitts, *Nominal Sets*][Pitts2013], Chapter 3.
-/

namespace Nominal.Set
open Core

open MulAction

variable {α : Type*} [Name α]

/-! ### `split_fresh`

`split_fresh h` recursively splits product freshness on either side of `h`, for either
product association, including product-valued variables. It visits right-hand product
components first, then left-hand components, each from left to right. For example,
`(a, b) # (c, d)` yields `a # c`, `b # c`, `a # d`, `b # d` in that order.

- `split_fresh h` names the leaves `h_1`, `h_2`, …, skipping names already in use.
- `split_fresh h with h₁ h₂ …` requires exactly one distinct, unused name per leaf.
  Too few/many names, duplicates, and collisions (including `h` itself) are errors.
- Non-freshness hypotheses and freshness without a product are errors.

The original hypothesis is cleared when no remaining declaration or goal depends on it;
otherwise it is retained. Every generated leaf is proved from the original hypothesis.
-/

syntax "split_fresh" ident (" with " (colGt ident)+)? : tactic

open Lean Meta Elab Tactic in
private partial def freshnessLeaves (proof : Expr) : MetaM (Array Expr) := do
  let ty ← inferType proof
  if ty.isAppOfArity ``And 2 then
    return (← freshnessLeaves (← mkAppM ``And.left #[proof])) ++
      (← freshnessLeaves (← mkAppM ``And.right #[proof]))
  let some ty ← whnfUntil ty ``Fresh | return #[proof]
  let args := ty.getAppArgs
  let x := args[6]!
  let y := args[7]!
  let right := (← whnf (← inferType y)).isAppOfArity ``Prod 2
  let left := (← whnf (← inferType x)).isAppOfArity ``Prod 2
  unless right || left do return #[proof]
  let pair := if right then y else x
  let fst := mkProj ``Prod 0 pair
  let snd := mkProj ``Prod 1 pair
  let fst := (← reduceProj? fst).getD fst
  let snd := (← reduceProj? snd).getD snd
  let (lemmaName, a, b, c) := if right then
    (``fresh_prod_right, x, fst, snd)
    else (``fresh_prod_left, fst, snd, y)
  let iff ← mkAppOptM lemmaName #[some args[0]!, some args[1]!, none, none, none,
    none, none, none, some a, some b, some c]
  freshnessLeaves (← mkAppM ``Iff.mp #[iff, proof])

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| split_fresh $h $[with $hs:ident*]?) => withMainContext do
    let original ← getFVarId h
    unless (← whnfUntil (← original.getType) ``Fresh).isSome do
      throwError "split_fresh: expected a freshness hypothesis"
    let fid := original
    let leaves ← freshnessLeaves (mkFVar fid)
    if leaves.size == 1 then
      throwError "split_fresh: hypothesis has no product freshness to split"
    let mut names : Array Lean.Name := #[]
    match hs with
    | some hs =>
      unless hs.size == leaves.size do
        throwError "split_fresh: expected {leaves.size} names, got {hs.size}"
      for n in hs do
        let name := n.getId
        if names.contains name || ((← getLCtx).findFromUserName? name).isSome then
          throwError "split_fresh: name '{name}' is already in use"
        names := names.push name
    | none =>
      let mut i := 1
      while names.size < leaves.size do
        let name := Lean.Name.mkSimple s!"{h.getId}_{i}"
        i := i + 1
        if ((← getLCtx).findFromUserName? name).isNone then
          names := names.push name
    let mut goal ← getMainGoal
    for name in names, proof in leaves do
      let (_, next) ← goal.note name proof
      goal := next
    replaceMainGoal [← goal.tryClear fid]

/-! ### `choose_fresh` (Choose-a-Fresh-Name Principle, Pitts 3.1)

`choose_fresh a from x₁ x₂ … xₙ` introduces an atom fresh for every listed object.
Terms are elaborated once; types expand to eligible local elements in declaration order.
Mixed types/terms and repeated inputs are preserved, including shadowed locals.

- `choose_fresh a from x` introduces `a` and `aFresh1 : a # x`.
- `choose_fresh a from x with h` introduces `a` and `h1 : a # x`.
- `choose_fresh a from x y with h` introduces `h1 : a # x`, `h2 : a # y`.
- `choose_fresh a from X y` expands local elements of type `X`, then includes `y`.
- `choose_fresh a` scans eligible locals in declaration order, synthesizing `Nominal`
  instances (including atoms, products, abstractions and nominal functions).
- `choose_fresh a with h` performs the same scan with hypothesis prefix `h`.

Automatic scanning and type expansion skip auxiliary/implementation declarations,
instance/class declarations, proofs, types, and locals whose types contain unresolved
expression metavariables. Candidate checks restore metavariable state. Explicit terms
are not subject to this filter and must elaborate and have nominal instances.

Atom types come from local `Name`/`Nominal` declarations and ordinary instance inference
for the objects. Explicit inputs must all share exactly one available atom type;
automatic mode requires exactly one atom type with eligible locals. Unused atom sorts
are harmless. Ambiguity is an error: use `from` to narrow the objects. This follows Lean's
instance selection; it does not enumerate all alternative global instance derivations.

Empty selections, unsupported explicit inputs, and type expansions without local elements
are errors. The new atom name and all indexed hypothesis names must be unused; a collision
is an error (use `with` to change the prefix). Indexing starts at 1 even for a single input.
-/

syntax "choose_fresh" ident (" from " (colGt term:max)+)? (" with " ident)? : tactic

open Lean Meta Elab Tactic in
/-- `Nominal`'s atom is an out-parameter. Hide incompatible local nominal instances
while checking one atom sort, so derived instances do not silently prefer another sort. -/
private def withFreshAtom {β : Type} (atom : Expr) (action : MetaM β) : MetaM β := do
  let instances ← (← getLocalInstances).filterM fun inst => do
    let ty ← whnf (← inferType inst.fvar)
    if ty.isAppOfArity ``Nominal 3 then
      return ← withoutModifyingState <| isDefEq atom ty.getAppArgs[0]!
    return true
  withLCtx (← getLCtx) instances action

open Lean Meta Elab Elab.Tactic in
private def evalChooseFresh (a : TSyntax `ident) (atom : Expr) (es : Array Expr)
    (baseName : String) : TacticM Unit := do
  let aName := a.getId
  if ((← getLCtx).findFromUserName? aName).isSome then
    throwError "choose_fresh: '{aName}' is already declared in the local context"
  for i in [:es.size] do
    let name := Lean.Name.mkSimple s!"{baseName}{i + 1}"
    if name == aName || ((← getLCtx).findFromUserName? name).isSome then
      throwError "choose_fresh: hypothesis name '{name}' is already in use (use 'with' to change the prefix)"
  -- Assigned expression holes retain FVarIds, including inaccessible shadowed locals.
  let xs ← es.mapM (fun e => Term.exprToSyntax e)
  let atomStx ← Term.exprToSyntax atom
  let supportExprs ← es.mapM fun e =>
    withFreshAtom atom <| mkAppOptM ``supp #[some atom, none, none, none, some e]
  let supports ← supportExprs.mapM (fun e => Term.exprToSyntax e)
  -- Retain the selected instances as well as the selected object expressions.
  let freshLemmas ← supportExprs.mapM fun s => do
    let lemmaExpr := mkAppN (← mkConstWithFreshMVarLevels ``fresh_atom_left) s.getAppArgs[:4]
    Term.exprToSyntax lemmaExpr
  let rawHId : TSyntax `ident := ⟨← withFreshMacroScope `(_pfresh)⟩
  let unionTerm ← supports[1:].foldlM (fun acc s ↦ `($acc ∪ $s)) supports[0]!
  evalTactic (← `(tactic| obtain ⟨$a, $rawHId⟩ := ($unionTerm : Finset $atomStx).exists_notMem))
  for i in [:xs.size] do
    let x := xs[i]!
    let freshLemma := freshLemmas[i]!
    let hi := mkIdent <| Lean.Name.mkSimple s!"{baseName}{i + 1}"
    let hmemId : TSyntax `ident := ⟨← withFreshMacroScope `(_hmem_i)⟩
    -- Do not simplify supports: embed membership at its original union position.
    let mut proof : TSyntax `term ← `($hmemId)
    if i > 0 then
      proof ← `(Finset.mem_union_right _ $proof)
    for _ in [i + 1:xs.size] do
      proof ← `(Finset.mem_union_left _ $proof)
    evalTactic (← `(tactic|
      have $hi :=
        ($freshLemma $a $x).mpr
          (fun $hmemId ↦ $rawHId $proof)))
  evalTactic (← `(tactic| clear $rawHId))

open Lean Meta Elab Tactic in
/-- Speculative checks never assign metavariables in the caller's proof state. -/
private def sameFreshType (a b : Expr) : MetaM Bool :=
  withoutModifyingState <| isDefEq a b

open Lean Meta Elab Tactic in
private def freshCandidate (decl : LocalDecl) : MetaM Bool := withoutModifyingState do
  if decl.isAuxDecl || decl.isImplementationDetail || decl.binderInfo.isInstImplicit then
    return false
  let ty ← instantiateMVars decl.type
  return !ty.hasExprMVar && !(← isProp ty) && !(← whnf ty).isSort &&
    (← isClass? ty).isNone

open Lean Meta Elab Tactic in
/-- Synthesize before fixing the out-parameter, or check a particular atom type.
Only a fully resolved atom type escapes this speculative computation. -/
private def nominalAtom? (ty : Expr) (atom? : Option Expr := none) : MetaM (Option Expr) :=
  withoutModifyingState do
    try
      let atom ← match atom? with
        | some atom => pure atom
        | none => mkFreshExprMVar (mkSort (.succ (← mkFreshLevelMVar)))
      let name ← mkFreshExprMVar (← mkAppM ``Core.Name #[atom])
      let cls := mkApp3 (← mkConstWithFreshMVarLevels ``Nominal) atom name ty
      let _ ← match atom? with
        | some atom => withFreshAtom atom <| synthInstance cls
        | none => synthInstance cls
      let atom ← instantiateMVars atom
      if atom.hasMVar then return none
      return some atom
    catch _ => return none

open Lean Meta Elab Tactic in
private def expandFromArgs (xs : Array (TSyntax `term)) : TacticM (Array Expr) := do
  let mut result := #[]
  for x in xs do
    let e ← Term.elabTerm x none
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    if ← isType e then
      let mut found := false
      for decl in ← getLCtx do
        if (← freshCandidate decl) && (← sameFreshType decl.type e) then
          result := result.push decl.toExpr
          found := true
      unless found do
        throwError "choose_fresh: no local declarations of type '{e}' found in context"
    else
      result := result.push e
  return result

open Lean Meta Elab Tactic in
/-- Consider local atom instances as well as atoms inferred from the selected objects.
Checking each candidate avoids silently choosing between two local atom sorts. -/
private def selectFreshInputs (explicit? : Option (Array Expr)) : TacticM (Expr × Array Expr) := do
  let mut inputs := explicit?.getD #[]
  if explicit?.isNone then
    for decl in ← getLCtx do
      if ← freshCandidate decl then inputs := inputs.push decl.toExpr
  let mut atoms : Array Expr := #[]
  for inst in ← getLocalInstances do
    let ty ← withoutModifyingState <| whnf (← instantiateMVars (← inferType inst.fvar))
    if ty.isAppOfArity ``Core.Name 1 || ty.isAppOfArity ``Nominal 3 then
      let atom := ty.getAppArgs[0]!
      if !atom.hasMVar && !(← atoms.anyM (fun other => sameFreshType atom other)) then
        atoms := atoms.push atom
  for e in inputs do
    if let some atom ← nominalAtom? (← inferType e) then
      if !(← atoms.anyM (fun other => sameFreshType atom other)) then atoms := atoms.push atom
  let mut choices : Array (Expr × Array Expr) := #[]
  for atom in atoms do
    let selected ← inputs.filterM fun e =>
      return (← nominalAtom? (← inferType e) (some atom)).isSome
    if !selected.isEmpty && (explicit?.isNone || selected.size == inputs.size) then
      choices := choices.push (atom, selected)
  if choices.isEmpty then
    throwError "choose_fresh: no common atom type with Nominal instances for the selected inputs (use 'from' with nominal terms or types having local elements)"
  if choices.size > 1 then
    let types := choices.map Prod.fst
    throwError "choose_fresh: ambiguous atom types {types}; use 'from' to select objects with one common atom type"
  return choices[0]!

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| choose_fresh $a $[from $xs:term*]? $[with $h]?) => withMainContext do
    let baseName := h.map (·.getId.toString) |>.getD (a.getId.toString ++ "Fresh")
    let explicit? ← xs.mapM expandFromArgs
    let (atom, inputs) ← selectFreshInputs explicit?
    evalChooseFresh a atom inputs baseName

end Nominal.Set
