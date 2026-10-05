import Nominal

/-!
Research probe, 2026-10-05, Lean 4.34.1.
Run: `lake env lean docs/research/probes/BackendStaging.lean`.
This checks a universe-polymorphic bundled arity interpretation and a two-category
raw syntax with recursion in both directions. It does not construct a generic
alpha quotient, initial algebra, syntax generator, or fresh induction theorem.
-/

open Nominal.Core Nominal.Set
universe u

namespace BackendProbe

@[instance_reducible] def discreteNominal (α : Type u) [Name α] (X : Type u) : Nominal α X where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  finSupp _ := ⟨∅, fun _ _ => rfl⟩

structure Obj (α : Type u) [Name α] where
  carrier : Type u
  nominal : Nominal α carrier

inductive Shape (I K : Type) where
  | atom
  | unit
  | data : K → Shape I K
  | recur : I → Shape I K
  | prod : Shape I K → Shape I K → Shape I K
  | bind : Shape I K → Shape I K

def interp {α : Type u} [Name α] {I K : Type}
    (R : I → Obj α) (D : K → Obj α) : Shape I K → Obj α
  | .atom => ⟨α, inferInstance⟩
  | .unit => ⟨PUnit, discreteNominal α PUnit⟩
  | .data k => D k
  | .recur i => R i
  | .prod s t =>
    let S := interp R D s
    let T := interp R D t
    letI := S.nominal
    letI := T.nominal
    ⟨S.carrier × T.carrier, inferInstance⟩
  | .bind s =>
    let S := interp R D s
    letI := S.nominal
    ⟨NameAbs α S.carrier, inferInstance⟩

theorem interp_bind_carrier {α : Type u} [Name α] {I K : Type}
    (R : I → Obj α) (D : K → Obj α) (s : Shape I K) :
    (interp R D (.bind s)).carrier =
      @NameAbs α _ (interp R D s).carrier (interp R D s).nominal := rfl

inductive Cat where
  | term | formula

inductive Raw (α D : Type u) : Cat → Type u where
  | var : α → Raw α D .term
  | data : D → Raw α D .term
  | quote : Raw α D .formula → Raw α D .term
  | eq : Raw α D .term → Raw α D .term → Raw α D .formula
  | all : α → Raw α D .formula → Raw α D .formula

def Raw.size {α D : Type u} {i : Cat} : Raw α D i → Nat
  | .var _ => 1
  | .data _ => 1
  | .quote p => p.size + 1
  | .eq t s => t.size + s.size + 1
  | .all _ p => p.size + 1

def Raw.map {α β D E : Type u} (f : α → β) (g : D → E) {i : Cat} :
    Raw α D i → Raw β E i
  | .var a => .var (f a)
  | .data d => .data (g d)
  | .quote p => .quote (p.map f g)
  | .eq t s => .eq (t.map f g) (s.map f g)
  | .all a p => .all (f a) (p.map f g)

theorem Raw.map_id {α D : Type u} {i : Cat} (x : Raw α D i) :
    x.map id id = x := by
  induction x with
  | var a => rfl
  | data d => rfl
  | quote p ih => simp [Raw.map, ih]
  | eq t s iht ihs => simp [Raw.map, iht, ihs]
  | all a p ih => simp [Raw.map, ih]

theorem Raw.size_map {α β D E : Type u} (f : α → β) (g : D → E)
    {i : Cat} (x : Raw α D i) : (x.map f g).size = x.size := by
  induction x with
  | var a => rfl
  | data d => rfl
  | quote p ih => simp [Raw.map, Raw.size, ih]
  | eq t s iht ihs => simp [Raw.map, Raw.size, iht, ihs]
  | all a p ih => simp [Raw.map, Raw.size, ih]

#print axioms interp
#print axioms interp_bind_carrier
#print axioms Raw.map_id
#print axioms Raw.size_map

end BackendProbe
