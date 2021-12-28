/-
Copyright (c) 2021 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro, Jakob von Raumer
-/
import Lean.Elab.Command
import Lean.Meta.FunInfo
import Mathlib.Data.Option

open Lean Meta Inhabited

namespace Lean.Parser.Tactic

declare_syntax_cat rcasesPat
syntax rcasesPatMed := sepBy1(rcasesPat, " | ")
syntax rcasesPatLo := rcasesPatMed (" : " term)?
syntax (name := rcasesPat.one) ident : rcasesPat
syntax (name := rcasesPat.ignore) "_" : rcasesPat
syntax (name := rcasesPat.clear) "-" : rcasesPat
syntax (name := rcasesPat.tuple) "⟨" rcasesPatLo,* "⟩" : rcasesPat
syntax (name := rcasesPat.paren) "(" rcasesPatLo ")" : rcasesPat
syntax (name := rcases?) "rcases?" casesTarget,* (" : " num)? : tactic
syntax (name := rcases) "rcases" casesTarget,* (" with " rcasesPat)? : tactic

end Lean.Parser.Tactic


namespace Lean

namespace Meta

@[reducible] def ListSigma := List
@[reducible] def ListPi    := List

local notation "ListΣ" => ListSigma
local notation "ListΠ" => ListPi

inductive RCasesPatt : Type
| one : Name → RCasesPatt
| clear : RCasesPatt
| typed : RCasesPatt → Expr → RCasesPatt -- Exchange `Expr` for `Syntax`?
| tuple : List RCasesPatt → RCasesPatt
| alts :  List RCasesPatt → RCasesPatt
deriving Inhabited

declare_syntax_cat rcases_patt
syntax ident : rcases_patt
syntax "⟨"rcases_patt,*"⟩" : rcases_patt
syntax "("rcases_patt,*")" : rcases_patt

macro_rules
| `(rcases_patt|⟨a, ⟨b, c⟩⟩) => `(rcases_patt|⟨a, b, c⟩)
| `(rcases_patt|(a, (b, c))) => `(rcases_patt|(a, b, c))

namespace RCasesPatt

partial def name : RCasesPatt → Option Name
| one `_    => none
| one `rfl  => none
| one n     => n
| typed p _ => p.name
| alts [p]  => p.name
| _         => none

def asTuple : RCasesPatt → ListΠ RCasesPatt
| tuple ps => ps
| p        => [p]

def asAlts : RCasesPatt → ListΣ RCasesPatt
| alts ps => ps
| p       => [p]

def tuple' : ListΠ RCasesPatt → RCasesPatt
| [p] => p
| ps  => tuple ps

def alts' : ListΣ RCasesPatt → RCasesPatt
| [p] => p
| ps  => alts ps

def tuple₁Core : ListΠ RCasesPatt → ListΠ RCasesPatt
| []         => []
| [tuple []] => [tuple []]
| [tuple ps] => ps
| p :: ps    => p :: tuple₁Core ps

def tuple₁ : ListΠ RCasesPatt → RCasesPatt
| []      => default
| [one n] => one n
| ps      => tuple $ tuple₁Core ps

def alts₁Core : ListΣ (ListΠ RCasesPatt) → ListΣ RCasesPatt
| []          => []
| [[alts ps]] => ps
| p :: ps     => tuple₁ p :: alts₁Core ps

def alts₁ : ListΣ (ListΠ RCasesPatt) → RCasesPatt
| [[]]        => tuple []
| [[alts ps]] => tuple ps
| ps          => alts' $ alts₁Core ps

-- TODO has_reflect, format

end RCasesPatt

def RCases.processConstructor : Nat → ListΠ RCasesPatt → ListΠ Name × ListΠ RCasesPatt
| 0,     ps      => ([], [])
| 1,     []      => ([`_], default)
| 1,     [p]     => ([p.name.getOrElse `_], [p])
| 1,     ps      => ([`_], [RCasesPatt.tuple ps])
| n + 1, p :: ps => let (ns, tl) := processConstructor n ps
                    (p.name.getOrElse `_ :: ns, p :: tl)
| _,     _       => ([], [])

def RCases.processConstructors (params : Nat) :
  ListΣ Name → ListΣ RCasesPatt → MetaM (List Name × ListΣ (Name × ListΠ RCasesPatt))
| [], ps           => ([], [])
| c :: cs, p :: ps => do
  let n := FunInfo.getArity $ ← getFunInfo (mkConst c) --TODO check if this does the right thing
  let (h, t) := match cs, ps with
  | [], _ :: _ => ([RCasesPatt.alts ps], [])
  | _,  _      => (p.asTuple, ps)
  let (ns, ps) := RCases.processConstructor (n - params) h
  let (l,  r)  ← processConstructors params cs t
  pure (ns ++ l, (c, ps) :: r)
| _,       _       => panic! "Not enough `rcases` patterns!"

def align (p : α → β → Prop) [∀ a b, Decidable (p a b)] :
  List α → List β → List (α × β)
| a :: as, b :: bs =>
  if p a b then (a, b) :: align p as bs else align p as (b :: bs)
| _,       _       => []

inductive RCasesArgs
| hint (tgt : Expr) (depth : Nat)
| rcases (name : Option Name) (tgt : Expr) (pat : RCasesPatt)
| rcases_many (tgt : ListΠ RCasesPatt) (pat : RCasesPatt)

open Elab Tactic

@[reducible]
def UnclearedGoal := (List Expr) × MVarId

@[reducible]
def SubstMetaM := StateT (FVarSubst × List MVarId) MetaM

mutual

partial def RCases_core : RCasesPatt → Expr → SubstMetaM (List UnclearedGoal)
| RCasesPatt.one `rfl, e => do
  match ← get with
  | (fs, g :: gs) =>
    let (_, g) ← substCore g e.fvarId! (fvarSubst := fs)
    return (g :: gs).map (Prod.mk [])
  | (fs, []) => throwError "foo"
| RCasesPatt.one _, _ => do return (← get).2.map (Prod.mk [])
| RCasesPatt.clear, e => do
  let (fs, gs) ← get
  let e := fs.apply e
  return (← get).2.map (Prod.mk [e])
| RCasesPatt.alts [p], e => RCases_core p e
| _, _ => do return []

partial def RCases_continue : ListΠ (RCasesPatt × Expr) → SubstMetaM (List UnclearedGoal)
| []  => do return (← get).2.map (Prod.mk [])
| ((pat, e) :: ps) => do
  let gs ← RCases_core pat e
  List.join <$> gs.mapM fun (cs, g) => do
    let (fs, _) ← get
    set (fs, [g])
    let ugs ← RCases_continue ps
    pure $ ugs.map fun (cs', g) => (cs ++ cs, g)

end

def clearGoals (ugs : List UnclearedGoal) : SubstMetaM (List MVarId) :=
  ugs.mapM fun (cs, g) => do
    let (fs, _) ← get
    let cs : List Expr := (cs.map fs.apply).filter Expr.isFVar
    tryClearMany g $ (cs.map Expr.fvarId!).toArray

end Meta

inductive RCasesArgs
| hint (tgt : Expr) (depth : Nat)
| rcases (name : Option Name) (tgt : Expr) (pat : RCasesPatt)
| rcases_many (tgt : ListPi RCasesPatt) (pat : RCasesPatt)

/-
declare_syntax_cat rcasesPat
syntax rcasesPatMed := sepBy1(rcasesPat, " | ")
syntax rcasesPatLo := rcasesPatMed (" : " term)?
syntax (name := rcasesPat.one) ident : rcasesPat
syntax (name := rcasesPat.tuple) "⟨" rcasesPatLo,* "⟩" : rcasesPat
syntax (name := rcasesPat.paren) "(" rcasesPatLo ")" : rcasesPat
syntax (name := rcases?) "rcases?" casesTarget,* (" : " num)? : tactic
syntax (name := rcases) "rcases" casesTarget,* (" with " rcasesPat)? : tactic
-/

open Elab

def RCasesPatt.Parse : Syntax → MetaM RCasesPatt
| `(rcasesPat|_) => RCasesPatt.one `_
| `(rcasesPat|rfl) => RCasesPatt.one `rfl
| `(rcasesPat|-) => RCasesPatt.clear
| `(rcasesPat|⟨$[$ps:rcasesPat|* $[: $t:term]?],*⟩) => do
   let ps := ps.map Syntax.SepArray.getElems
   let ps := Array.zip ps t
   let f
   | (p, none)   => do
     RCasesPatt.alts' $ (← p.toList.mapM Parse)
   | (p, some t) => do
     let alts := RCasesPatt.alts' $ (← p.toList.mapM Parse)
     RCasesPatt.typed alts t
   return RCasesPatt.tuple' $ ← ps.toList.mapM f
| `(rcasesPat|($ps:rcasesPat|* $[: $t:term]?)) => _
| _ => throwUnsupportedSyntax

#check RCasesPatt.alts'

open Meta Elab Parser.Tactic

elab "rcases " tgts:casesTarget " with " pat:rcasesPat : tactic => pure ()

end Lean.Elab.Tactic

example (m : Nat) : m > 0 ∨ m ≤ 4 := by
  skip
  rcases m with ⟨⟨a, c⟩|b : Nat⟩


end Lean
