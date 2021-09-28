/-
Copyright (c) 2021 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro, Jakob von Raumer
-/
import Lean.Elab.Command
import Lean.Meta.FunInfo
import Mathlib.Data.Option

open Lean Meta Inhabited

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

inductive RCasesArgs
| hint (tgt : Expr) (depth : Nat)
| rcases (name : Option Name) (tgt : Expr) (pat : RCasesPatt)
| rcases_many (tgt : ListΠ RCasesPatt) (pat : RCasesPatt)

end Meta

syntax (name := Parser.Tactic.rcases) "rcases" : tactic

open Meta Elab Tactic

end Lean
