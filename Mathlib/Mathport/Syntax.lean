/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Lean.Elab.Command
import Lean.Elab.Quotation
import Std.Tactic.Ext
import Std.Tactic.RCases
import Mathlib.Logic.Equiv.LocalEquiv
import Mathlib.Tactic.Alias
import Mathlib.Tactic.ApplyWith
import Mathlib.Tactic.ApplyRules
import Mathlib.Tactic.Cases
import Mathlib.Tactic.CasesM
import Mathlib.Tactic.Clear!
import Mathlib.Tactic.ClearExcept
import Mathlib.Tactic.Clear_
import Mathlib.Tactic.CommandQuote
import Mathlib.Tactic.Constructor
import Mathlib.Tactic.Core
import Mathlib.Tactic.Existsi
import Mathlib.Tactic.Find
import Mathlib.Tactic.InferParam
import Mathlib.Tactic.Inhabit
import Mathlib.Tactic.LeftRight
import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.NormCast
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.PushNeg
import Mathlib.Tactic.Recover
import Mathlib.Tactic.Replace
import Mathlib.Tactic.Relation.Rfl
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Set
import Mathlib.Tactic.SimpTrace
import Mathlib.Tactic.Simps
import Mathlib.Tactic.SolveByElim
import Mathlib.Tactic.Trace
import Mathlib.Tactic.Substs
import Mathlib.Util.WithWeakNamespace
import Mathlib.Util.Syntax

-- To fix upstream:
-- * bracketedExplicitBinders doesn't support optional types

/-!
This file defines all the tactics that are required by mathport. Most of the `syntax` declarations
in this file (as opposed to the imported files) are not defined anywhere and effectively form the
TODO list before we can port mathlib to lean 4 for real.

For tactic writers: I (Mario) have put a comment before each syntax declaration to represent the
estimated difficulty of writing the tactic. The key is as follows:

* `E`: Easy. It's a simple macro in terms of existing things,
  or an elab tactic for which we have many similar examples. Example: `left`
* `M`: Medium. An elab tactic, not too hard, perhaps a 100-200 lines file. Example: `have`
* `N`: Possibly requires new mechanisms in lean 4, some investigation required
* `B`: Hard, because it is a big and complicated tactic
* `S`: Possibly easy, because we can just stub it out or replace with something else
* `?`: uncategorized
-/

namespace Lean

namespace Parser.Command
open Std.ExtendedBinder

/- N -/ elab (name := include) "include " ident+ : command => pure ()
/- N -/ elab (name := omit) "omit " ident+ : command => pure ()
/- N -/ syntax (name := parameter) "parameter " bracketedBinder+ : command

/--
Expands binders into nested combinators.
For example, the familiar exists is given by:
`expandBinders% (p => Exists p) x y : Nat, x < y`
which expands to the same expression as
`∃ x y : Nat, x < y`
-/
syntax "expandBinders% " "(" ident " => " term ")" extBinders ", " term : term

macro_rules
  | `(expandBinders% ($x => $term) $y:extBinder, $res) =>
    `(expandBinders% ($x => $term) ($y:extBinder), $res)
  | `(expandBinders% ($_ => $_), $res) => pure res
macro_rules
  | `(expandBinders% ($x => $term) ($y:ident $[: $ty]?) $binders*, $res) => do
    let ty := ty.getD (← `(_))
    term.replaceM fun x' => do
      unless x == x' do return none
      `(fun $y:ident : $ty => expandBinders% ($x => $term) $[$binders]*, $res)
  | `(expandBinders% ($x => $term) ($y:ident $pred:binderPred) $binders*, $res) =>
    term.replaceM fun x' => do
      unless x == x' do return none
      `(fun $y:ident => expandBinders% ($x => $term) (h : satisfiesBinderPred% $y $pred)
        $[$binders]*, $res)

macro (name := expandFoldl) "expandFoldl% "
  "(" x:ident y:ident " => " term:term ")" init:term:max "[" args:term,* "]" : term =>
  args.getElems.foldlM (init := init) fun res arg => do
    term.replaceM fun e =>
      return if e == x then some res else if e == y then some arg else none
macro (name := expandFoldr) "expandFoldr% "
  "(" x:ident y:ident " => " term:term ")" init:term:max "[" args:term,* "]" : term =>
  args.getElems.foldrM (init := init) fun arg res => do
    term.replaceM fun e =>
      return if e == x then some arg else if e == y then some res else none

/-- Keywording indicating whether to use a left- or right-fold. -/
syntax foldKind := &"foldl" <|> &"foldr"
/-- `notation3` argument matching `extBinders`. -/
syntax bindersItem := atomic("(" "..." ")")
/-- `notation3` argument simulating a Lean 3 fold notation. -/
syntax foldAction := "(" ident strLit "*" " => " foldKind " (" ident ident " => " term ") " term ")"
/-- `notation3` argument binding a name. -/
syntax identOptScoped := ident (":" "(" "scoped " ident " => " term ")")?
/-- `notation3` argument. -/
syntax notation3Item := strLit <|> bindersItem <|> identOptScoped <|> foldAction
/--
`notation3` declares notation using Lean 3-style syntax.
Only to be used for mathport.
-/
macro ak:Term.attrKind "notation3"
    prec:(precedence)? name:(namedName)? prio:(namedPrio)?
    lits:(notation3Item)+ " => " val:term : command => do
  let mut boundNames : Lean.HashMap Name Syntax := {}
  let mut macroArgs := #[]
  for lit in lits do
    match (lit : TSyntax ``notation3Item) with
    | `(notation3Item| $lit:str) =>
      macroArgs := macroArgs.push (← `(macroArg| $lit:str))
    | `(notation3Item| $_:bindersItem) =>
      macroArgs := macroArgs.push (← `(macroArg| binders:extBinders))
    | `(notation3Item| ($id:ident $sep:str* => $kind ($x $y => $scopedTerm) $init)) =>
      macroArgs := macroArgs.push (← `(macroArg| $id:ident:sepBy(term, $sep:str)))
      let scopedTerm ← scopedTerm.replaceM fun
        | Syntax.ident _ _ id .. => pure $ boundNames.find? id
        | _ => pure none
      let init ← init.replaceM fun
        | Syntax.ident _ _ id .. => pure $ boundNames.find? id
        | _ => pure none
      let args := mkNullNode #[.mkAntiquotSuffixSpliceNode `sepBy
        (.mkAntiquotNode `term (← `(Syntax.TSepArray.ofElems ($id:ident).getElems))) ",*"]
      let args := #[
        Lean.mkAtom "(", x, y, Lean.mkAtom "=>", scopedTerm, Lean.mkAtom ")", init,
        Lean.mkAtom "[", args, Lean.mkAtom "]"]
      let stx ← show MacroM Syntax.Term from match kind.1[0] with
        | .atom _ "foldl" => pure ⟨mkNode ``expandFoldl (#[Lean.mkAtom "expandFoldl%"] ++ args)⟩
        | .atom _ "foldr" => pure ⟨mkNode ``expandFoldr (#[Lean.mkAtom "expandFoldr%"] ++ args)⟩
        | _ => Macro.throwUnsupported
      boundNames := boundNames.insert id.getId stx
    | `(notation3Item| $lit:ident : (scoped $scopedId:ident => $scopedTerm)) =>
      let id := lit.getId
      macroArgs := macroArgs.push (← `(macroArg| $lit:ident:term))
      let scopedTerm ← scopedTerm.replaceM fun
        | Syntax.ident _ _ id .. => pure $ boundNames.find? id
        | _ => pure none
      boundNames := boundNames.insert id <|
        ← `(expandBinders% ($scopedId => $scopedTerm) $$binders:extBinders,
          $(⟨lit.1.mkAntiquotNode `term⟩):term)
    | `(notation3Item| $lit:ident) =>
      macroArgs := macroArgs.push (← `(macroArg| $lit:ident:term))
      boundNames := boundNames.insert lit.getId <| lit.1.mkAntiquotNode `term
    | stx => Macro.throwUnsupported
  let val ← val.replaceM fun
    | Syntax.ident _ _ id .. => pure $ boundNames.find? id
    | _ => pure none
  `($ak:attrKind macro $[$prec]? $[$name]? $[$prio]? $[$macroArgs]* : term => do
    `($val:term))

end Parser.Command

namespace Parser.Term

/- S -/ syntax "quoteₓ " term : term
/- S -/ syntax "pquoteₓ " term : term
/- S -/ syntax "ppquoteₓ " term : term
/- S -/ syntax "%%ₓ" term : term

end Term

namespace Tactic

/- S -/ syntax (name := propagateTags) "propagate_tags " tacticSeq : tactic
/- S -/ syntax (name := mapply) "mapply " term : tactic
/- S -/ syntax (name := withCases) "with_cases " tacticSeq : tactic
/- S -/ syntax "destruct " term : tactic
/- N -/ syntax (name := abstract) "abstract" (ppSpace ident)? ppSpace tacticSeq : tactic

/- N -/ syntax (name := simpIntro) "simp_intro" (config)?
  (ppSpace colGt (ident <|> "_"))* (&" only")? (simpArgs)? : tactic
/- E -/ syntax (name := symm) "symm" : tactic
/- E -/ syntax (name := trans) "trans" (ppSpace colGt term)? : tactic
/- B -/ syntax (name := cc) "cc" : tactic

/- M -/ syntax (name := unfoldProjs) "unfold_projs" (config)? (ppSpace location)? : tactic

/- E -/ syntax (name := inferAutoParam) "infer_auto_param" : tactic

/- S -/ syntax (name := rsimp) "rsimp" : tactic
/- S -/ syntax (name := compVal) "comp_val" : tactic
/- S -/ syntax (name := async) "async " tacticSeq : tactic

/- E -/ syntax (name := apply') "apply' " term : tactic
/- E -/ syntax (name := fapply') "fapply' " term : tactic
/- E -/ syntax (name := eapply') "eapply' " term : tactic
/- E -/ syntax (name := applyWith') "apply_with' " (config)? term : tactic
/- E -/ syntax (name := mapply') "mapply' " term : tactic
/- E -/ syntax (name := rfl') "rfl'" : tactic
/- E -/ syntax (name := symm') "symm'" (ppSpace location)? : tactic
/- E -/ syntax (name := trans') "trans'" (ppSpace term)? : tactic

/- M -/ syntax (name := injectionsAndClear) "injections_and_clear" : tactic

/- E -/ syntax (name := tryFor) "try_for " term:max tacticSeq : tactic
/- E -/ syntax (name := unfoldCoes) "unfold_coes" (ppSpace location)? : tactic
/- E -/ syntax (name := unfoldWf) "unfold_wf" : tactic
/- M -/ syntax (name := unfoldAux) "unfold_aux" : tactic
/- S -/ syntax (name := «continue») "continue " tacticSeq : tactic
/- M -/ syntax (name := generalizeHyp) "generalize " atomic(ident " : ")? term:51 " = " ident
  ppSpace location : tactic
/- M -/ syntax (name := clean) "clean " term : tactic
/- B -/ syntax (name := refineStruct) "refine_struct " term : tactic
/- M -/ syntax (name := matchHyp) "match_hyp " ("(" &"m" " := " term ") ")? ident " : " term :
  tactic
/- S -/ syntax (name := guardTags) "guard_tags" (ppSpace ident)* : tactic
/- S -/ syntax (name := guardProofTerm) "guard_proof_term " tactic:51 " => " term : tactic
/- S -/ syntax (name := failIfSuccess?) "fail_if_success? " str ppSpace tacticSeq : tactic
/- N -/ syntax (name := field) "field " ident " => " tacticSeq : tactic
/- S -/ syntax (name := haveField) "have_field" : tactic
/- S -/ syntax (name := applyField) "apply_field" : tactic
/- S -/ syntax (name := hGeneralize) "h_generalize " atomic(binderIdent " : ")? term:51 " = " ident
  (" with " binderIdent)? : tactic
/- S -/ syntax (name := hGeneralize!) "h_generalize! " atomic(binderIdent " : ")?
  term:51 " = " ident (" with " binderIdent)? : tactic
/- S -/ syntax (name := extractGoal) "extract_goal" (ppSpace ident)?
  (" with" (ppSpace (colGt ident))*)? : tactic
/- S -/ syntax (name := extractGoal!) "extract_goal!" (ppSpace ident)?
  (" with" (ppSpace (colGt ident))*)? : tactic
/- S -/ syntax (name := revertDeps) "revert_deps" (ppSpace colGt ident)* : tactic
/- S -/ syntax (name := revertAfter) "revert_after " ident : tactic
/- S -/ syntax (name := revertTargetDeps) "revert_target_deps" : tactic
/- E -/ syntax (name := clearValue) "clear_value" (ppSpace colGt ident)* : tactic

/- M -/ syntax (name := applyAssumption) "apply_assumption" : tactic

/- S -/ syntax (name := hint) "hint" : tactic

/- B -/ syntax (name := choose) "choose" (ppSpace colGt ident)+ (" using " term)? : tactic
/- B -/ syntax (name := choose!) "choose!" (ppSpace colGt ident)+ (" using " term)? : tactic

/- N -/ syntax (name := congr') "congr" (ppSpace colGt num)?
  (" with " (colGt rcasesPat)* (" : " num)?)? : tactic
/- M -/ syntax (name := rcongr) "rcongr" (ppSpace colGt rcasesPat)* : tactic
/- E -/ syntax (name := convert) "convert " "← "? term (" using " num)? : tactic
/- E -/ syntax (name := convertTo) "convert_to " term (" using " num)? : tactic
/- E -/ syntax (name := acChange) "ac_change " term (" using " num)? : tactic

/- S -/ syntax (name := rcases?) "rcases?" casesTarget,* (" : " num)? : tactic
/- S -/ syntax (name := rintro?) "rintro?" (" : " num)? : tactic

/- M -/ syntax (name := decide!) "decide!" : tactic

/- M -/ syntax (name := deltaInstance) "delta_instance" (ppSpace ident)* : tactic

/- S -/ syntax (name := elide) "elide " num (ppSpace location)? : tactic
/- S -/ syntax (name := unelide) "unelide" (ppSpace location)? : tactic

/- S -/ syntax (name := clarify) "clarify" (config)?
  (Parser.Tactic.simpArgs)? (" using " term,+)? : tactic
/- S -/ syntax (name := safe) "safe" (config)?
  (Parser.Tactic.simpArgs)? (" using " term,+)? : tactic
/- S -/ syntax (name := finish) "finish" (config)?
  (Parser.Tactic.simpArgs)? (" using " term,+)? : tactic

syntax generalizesArg := (ident " : ")? term:51 " = " ident
/- M -/ syntax (name := generalizes) "generalizes " "[" generalizesArg,* "]" : tactic

/- M -/ syntax (name := generalizeProofs) "generalize_proofs"
  (ppSpace (colGt binderIdent))* (ppSpace location)? : tactic

syntax withPattern := "-" <|> "_" <|> ident
/- S -/ syntax (name := cases'') "cases''" casesTarget (" with " (colGt withPattern)+)? : tactic
syntax fixingClause := " fixing" (" *" <|> (ppSpace ident)+)
syntax generalizingClause := " generalizing" (ppSpace ident)+
/- S -/ syntax (name := induction'') "induction''" casesTarget
  (fixingClause <|> generalizingClause)? (" with " (colGt withPattern)+)? : tactic

syntax termList := " [" term,* "]"
/- B -/ syntax (name := itauto) "itauto" (" *" <|> termList)? : tactic
/- B -/ syntax (name := itauto!) "itauto!" (" *" <|> termList)? : tactic

/- B -/ syntax (name := lift) "lift " term " to " term
  (" using " term)? (" with " binderIdent+)? : tactic

/- B -/ syntax (name := obviously) "obviously" : tactic

/- S -/ syntax (name := prettyCases) "pretty_cases" : tactic

/- M -/ syntax (name := assocRw) "assoc_rw " rwRuleSeq (ppSpace location)? : tactic

/- N -/ syntax (name := dsimpResult) "dsimp_result "
  (&"only ")? (dsimpArgs)? " => " tacticSeq : tactic
/- N -/ syntax (name := simpResult) "simp_result "
  (&"only ")? (simpArgs)? " => " tacticSeq : tactic

/- M -/ syntax (name := splitIfs) "split_ifs" (ppSpace location)? (" with " binderIdent+)? : tactic

/- S -/ syntax (name := suggest) "suggest" (config)? (ppSpace num)?
  (simpArgs)? (" using " (colGt binderIdent)+)? : tactic

/- B -/ syntax (name := tauto) "tauto" (config)? : tactic
/- B -/ syntax (name := tauto!) "tauto!" (config)? : tactic

/- M -/ syntax (name := truncCases) "trunc_cases " term (" with " (colGt binderIdent)+)? : tactic

/- E -/ syntax (name := applyNormed) "apply_normed " term : tactic

/- E -/ syntax (name := abel1) "abel1" : tactic
/- E -/ syntax (name := abel1!) "abel1!" : tactic
/- B -/ syntax (name := abel) "abel" (ppSpace (&"raw" <|> &"term"))? (ppSpace location)? : tactic
/- B -/ syntax (name := abel!) "abel!" (ppSpace (&"raw" <|> &"term"))? (ppSpace location)? : tactic

/- E -/ syntax (name := ring1) "ring1" : tactic
/- E -/ syntax (name := ring1!) "ring1!" : tactic

syntax ringMode := &"SOP" <|> &"raw" <|> &"horner"
/- E -/ syntax (name := ringNF) "ring_nf" (ppSpace ringMode)? (ppSpace location)? : tactic
/- E -/ syntax (name := ringNF!) "ring_nf!" (ppSpace ringMode)? (ppSpace location)? : tactic
/- E -/ syntax (name := ring!) "ring!" : tactic

/- B -/ syntax (name := ringExpEq) "ring_exp_eq" : tactic
/- B -/ syntax (name := ringExpEq!) "ring_exp_eq!" : tactic
/- B -/ syntax (name := ringExp) "ring_exp" (ppSpace location)? : tactic
/- B -/ syntax (name := ringExp!) "ring_exp!" (ppSpace location)? : tactic

/- E -/ syntax (name := noncommRing) "noncomm_ring" : tactic

syntax nameAndTerm := term:71 " * " term:66
/- M -/ syntax (name := linearCombination) "linear_combination" (config)?
  sepBy(atomic(nameAndTerm) <|> term:66, " + ") : tactic

/- B -/ syntax (name := linarith) "linarith" (config)? (&" only")? (" [" term,* "]")? : tactic
/- B -/ syntax (name := linarith!) "linarith!" (config)? (&" only")? (" [" term,* "]")? : tactic
/- M -/ syntax (name := nlinarith) "nlinarith" (config)? (&" only")? (" [" term,* "]")? : tactic
/- M -/ syntax (name := nlinarith!) "nlinarith!" (config)? (&" only")? (" [" term,* "]")? : tactic

/- S -/ syntax (name := omega) "omega" (&" manual")? (&" nat" <|> &" int")? : tactic

/- M -/ syntax (name := tfaeHave) "tfae_have " (ident " : ")? num (" → " <|> " ↔ " <|> " ← ") num :
  tactic
/- M -/ syntax (name := tfaeFinish) "tfae_finish" : tactic

syntax mono.side := &"left" <|> &"right" <|> &"both"
/- B -/ syntax (name := mono) "mono" "*"? (ppSpace mono.side)?
  (" with " (colGt term),+)? (" using " (colGt simpArg),+)? : tactic

/- B -/ syntax (name := acMono) "ac_mono" ("*" <|> ("^" num))?
  (config)? ((" : " term) <|> (" := " term))? : tactic

/- M -/ syntax (name := applyFun) "apply_fun " term (ppSpace location)? (" using " term)? : tactic

/- M -/ syntax (name := finCases) "fin_cases " ("*" <|> (term,+)) (" with " term)? : tactic

/- M -/ syntax (name := intervalCases) "interval_cases" (ppSpace (colGt term))?
  (" using " term ", " term)? (" with " ident)? : tactic

/- M -/ syntax (name := reassoc) "reassoc" (ppSpace (colGt ident))* : tactic
/- M -/ syntax (name := reassoc!) "reassoc!" (ppSpace (colGt ident))* : tactic
/- M -/ syntax (name := deriveReassocProof) "derive_reassoc_proof" : tactic

/- M -/ syntax (name := sliceLHS) "slice_lhs " num num " => " Conv.convSeq : tactic
/- M -/ syntax (name := sliceRHS) "slice_rhs " num num " => " Conv.convSeq : tactic

/- S -/ syntax (name := subtypeInstance) "subtype_instance" : tactic

/- M -/ syntax (name := group) "group" (ppSpace location)? : tactic

/- M -/ syntax (name := cancelDenoms) "cancel_denoms" (ppSpace location)? : tactic

/- M -/ syntax (name := zify) "zify" (simpArgs)? (ppSpace location)? : tactic

/- S -/ syntax (name := transport) "transport" (ppSpace term)? " using " term : tactic

/- M -/ syntax (name := unfoldCases) "unfold_cases " tacticSeq : tactic

/- M -/ syntax (name := fieldSimp) "field_simp" (config)? (discharger)? (&" only")?
  (Tactic.simpArgs)? (ppSpace location)? : tactic

/- B -/ syntax (name := equivRw) "equiv_rw" (config)? (termList <|> term) (ppSpace location)? :
  tactic
/- B -/ syntax (name := equivRwType) "equiv_rw_type" (config)? term : tactic

/- N -/ syntax (name := nthRw) "nth_rw " num rwRuleSeq (ppSpace location)? : tactic
/- E -/ syntax (name := nthRwLHS) "nth_rw_lhs " num rwRuleSeq (ppSpace location)? : tactic
/- E -/ syntax (name := nthRwRHS) "nth_rw_rhs " num rwRuleSeq (ppSpace location)? : tactic

/- S -/ syntax (name := rwSearch) "rw_search " (config)? rwRuleSeq : tactic
/- S -/ syntax (name := rwSearch?) "rw_search? " (config)? rwRuleSeq : tactic

/- M -/ syntax (name := piInstanceDeriveField) "pi_instance_derive_field" : tactic
/- M -/ syntax (name := piInstance) "pi_instance" : tactic

/- B -/ syntax (name := tidy) "tidy" (config)? : tactic
/- B -/ syntax (name := tidy?) "tidy?" (config)? : tactic

/- B -/ syntax (name := wlog) "wlog" (" (" &"discharger" " := " term ")")?
  (ppSpace (colGt ident))? (" : " term)? (" := " term)? (" using " (ident*),+)? : tactic

/- M -/ syntax (name := elementwise) "elementwise" (ppSpace (colGt ident))* : tactic
/- M -/ syntax (name := elementwise!) "elementwise!" (ppSpace (colGt ident))* : tactic
/- M -/ syntax (name := deriveElementwiseProof) "derive_elementwise_proof" : tactic

/- S -/ syntax (name := mkDecorations) "mk_decorations" : tactic

/- M -/ syntax (name := nontriviality) "nontriviality"
  (ppSpace (colGt term))? (" using " simpArg,+)? : tactic

/- M -/ syntax (name := filterUpwards) "filter_upwards" (termList)?
  (" with" term:max*)? (" using" term)? : tactic

/- E -/ syntax (name := isBounded_default) "isBounded_default" : tactic

/- N -/ syntax (name := opInduction) "op_induction" (ppSpace (colGt term))? : tactic

/- S -/ syntax (name := mvBisim) "mv_bisim" (ppSpace (colGt term))? (" with " binderIdent+)? :
  tactic

/- M -/ syntax (name := continuity) "continuity" (config)? : tactic
/- M -/ syntax (name := continuity!) "continuity!" (config)? : tactic
/- M -/ syntax (name := continuity?) "continuity?" (config)? : tactic
/- M -/ syntax (name := continuity!?) "continuity!?" (config)? : tactic

/- E -/ syntax (name := unitInterval) "unit_interval" : tactic

/- N -/ syntax (name := measurability) "measurability" (config)? : tactic
/- N -/ syntax (name := measurability!) "measurability!" (config)? : tactic
/- N -/ syntax (name := measurability?) "measurability?" (config)? : tactic
/- N -/ syntax (name := measurability!?) "measurability!?" (config)? : tactic
/- M -/ syntax (name := padicIndexSimp) "padic_index_simp" " [" term,* "]" (ppSpace location)? :
  tactic

/- E -/ syntax (name := uniqueDiffWithinAt_Ici_Iic_univ) "uniqueDiffWithinAt_Ici_Iic_univ" : tactic

/- M -/ syntax (name := ghostFunTac) "ghost_fun_tac " term ", " term : tactic
/- M -/ syntax (name := ghostCalc) "ghost_calc" (ppSpace binderIdent)* : tactic
/- M -/ syntax (name := initRing) "init_ring" (" using " term)? : tactic
/- E -/ syntax (name := ghostSimp) "ghost_simp" (simpArgs)? : tactic
/- E -/ syntax (name := wittTruncateFunTac) "witt_truncate_fun_tac" : tactic

/- M -/ @[nolint docBlame] syntax (name := pure_coherence) "pure_coherence" : tactic
/- M -/ @[nolint docBlame] syntax (name := coherence) "coherence" : tactic

namespace Conv

-- https://github.com/leanprover-community/mathlib/issues/2882
/- M -/ syntax (name := applyCongr) "apply_congr" (ppSpace (colGt term))? : conv

/- E -/ syntax (name := normNum1) "norm_num1" : conv
/- E -/ syntax (name := normNum) "norm_num" (simpArgs)? : conv

/- E -/ syntax (name := ringNF) "ring_nf" (ppSpace ringMode)? : conv
/- E -/ syntax (name := ringNF!) "ring_nf!" (ppSpace ringMode)? : conv
/- E -/ syntax (name := ring) "ring" : conv
/- E -/ syntax (name := ring!) "ring!" : conv

/- E -/ syntax (name := ringExp) "ring_exp" : conv
/- E -/ syntax (name := ringExp!) "ring_exp!" : conv

/- M -/ syntax (name := slice) "slice " num num : conv

end Conv
end Tactic

namespace Attr

/- S -/ syntax (name := intro) "intro" : attr
/- S -/ syntax (name := intro!) "intro!" : attr

/- M -/ syntax (name := ext) "ext" (ppSpace ident)? : attr

/- M -/ syntax (name := higherOrder) "higher_order" (ppSpace ident)? : attr
/- S -/ syntax (name := interactive) "interactive" : attr

/- M -/ syntax (name := mkIff) "mk_iff" (ppSpace ident)? : attr

-- TODO: this should be handled in mathport
/- S -/ syntax (name := protectProj) "protect_proj" (&" without" (ppSpace ident)+)? : attr

/- M -/ syntax (name := notationClass) "notation_class" "*"? (ppSpace ident)? : attr

/- M -/ syntax (name := mono) "mono" (ppSpace Tactic.mono.side)? : attr

/- M -/ syntax (name := reassoc) "reassoc" (ppSpace ident)? : attr

/- M -/ syntax (name := elementwise) "elementwise" (ppSpace ident)? : attr

end Attr

namespace Command

/- N -/ syntax (name := copyDocString) "copy_doc_string " ident " → " ident+ : command
/- N -/ syntax (name := addTacticDoc) (docComment)? "add_tactic_doc " term : command
/- N -/ syntax (name := addDeclDoc) docComment "add_decl_doc " ident : command

/- S -/ syntax (name := setupTacticParser) "setup_tactic_parser" : command
/- N -/ syntax (name := mkSimpAttribute) "mk_simp_attribute " ident
  (" from" (ppSpace ident)+)? (" := " str)? : command

/- M -/ syntax (name := addHintTactic) "add_hint_tactic " tactic : command

/- S -/ syntax (name := explode) "#explode " ident : command

syntax (name := localized) "localized " "[" ident "] " command : command
macro_rules
  | `(localized [$ns] notation $[$prec:precedence]? $[$n:namedName]? $[$prio:namedPrio]?
       $sym => $t) =>
    let ns := mkIdentFrom ns <| rootNamespace ++ ns.getId
    `(with_weak_namespace $ns
      scoped notation $[$prec:precedence]? $[$n:namedName]? $[$prio:namedPrio]? $sym => $t)
  | `(localized [$ns] $_:attrKind $mixfixKind $prec:precedence $[$n:namedName]? $[$prio:namedPrio]?
       $sym => $t) =>
    let ns := mkIdentFrom ns <| rootNamespace ++ ns.getId
    `(with_weak_namespace $ns
      scoped $mixfixKind $prec:precedence $[$n:namedName]? $[$prio:namedPrio]? $sym => $t)
  | `(localized [$ns] attribute [$attr:attr] $ids*) =>
    let ns := mkIdentFrom ns <| rootNamespace ++ ns.getId
    `(with_weak_namespace $ns attribute [scoped $attr:attr] $ids*)

/- S -/ syntax (name := listUnusedDecls) "#list_unused_decls" : command
/- M -/ syntax (name := mkIffOfInductiveProp) "mk_iff_of_inductive_prop" ident ident : command

/- N -/ syntax (name := defReplacer) "def_replacer " ident Term.optType : command

/- S -/ syntax (name := simp) "#simp" (&" only")? (Tactic.simpArgs)? " :"? ppSpace term : command

/- S -/ syntax (name := «where») "#where" : command

/- M -/ syntax (name := reassoc_axiom) "reassoc_axiom " ident : command

/- S -/ syntax (name := sample) "#sample " term : command

end Command
