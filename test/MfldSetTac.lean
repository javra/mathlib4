/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Heather Macbeth, Frédéric Dupuis
-/

import Mathlib.Logic.Equiv.LocalEquiv

/-!
This is a test file for the tactic `mfld_set_tac`. Because this tactic applies a simp-set which
mostly contains lemmas in advanced parts of mathlib, it is currently impossible to truly test it
in realistic conditions. Instead, we create stub definitions and lemmas on objects such as
`LocalHomeomorph`, label them with `mfld_simps` and run tests on those.
-/

open Lean Meta Elab Tactic

/-! ## Syntax of objects and lemmas needed for testing `MfldSetTac` -/
section stub_lemmas

@[mfld_simps] lemma Set.mem_set_of_eq {p : α → Prop} : (x ∈ {y : α | p y}) = p x := sorry

@[mfld_simps] lemma Set.inter_univ (a : Set α) : a ∩ Set.univ = a := sorry

@[mfld_simps] theorem Set.mem_inter_eq (x : α) (a b : Set α) : (x ∈ a ∩ b) = (x ∈ a ∧ x ∈ b) :=
sorry

def Set.preimage (f : α → β) (s : Set β) : Set α := {x | f x ∈ s}

@[mfld_simps] lemma Set.preimage_univ {f : α → β} : Set.preimage f Set.univ = Set.univ := sorry

@[mfld_simps] theorem Set.mem_preimage {f : α → β} : (a ∈ Set.preimage f s) ↔ (f a ∈ s) := sorry

@[mfld_simps] theorem Set.preimage_inter {f : α → β} {s t : Set β} :
  (Set.preimage f (s ∩ t)) = Set.preimage f s ∩ Set.preimage f t :=
sorry

structure LocalEquiv (α : Type u) (β : Type u) :=
(source      : Set α)
(target      : Set β)

instance : CoeFun (LocalEquiv α β) fun _ => α → β := sorry

@[mfld_simps] theorem LocalEquiv.map_source (e : LocalEquiv α β) (h : x ∈ e.source) :
  e x ∈ e.target :=
sorry

def LocalEquiv.symm (e : LocalEquiv α β) : LocalEquiv β α := sorry

@[mfld_simps] theorem LocalEquiv.symm_source (e : LocalEquiv α β) : e.symm.source = e.target :=
sorry

@[mfld_simps] lemma LocalEquiv.left_inv (e : LocalEquiv α β) (h : x ∈ e.source) :
  e.symm (e x) = x :=
sorry

def LocalEquiv.trans (e : LocalEquiv α β) (e' : LocalEquiv β γ) : LocalEquiv α γ := sorry

@[mfld_simps] theorem LocalEquiv.trans_source (e : LocalEquiv α β) (e' : LocalEquiv β γ) :
  (e.trans e').source = (e.source ∩ Set.preimage e e'.source) :=
sorry

@[mfld_simps] lemma LocalEquiv.coe_trans (e : LocalEquiv α β) (e' : LocalEquiv β γ) :
  (e.trans e' : α → γ) = (e' : β → γ) ∘ e :=
sorry

@[mfld_simps] lemma LocalEquiv.coe_trans_symm (e : LocalEquiv α β) (e' : LocalEquiv β γ) :
  ((e.trans e').symm : γ → α) = (e.symm : β → α) ∘ e'.symm :=
sorry

structure LocalHomeomorph (α : Type u) (β : Type u) extends LocalEquiv α β

instance LocalHomeomorph.has_coe_to_fun : CoeFun (LocalHomeomorph α β) (λ _ => α → β) := sorry

def LocalHomeomorph.symm (e : LocalHomeomorph α β) : LocalHomeomorph β α := sorry

@[mfld_simps] lemma LocalHomeomorph.left_inv (e : LocalHomeomorph α β) {x : α}
  (h : x ∈ e.toLocalEquiv.source) :
  e.symm (e x) = x :=
sorry

@[mfld_simps] theorem LocalHomeomorph.symm_to_LocalEquiv (e : LocalHomeomorph α β) :
  e.symm.toLocalEquiv = e.toLocalEquiv.symm :=
sorry

@[mfld_simps] lemma LocalHomeomorph.coe_coe (e : LocalHomeomorph α β) :
  (e.toLocalEquiv : α → β) = e :=
sorry

@[mfld_simps] lemma LocalHomeomorph.coe_coe_symm (e : LocalHomeomorph α β) :
  (e.toLocalEquiv.symm : β → α) = (e.symm : β → α) :=
sorry

structure ModelWithCorners (𝕜 E H : Type u) extends LocalEquiv H E :=
(source_eq : source = Set.univ)

attribute [mfld_simps] ModelWithCorners.source_eq

def ModelWithCorners.symm (I : ModelWithCorners 𝕜 E H) : LocalEquiv E H := sorry

instance ModelWithCorners.has_coe_to_fun : CoeFun (ModelWithCorners 𝕜 E H) (λ _ => H → E) := sorry

@[mfld_simps] lemma ModelWithCorners.left_inv (I : ModelWithCorners 𝕜 E H) (x : H) :
  I.symm (I x) = x :=
sorry

@[mfld_simps] lemma ModelWithCorners.to_local_equiv_coe (I : ModelWithCorners 𝕜 E H) :
  (I.toLocalEquiv : H → E) = I :=
sorry

@[mfld_simps] lemma ModelWithCorners.to_local_equiv_coe_symm (I : ModelWithCorners 𝕜 E H) :
  (I.toLocalEquiv.symm : E → H) = I.symm :=
sorry

end stub_lemmas


/-! ## Tests for `MfldSetTac` -/
section tests

example (e : LocalEquiv α β) (e' : LocalEquiv β γ) :
  (e.trans e').source = e.source ∩ Set.preimage e (e.target ∩ e'.source) := by
  mfld_set_tac

example (e : LocalEquiv α β) : (e.trans e.symm).source = e.source := by mfld_set_tac

example (s : Set α) (f : LocalHomeomorph α β) :
  f.symm.toLocalEquiv.source ∩ (f.toLocalEquiv.target ∩ Set.preimage f.symm s)
  = f.symm.toLocalEquiv.source ∩ Set.preimage f.symm s := by mfld_set_tac

example
  {I : ModelWithCorners 𝕜 E H}
  {I' : ModelWithCorners 𝕜 E' H'}
  {I'' : ModelWithCorners 𝕜 E'' H''}
  (e₁ : LocalHomeomorph M H)
  (e₂ : LocalHomeomorph M' H')
  (e₃ : LocalHomeomorph M'' H'')
  {f : M → M'}
  {g : M' → M''} :
  (Set.preimage (f ∘ ((e₁.toLocalEquiv.trans I.toLocalEquiv).symm))
      (e₂.toLocalEquiv.trans I'.toLocalEquiv).source) ⊆
    {y : E |
    ((e₃.toLocalEquiv.trans I''.toLocalEquiv) ∘
          (g ∘ f) ∘ ((e₁.toLocalEquiv.trans I.toLocalEquiv).symm)) y
    = (((e₃.toLocalEquiv.trans I''.toLocalEquiv : M'' → E'') ∘
             g ∘ ((e₂.toLocalEquiv.trans I'.toLocalEquiv).symm)) ∘
          (e₂.toLocalEquiv.trans I'.toLocalEquiv : M' → E') ∘
            f ∘ ((e₁.toLocalEquiv.trans I.toLocalEquiv).symm)) y} := by
  mfld_set_tac

end tests
