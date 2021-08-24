/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Scott Morrison
-/
import Mathlib.Tactic.Split
import Mathlib.Tactic.ShowTerm

-- TODO can `show_term` be indenting aware, so we don't have to use braces and semicolons?

example (n : Nat) : Nat × Nat := by
  showTerm
    { split;
      exact n;
      exact 37 }
