/-
Copyright (c) 2022 Arthur Paulino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino
-/
import Mathlib.Tactic.Have

example : Nat := by
  have h : Nat
  exact 5
  exact h

example : Nat := by
  have : Nat
  · exact 5
  exact this

example {a : Nat} : a = a := by
  have h : a = a
  · rfl
  exact h

example {a : Nat} : a = a := by
  have : a = a
  · rfl
  exact this

example : True := by
  (let N) -- FIXME: lean4#1670
  exact Nat
  have
  · exact 0
  have h : Nat
  · exact 5
  have h' x : x < x + 1
  · exact Nat.lt.base x
  have h'' (x : Nat) : x < x + 1
  · exact Nat.lt.base x
  let m
  · exact 6
  let m' x (y : Nat) : x + y = y + x
  rw [Nat.add_comm]
  have q
  · exact 6
  simp
