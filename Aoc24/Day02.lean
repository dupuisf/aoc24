import Parser

open System

namespace Day02

def testinput1 : FilePath := "input_02_test1"
def testinput2 : FilePath := "input_02_test2"
def realinput : FilePath := "input_02"

/-
PART 1:
-/

def isSlowlyInc : List Nat → Bool
| [] => true
| [_] => true
| x :: y :: xs => if x + 1 ≤ y ∧ y ≤ x + 3 then isSlowlyInc (y :: xs) else false

def isSlowlyDec : List Nat → Bool
| [] => true
| [_] => true
| x :: y :: xs => if y + 1 ≤ x ∧ x ≤ y + 3 then isSlowlyDec (y :: xs) else false

def isSafe (lvl : List Nat) : Bool :=
  isSlowlyInc lvl || isSlowlyDec lvl

def firstPart (input : FilePath) : IO Nat := do
  let rawdata := (← IO.FS.lines input).map String.splitOn
  let reports := rawdata.map (List.map String.toNat!)
  let filtered := reports.filter isSafe
  return filtered.size

--#eval firstPart testinput1           --(ans: 2)
--#eval firstPart realinput           --(ans: 379)

/-
PART 2:
-/

def isApproxSlowlyInc (lvl : List Nat) : Bool := Id.run do
  if isSlowlyInc lvl then return true
  for i in [0:lvl.length] do
    let lvl' := (lvl.take i) ++ (lvl.drop (i + 1))
    if isSlowlyInc lvl' then return true
  return false

def isApproxSlowlyDec (lvl : List Nat) : Bool := Id.run do
  if isSlowlyDec lvl then return true
  for i in [0:lvl.length] do
    let lvl' := (lvl.take i) ++ (lvl.drop (i + 1))
    if isSlowlyDec lvl' then return true
  return false

def isApproxSafe (lvl : List Nat) :=
  isApproxSlowlyInc lvl || isApproxSlowlyDec lvl

def secondPart (input : FilePath) : IO Nat := do
  let rawdata := (← IO.FS.lines input).map String.splitOn
  let reports := rawdata.map (List.map String.toNat!)
  let filtered := reports.filter isApproxSafe
  return filtered.size

--#eval secondPart testinput1           --(ans: 4)
--#eval secondPart realinput           --(ans: 430)

end Day02
