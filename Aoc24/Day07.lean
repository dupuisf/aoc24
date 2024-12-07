import Aoc24.Utils

open System Parser

namespace Day07

def testinput1 : FilePath := "input_07_test1"
def testinput2 : FilePath := "input_07_test2"
def realinput : FilePath := "input_07"

/-
PART 1:
-/

def parseLine : StringParser (Nat × Array Nat) := do
  let test ← Char.ASCII.parseNat
  let _ ← Char.chars ": "
  let nums ← sepBy (Char.char ' ') Char.ASCII.parseNat
  return ⟨test, nums⟩

def checkLine (test : Nat) (nums : List Nat) : Bool :=
  match nums with
  | [] => false
  | [x] => if test = x then true else false
  | x :: tail => Id.run do
      if test % x == 0 then
        if checkLine (test / x) tail then return true
      return checkLine (test - x) tail

def firstPart (input : FilePath) : IO Nat := do
  let rawdata := (← IO.FS.lines input).map (String.yoloParse · parseLine)
  let lists : Array (Nat × (List Nat)) := rawdata.map fun ⟨test, ln⟩ => ⟨test, ln.toList.reverse⟩
  let mut out := 0
  for ln in lists do
    if checkLine ln.1 ln.2 then
      out := out + ln.1
  return out

--#eval firstPart testinput1           --(ans: )
--#eval firstPart realinput           --(ans: )

/-
PART 2:
-/

def log10 (n : Nat) (out : Nat := 0) : Nat :=
  match n with
  | 0 => out
  | k+1 => 1 + log10 ((k+1) / 10)

def checkLine2 (test : Nat) (nums : List Nat) : Bool :=
  match nums with
  | [] => false
  | [x] => if test = x then true else false
  | x :: tail => Id.run do
      if test % x = 0 then
        if checkLine2 (test / x) tail then return true
      let d := log10 x
      if test % (10 ^ d) == x then
        if checkLine2 (test / (10 ^ d)) tail then return true
      return checkLine2 (test - x) tail

def secondPart (input : FilePath) : IO Nat := do
  let rawdata := (← IO.FS.lines input).map (String.yoloParse · parseLine)
  let lists : Array (Nat × (List Nat)) := rawdata.map fun ⟨test, ln⟩ => ⟨test, ln.toList.reverse⟩
  let mut out := 0
  for ln in lists do
    if checkLine2 ln.1 ln.2 then
      out := out + ln.1
  return out

--#eval secondPart testinput1           --(ans: )
--#eval secondPart realinput           --(ans: )

end Day07
