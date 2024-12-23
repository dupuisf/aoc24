import Aoc24.Utils
import Aoc24.Direction
import Aoc24.PriorityQueue

-- https://www.dorais.org/lean4-parser/doc/

open System Parser

namespace Day22

def testinput1 : FilePath := "input_22_test1"
def testinput2 : FilePath := "input_22_test2"
def realinput : FilePath := "input_22"

-- input: 2474 numbers

/-
PART 1:
-/

@[inline]
def nextSecret (s : UInt64) : UInt64 := Id.run do
  let mut out := s
  out := ((out <<< 6) ^^^ out) &&& 16777215
  out := ((out >>> 5) ^^^ out) &&& 16777215
  out := ((out <<< 11) ^^^ out) &&& 16777215
  return out

@[inline]
def iterateSecret (s : UInt64) (it : Nat) : UInt64 := Id.run do
  let mut s' := s
  for _ in [:it] do
    s' := nextSecret s'
  return s'

def firstPart (input : FilePath) : IO Nat := do
  let initSecrets := (← IO.FS.lines input).map (·.toNat!.toUInt64)
  let outputs := initSecrets.map (iterateSecret · 2000) |>.map UInt64.toNat
  return outputs.sum

--#eval firstPart testinput1           --(ans: )
--#eval firstPart testinput2           --(ans: )
--#eval firstPart realinput           --(ans: )

/-
PART 2:
-/

@[inline]
def getReg (x : UInt64) (id : UInt64) : Int8 :=
  ⟨((x >>> (id*8)) &&& 255).toUInt8⟩

def secondPart (input : FilePath) : IO Nat := do
  let secrets := (← IO.FS.lines input).map (·.toNat!.toUInt64)
  let mut table : Std.HashMap (UInt64 × UInt8) UInt64 := .empty
  for s in secrets do
    let mut s' := s
    let mut latestdiffs : UInt64 := 0
    let mut latestvals : UInt64 := 0
    let mut seen : Std.HashSet UInt64 := .empty
    for i in [:2000] do
      s' := nextSecret s'
      let digit : UInt8 := (s' % 10).toUInt8
      let sdigit : Int8 := ⟨digit⟩
      latestvals := ((latestvals <<< 8) ^^^ digit.toUInt64) &&& 4294967295   -- i.e. 2^32 - 1
      latestdiffs := ((latestdiffs <<< 8) ^^^ (sdigit - getReg latestvals 1).1.toUInt64) &&& 4294967295
      if i ≥ 3 && !seen.contains latestdiffs then
        seen := seen.insert latestdiffs
        table := table.insertOrModify ⟨latestdiffs, digit⟩ (· + 1) 1

  let mut table2 : Std.HashMap UInt64 UInt64 := .empty
  for k in table.keys do
    let ⟨diffs, bananas⟩ := k
    let times := table[k]!
    table2 := table2.insertOrModify diffs (· + bananas.toUInt64*times) (bananas.toUInt64*times)

  let mut numbananas := 0
  for k in table2.keys do
    if numbananas ≤ table2[k]! then numbananas := table2[k]!

  return numbananas.toNat

--#eval secondPart testinput1           --(ans: )
--#eval secondPart testinput2           --(ans: )
--#eval secondPart realinput           --(ans: )

end Day22
