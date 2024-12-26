import Aoc24.Utils
import Aoc24.Direction
import Aoc24.PriorityQueue

-- https://www.dorais.org/lean4-parser/doc/

open System Parser

namespace Day25

def testinput1 : FilePath := "input_25_test1"
def testinput2 : FilePath := "input_25_test2"
def realinput : FilePath := "input_25"

/-
PART 1:
-/

-- false => lock, true => key
def parseSchematic : StringParser (Vector Nat 5 × Bool) := do
  let rows : Array (Vector Char 5) ← sepBy Char.ASCII.lf (takeVec 5 (Char.char '.' <|> Char.char '#'))
  let mut cols : Vector Nat 5 := .mkVector _ 0
  for hx : x in [:5] do
    for y in [1:6] do
      if rows[y]![x] == '#' then
        cols := cols.modify x (· + 1)
  if rows[0]! == ⟨#['#', '#', '#', '#', '#'], by simp⟩ then
    -- lock
    return ⟨cols, false⟩
  else if rows[0]! == ⟨#['.', '.', '.', '.', '.'], by simp⟩ then
    -- key
    return ⟨cols, true⟩
  else throwUnexpected

def parseInput : StringParser (Array (Vector Nat 5 × Bool)) := sepBy (Char.ASCII.lf *> Char.ASCII.lf) parseSchematic

@[inline]
def checkMatch (lock : Vector Nat 5) (key : Vector Nat 5) : Bool := Id.run do
  for h : i in [:5] do
    if lock[i] + key[i] > 5 then return false
  return true

def firstPart (input : FilePath) : IO Nat := do
  let some raw := (← IO.FS.readFile input).parse? parseInput | IO.exitWithError "parse error"
  let locks := raw.filterMap fun ⟨r, b⟩ => if !b then some r else none
  let keys := raw.filterMap fun ⟨r, b⟩ => if b then some r else none
  let mut out := 0
  for l in locks do
    for k in keys do
      if checkMatch l k then out := out + 1
  return out

--#eval firstPart testinput1           --(ans: )
--#eval firstPart testinput2           --(ans: )
--#eval firstPart realinput           --(ans: )

/-
PART 2:
-/

--def secondPart (input : FilePath) : IO Nat := do
--  --let raw := (← IO.FS.readFile input)
--  let raw := (← IO.FS.lines input)
--  return 0

--#eval secondPart testinput1           --(ans: )
--#eval secondPart testinput2           --(ans: )
--#eval secondPart realinput           --(ans: )

end Day25
