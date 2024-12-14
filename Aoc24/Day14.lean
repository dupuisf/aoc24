import Aoc24.Utils
import Aoc24.Direction

open System Parser

namespace Day14

def testinput1 : FilePath := "input_14_test1"
def testinput2 : FilePath := "input_14_test2"
def realinput : FilePath := "input_14"

/-
PART 1:
-/

-- Real field 101 wide × 103 tall
-- Test: 11 wide × 7 tall

structure Robot where
  pos : Int × Int
  v : Int × Int
deriving Repr, Inhabited, DecidableEq, Hashable

instance : ToString Robot where
  toString r := s!"p={r.pos.1},{r.pos.2} v={r.v.1},{r.v.2}"

def parseRobot : StringParser Robot := do
  let _ ← Char.chars "p="
  let x ← Char.ASCII.parseInt
  let _ ← Char.chars ","
  let y ← Char.ASCII.parseInt
  let _ ← Char.chars " v="
  let vx ← Char.ASCII.parseInt
  let _ ← Char.chars ","
  let vy ← Char.ASCII.parseInt
  return ⟨⟨x, y⟩, ⟨vx, vy⟩⟩

def moveRobot (r : Robot) (steps : Int) (width height : Nat) : Robot :=
  let nx := (r.pos.1 + steps * r.v.1) % width
  let ny := (r.pos.2 + steps * r.v.2) % height
  ⟨⟨nx, ny⟩, r.v⟩

def findQuadrant (r : Robot) (w h : Nat) : Option Nat :=
  let xmid := w / 2
  let ymid := h / 2
  if r.pos.1 < xmid ∧ r.pos.2 < ymid then some 0
  else if r.pos.1 > xmid ∧ r.pos.2 < ymid then some 1
  else if r.pos.1 < xmid ∧ r.pos.2 > ymid then some 2
  else if r.pos.1 > xmid ∧ r.pos.2 > ymid then some 3
  else none

def firstPart (input : FilePath) (w h : Nat) : IO Nat := do
  let raw := (← IO.FS.lines input).map (·.yoloParse parseRobot)
  let moved := raw.map fun r => moveRobot r 100 w h
  let quadrants := moved.map fun r => findQuadrant r w h
  let q0 := quadrants.foldl (init := 0) fun sum r => if r == some 0 then sum + 1 else sum
  let q1 := quadrants.foldl (init := 0) fun sum r => if r == some 1 then sum + 1 else sum
  let q2 := quadrants.foldl (init := 0) fun sum r => if r == some 2 then sum + 1 else sum
  let q3 := quadrants.foldl (init := 0) fun sum r => if r == some 3 then sum + 1 else sum
  return q0*q1*q2*q3

--#eval firstPart testinput1 11 7           --(ans: )
--#eval firstPart realinput 101 103           --(ans: )

/-
PART 2:
-/

def printGrid (robots : Array Robot) : IO Unit := do
  let mut grid : Vector₂ Char 103 101 := .mkVector₂ 103 101 '.'
  for r in robots do
    grid := grid.setIfInBounds r.pos.2 r.pos.1 '#'
  for hy : y in [:103] do
    IO.println (String.ofCharArray grid[y].1)

def secondPart (input : FilePath) : IO Nat := do
  let raw := (← IO.FS.lines input).map (·.yoloParse parseRobot)
  for i in [:(101*103)] do
    let moved := raw.map fun r => moveRobot r i 101 103
    let quadrants := moved.map fun r => findQuadrant r 101 103
    let q0 := quadrants.foldl (init := 0) fun sum r => if r == some 0 then sum + 1 else sum
    let q1 := quadrants.foldl (init := 0) fun sum r => if r == some 1 then sum + 1 else sum
    let q2 := quadrants.foldl (init := 0) fun sum r => if r == some 2 then sum + 1 else sum
    let q3 := quadrants.foldl (init := 0) fun sum r => if r == some 3 then sum + 1 else sum
    let prod := q0*q1*q2*q3
    if prod < 100000000 then
      IO.println s!"==================== i = {i} ========================= prod = {prod}"
      IO.println ""
      printGrid moved
      IO.println ""
  return 0

--#eval secondPart testinput1           --(ans: )
--#eval secondPart realinput           --(ans: )

end Day14
