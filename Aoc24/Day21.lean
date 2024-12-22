import Aoc24.Utils
import Aoc24.Direction

-- https://www.dorais.org/lean4-parser/doc/

open System Parser

namespace Day21

def testinput1 : FilePath := "input_21_test1"
def testinput2 : FilePath := "input_21_test2"
def realinput : FilePath := "input_21"

/-
PART 1:
-/

def numkeypadlist : List (Char × (Nat × Nat)) :=
  [ ⟨'7', ⟨0, 0⟩⟩, ⟨'8', ⟨0, 1⟩⟩, ⟨'9', ⟨0, 2⟩⟩,
    ⟨'4', ⟨1, 0⟩⟩, ⟨'5', ⟨1, 1⟩⟩, ⟨'6', ⟨1, 2⟩⟩,
    ⟨'1', ⟨2, 0⟩⟩, ⟨'2', ⟨2, 1⟩⟩, ⟨'3', ⟨2, 2⟩⟩,
                   ⟨'0', ⟨3, 1⟩⟩, ⟨'A', ⟨3, 2⟩⟩]

def dirkeypadlist : List (Char × (Nat × Nat)) :=
  [                ⟨'^', ⟨0, 1⟩⟩, ⟨'A', ⟨0, 2⟩⟩,
    ⟨'<', ⟨1, 0⟩⟩, ⟨'v', ⟨1, 1⟩⟩, ⟨'>', ⟨1, 2⟩⟩ ]

def numkeypadpos : Std.HashMap Char (Nat × Nat) := .ofList numkeypadlist
def numkeypadkey : Std.HashMap (Nat × Nat) Char := .ofList (numkeypadlist.map Prod.swap)
def dirkeypadpos : Std.HashMap Char (Nat × Nat) := .ofList dirkeypadlist
def dirkeypadkey : Std.HashMap (Nat × Nat) Char := .ofList (dirkeypadlist.map Prod.swap)

def getPaths (positions : Std.HashMap Char (Nat × Nat)) (chars : Std.HashMap (Nat × Nat) Char)
    (src tgt : Char) : Array (Array NSEW) :=
  let dy := (positions[tgt]!.1 : Int) - positions[src]!.1
  let dx := (positions[tgt]!.2 : Int) - positions[src]!.2
  let miny := min positions[src]!.1 positions[tgt]!.1
  let minx := min positions[src]!.2 positions[tgt]!.2
  let maxy := max positions[src]!.1 positions[tgt]!.1
  let convertx (x : Int) : Array NSEW := if x < 0 then Array.mkArray (-x).toNat .w else Array.mkArray x.toNat .e
  let converty (y : Int) : Array NSEW := if y < 0 then Array.mkArray (-y).toNat .n else Array.mkArray y.toNat .s
  if !chars.contains ⟨miny, minx⟩ then
    if dy ≥ 0 then #[converty dy ++ convertx dx]
    else #[convertx dx ++ converty dy]
  else if !chars.contains ⟨maxy, minx⟩ then
    if dy ≥ 0 then #[convertx dx ++ converty dy]
    else #[converty dy ++ convertx dx]
  else
    if dx == 0 || dy == 0 then #[converty dy ++ convertx dx]
    else #[converty dy ++ convertx dx, convertx dx ++ converty dy]

def getPathCost (previousLevel : Std.HashMap (Char × Char) Nat) (path : Array Char) : Nat := Id.run do
  let mut acc := 0
  let mut prev := 'A'
  for btn in path.push 'A' do
    let curcost := previousLevel[(⟨prev, btn⟩ : Char × Char)]!
    acc := acc + curcost
    prev := btn
  return acc

def getCosts (positions : Std.HashMap Char (Nat × Nat)) (chars : Std.HashMap (Nat × Nat) Char)
    (previousLevel : Std.HashMap (Char × Char) Nat) : Std.HashMap (Char × Char) Nat := Id.run do
  let mut out := .empty
  for src in positions.keys do
    for tgt in positions.keys do
      let paths := getPaths positions chars src tgt
      let candidates := paths.map fun path => Id.run do
        let pathchars := path.map fun dir => dir.toChar
        return getPathCost previousLevel pathchars
      out := out.insert ⟨src, tgt⟩ (candidates.foldl (init := 100000000000000000) fun acc cur => min acc cur)
  return out

def levelzero (chars : List Char) : Std.HashMap (Char × Char) Nat := Id.run do
  let mut out := .empty
  for src in chars do
    for tgt in chars do
      out := out.insert ⟨src, tgt⟩ 1
  return out

def firstPart (input : FilePath) : IO Nat := do
  let raw := (← IO.FS.lines input)
  let keycodesnat := raw.map (·.dropRight 1 |>.toNat!)
  let keycodes := raw.map (·.toCharArray)

  let mut levels : Array (Std.HashMap (Char × Char) Nat) := #[levelzero ['>', '^', '<', 'v', 'A']]
  for i in [:2] do
    let prev := levels[i]!
    let newlevel := getCosts dirkeypadpos dirkeypadkey prev
    levels := levels.push newlevel
  let finallevel := getCosts numkeypadpos numkeypadkey levels[levels.size-1]!

  let seqlengths := keycodes.map (fun x => getPathCost finallevel x - 1)
  let answer := keycodesnat.zipWith seqlengths (· * ·) |>.sum
  return answer

--#eval firstPart testinput1           --(ans: )
--#eval firstPart testinput2           --(ans: )
--#eval firstPart realinput           --(ans: )

/-
PART 2:
-/

def secondPart (input : FilePath) : IO Nat := do
  let raw := (← IO.FS.lines input)
  let keycodesnat := raw.map (·.dropRight 1 |>.toNat!)
  let keycodes := raw.map (·.toCharArray)

  let mut levels : Array (Std.HashMap (Char × Char) Nat) := #[levelzero ['>', '^', '<', 'v', 'A']]
  for i in [:25] do
    let prev := levels[i]!
    let newlevel := getCosts dirkeypadpos dirkeypadkey prev
    levels := levels.push newlevel
  let finallevel := getCosts numkeypadpos numkeypadkey levels[levels.size-1]!

  let seqlengths := keycodes.map (fun x => getPathCost finallevel x - 1)
  let answer := keycodesnat.zipWith seqlengths (· * ·) |>.sum
  return answer

--#eval secondPart testinput1           --(ans: )
--#eval secondPart testinput2           --(ans: )
--#eval secondPart realinput           --(ans: )

end Day21
