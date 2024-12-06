import Aoc24.Utils
import Parser

open System

namespace Day04

def testinput1 : FilePath := "input_04_test1"
def testinput2 : FilePath := "input_04_test2"
def realinput : FilePath := "input_04"

/-
PART 1:
-/

def getDiagsNESW (as : Array₂ α) : Array₂ α := Id.run do
  let mut out : Array₂ α := #[]
  if h : as.size ≠ 0 then
    for i in [0:as.size + as[as.size-1].size - 1] do
      let mut curline : Array α := #[]
      for j in [0:i+1] do
        if i - j < as.size then
          if hj' : j < as[i-j]!.size then curline := curline.push as[i-j]![j]
      out := out.push curline
  return out

def getDiagsNWSE (as : Array₂ α) : Array₂ α :=
  (getDiagsNESW <| as.map Array.reverse).map Array.reverse

def countXMAS (as : Array Char) : Nat :=
  as.foldlSlidingWinIdx 4 (init := 0) fun cnt win _ => Id.run do
    let mut newcnt := cnt
    if win = #['X', 'M', 'A', 'S'] then newcnt := newcnt + 1
    if win = #['S', 'A', 'M', 'X'] then newcnt := newcnt + 1
    return newcnt

def firstPart (input : FilePath) : IO Nat := do
  let horiz := (← IO.FS.lines input).map String.toCharArray      -- read line by line into an array
  let some vert := horiz.transpose | panic! "merde"
  let diagsNESW := getDiagsNESW horiz
  let diagsNWSE := getDiagsNWSE horiz
  let horizSum := (horiz.map countXMAS).sum
  let vertSum := (vert.map countXMAS).sum
  let diagsNESWSum := (diagsNESW.map countXMAS).sum
  let diagsNWSESum := (diagsNWSE.map countXMAS).sum
  return horizSum + vertSum + diagsNESWSum + diagsNWSESum

--#eval firstPart testinput1           --(ans: )
--#eval firstPart realinput           --(ans: )

/-
PART 2:
-/

def secondPart (input : FilePath) : IO Nat := do
  let grid := (← IO.FS.lines input).map String.toCharArray      -- read line by line into an array
  let rows := grid.size
  let cols := grid[0]!.size
  let mut cnt := 0
  for i in [0:rows-2] do
    for j in [0:cols-2] do
      if grid[i]![j]! == 'M' ∧ grid[i+1]![j+1]! == 'A' ∧ grid[i+2]![j+2]! == 'S' then
        if grid[i+2]![j]! == 'M' ∧ grid[i+1]![j+1]! == 'A' ∧ grid[i]![j+2]! == 'S' then cnt := cnt + 1
        if grid[i+2]![j]! == 'S' ∧ grid[i+1]![j+1]! == 'A' ∧ grid[i]![j+2]! == 'M' then cnt := cnt + 1
      if grid[i]![j]! == 'S' ∧ grid[i+1]![j+1]! == 'A' ∧ grid[i+2]![j+2]! == 'M' then
        if grid[i+2]![j]! == 'M' ∧ grid[i+1]![j+1]! == 'A' ∧ grid[i]![j+2]! == 'S' then cnt := cnt + 1
        if grid[i+2]![j]! == 'S' ∧ grid[i+1]![j+1]! == 'A' ∧ grid[i]![j+2]! == 'M' then cnt := cnt + 1
  return cnt

--#eval secondPart testinput1           --(ans: )
--#eval secondPart realinput           --(ans: )

end Day04
