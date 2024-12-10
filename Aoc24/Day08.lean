import Aoc24.Utils

open System Parser

namespace Day08

def testinput1 : FilePath := "input_08_test1"
def testinput2 : FilePath := "input_08_test2"
def realinput : FilePath := "input_08"

/-
PART 1:
-/

def findAntennas (map : Vector₂ Char n m) : Std.HashMap Char (Array (Nat × Nat)) := Id.run do
  let mut out : Std.HashMap Char (Array (Nat × Nat)) := .empty
  for hi : i in [:n] do
    for hj : j in [:m] do
      let c := map[i][j]
      if c ≠ '.' then out := out.push c ⟨i, j⟩
  return out

def markAntinodes (antennas : Std.HashMap Char (Array (Nat × Nat))) : Vector₂ Bool n m := Id.run do
  let mut out : Vector₂ Bool n m := .mkVector₂ n m false
  for hk : k in antennas.keys do
    for a₁ in antennas[k] do
      for a₂ in antennas[k] do
        if a₁ != a₂ then
          let ydiff : Int := (a₂.1 : Int) - a₁.1
          let xdiff : Int := (a₂.2 : Int) - a₁.2
          let y₁ := a₂.1 + ydiff
          let x₁ := a₂.2 + xdiff
          let y₂ := a₁.1 - ydiff
          let x₂ := a₁.2 - xdiff
          out := out.setIfInBounds y₁ x₁ true
          out := out.setIfInBounds y₂ x₂ true
  return out

def firstPart (input : FilePath) : IO Nat := do
  let some ⟨n, m, map⟩ := (← IO.FS.lines input).toCharGrid | panic! "problem"
  let antennas := findAntennas map
  let antinodes : Vector₂ Bool n m := markAntinodes antennas
  let mut cnt := 0
  for hi : i in [:n] do
    for hj : j in [:m] do
      if antinodes[i][j] then cnt := cnt + 1
  return cnt

--#eval firstPart testinput1           --(ans: )
--#eval firstPart realinput           --(ans: )

/-
PART 2:
-/

def markAntinodes2 (antennas : Std.HashMap Char (Array (Nat × Nat))) : Vector₂ Bool n m := Id.run do
  let mut out : Vector₂ Bool n m := .mkVector₂ n m false
  for hk : k in antennas.keys do
    for a₁ in antennas[k] do
      for a₂ in antennas[k] do
        if a₁ != a₂ then
          -- Only works because the input is 50*50
          for i in [:100] do
            let m : Int := (i : Int) - 50
            let ydiff : Int := (a₂.1 : Int) - a₁.1
            let xdiff : Int := (a₂.2 : Int) - a₁.2
            let y₁ := a₂.1 + m * ydiff
            let x₁ := a₂.2 + m * xdiff
            let y₂ := a₁.1 - m * ydiff
            let x₂ := a₁.2 - m * xdiff
            out := out.setIfInBounds y₁ x₁ true
            out := out.setIfInBounds y₂ x₂ true
  return out

def secondPart (input : FilePath) : IO Nat := do
  let some ⟨n, m, map⟩ := (← IO.FS.lines input).toCharGrid | panic! "problem"
  let antennas := findAntennas map
  let antinodes : Vector₂ Bool n m := markAntinodes2 antennas
  let mut cnt := 0
  for hi : i in [:n] do
    for hj : j in [:m] do
      if antinodes[i][j] then cnt := cnt + 1
  return cnt

--#eval secondPart testinput1           --(ans: )
--#eval secondPart realinput           --(ans: )

end Day08
