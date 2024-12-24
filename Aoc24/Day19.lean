import Aoc24.Utils

-- https://www.dorais.org/lean4-parser/doc/

open System Parser

namespace Day19

def testinput1 : FilePath := "input_19_test1"
def testinput2 : FilePath := "input_19_test2"
def realinput : FilePath := "input_19"

/-
PART 1:
-/

def dmatch (p : Array Char) (d : Array Char) (pos : Nat) (hp : pos + p.size ≤ d.size) : Bool := Id.run do
  for hi : i in [:p.size] do
    have hi : i < p.size := Membership.get_elem_helper hi rfl
    if d[i+pos] != p[i] then return false
  return true

def checkDesign (patterns : Vector (Array Char) k) (design : Vector Char n) : Bool := Id.run do
  let mut table : Vector Bool (n + 1) := .ofFn fun x => x == 0
  for hpos : pos in [1:n+1] do
    have hpos_ub : pos < n+1 := Membership.get_elem_helper hpos rfl
    let mut flag := false
    for hi : i in [:k] do
      if h : patterns[i].size ≤ pos then
        if dmatch patterns[i] design.1 (pos - patterns[i].size) (by rw [design.2]; omega) then
          if table[pos - patterns[i].size] then flag := true
    if flag then table := table.set pos true
  return table[n]

def firstPart (input : FilePath) : IO Nat := do
  let raw := (← IO.FS.lines input)
  let some rawpatterns := raw[0]? >>= (·.parse? (sepBy (Char.chars ", ") (takeMany Char.ASCII.alpha))) | IO.exitWithError "Couldn't parse patterns"
  let ⟨_, patterns⟩ := rawpatterns.toVector
  let designs := raw.drop 2 |>.map (·.toCharArray)
  let mut out := 0
  for des in designs do
    let ⟨_, design⟩ := des.toVector
    let t := checkDesign patterns design
    if t then out := out + 1
  return out

--#eval firstPart testinput1           --(ans: )
--#eval firstPart testinput2           --(ans: )
--#eval firstPart realinput           --(ans: )

/-
PART 2:
-/

def countDesign (patterns : Vector (Array Char) k) (design : Vector Char n) : Nat := Id.run do
  let mut table : Vector Nat (n + 1) := .ofFn fun x => if x == 0 then 1 else 0
  for hpos : pos in [1:n+1] do
    have hpos_ub : pos < n+1 := Membership.get_elem_helper hpos rfl
    let mut acc := 0
    for hi : i in [:k] do
      if h : patterns[i].size ≤ pos then
        if dmatch patterns[i] design.1 (pos - patterns[i].size) (by rw [design.2]; omega) then
          acc := acc + table[pos - patterns[i].size]
    table := table.set pos acc
  return table[n]

def secondPart (input : FilePath) : IO Nat := do
  let raw := (← IO.FS.lines input)
  let some rawpatterns := raw[0]? >>= (·.parse? (sepBy (Char.chars ", ") (takeMany Char.ASCII.alpha))) | IO.exitWithError "Couldn't parse patterns"
  let ⟨_, patterns⟩ := rawpatterns.toVector
  let designs := raw.drop 2 |>.map (·.toCharArray)
  let mut out := 0
  for des in designs do
    let ⟨_, design⟩ := des.toVector
    let t := countDesign patterns design
    out := out + t
  return out

--#eval secondPart testinput1           --(ans: )
--#eval secondPart testinput2           --(ans: )
--#eval secondPart realinput           --(ans: )

end Day19
