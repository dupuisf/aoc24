import Aoc24.Utils

open System Parser

namespace Day05

def testinput1 : FilePath := "input_05_test1"
def testinput2 : FilePath := "input_05_test2"
def realinput : FilePath := "input_05"

/-
PART 1:
-/

def parseRule : StringParser (Nat × Nat) := do
  let x ← Char.ASCII.parseNat
  let _ ← Char.char '|'
  let y ← Char.ASCII.parseNat
  return ⟨x, y⟩

def parseUpdate : StringParser (Array Nat) := do
  let x ← Char.ASCII.parseNat
  let _ ← Char.char ','
  let tail ← sepBy (Char.char ',') Char.ASCII.parseNat
  return #[x] ++ tail

def validUpdate (upd : Array Nat) (rules : Std.HashMap Nat (Array Nat)) : Bool := Id.run do
  for hi : i in [:upd.size] do
    for hj : j in [i+1:upd.size] do
      let some bs := rules[upd[j]]? | continue
      if bs.contains upd[i] then return false
  return true

def firstPart (input : FilePath) : IO Nat := do
  let rawdata := (← IO.FS.lines input)      -- read line by line into an array
  let rules : Std.HashMap Nat (Array Nat) :=
    (rawdata.filterMap (String.parse? · parseRule)).foldl (init := .empty) fun hm rule =>
      hm.push rule.1 rule.2
  let updates := rawdata.filterMap (String.parse? · parseUpdate)
  let middlepages := updates.filterMap fun upd =>
    if validUpdate upd rules then some upd[upd.size / 2]! else none
  return middlepages.sum

--#eval firstPart testinput1           --(ans: )
--#eval firstPart realinput           --(ans: )

/-
PART 2:
-/

structure TopoData where
  sorted : List Nat
  visited : Std.HashSet Nat
  included : Array Nat

def visit (v : Nat) : StateM TopoData Unit := do
  let ⟨s, visited, incl⟩ ← get
  set (σ := TopoData) ⟨s, visited.insert v, incl⟩

def addNode (v : Nat) : StateM TopoData Unit := do
  let ⟨s, visited, incl⟩ ← get
  set (σ := TopoData) ⟨v :: s, visited, incl⟩

def isExcluded (v : Nat) : StateM TopoData Bool := do
  let ⟨_, visited, incl⟩ ← get
  return visited.contains v || !incl.contains v

partial def topoSortWithStart (rules : Std.HashMap Nat (Array Nat)) (v : Nat) : StateM TopoData Unit := do
  if (← isExcluded v) then return
  visit v
  let ws := match rules[v]? with
            | none => #[]
            | some a => a
  for w in ws do
    topoSortWithStart rules w
  addNode v

def topoSort (rules : Std.HashMap Nat (Array Nat)) : StateM TopoData (List Nat) := do
  rules.foldM (init := ⟨⟩) fun _ orig _ => topoSortWithStart rules orig
  return (← get).sorted

def secondPart (input : FilePath) : IO Nat := do
  let rawdata := (← IO.FS.lines input)      -- read line by line into an array
  let rules : Std.HashMap Nat (Array Nat) :=
    (rawdata.filterMap (String.parse? · parseRule)).foldl (init := .empty) fun hm rule =>
      hm.push rule.1 rule.2
  let updates := rawdata.filterMap (String.parse? · parseUpdate)
  let invalidUpdates := updates.filter fun upd => !validUpdate upd rules
  let filtered := invalidUpdates.map fun upd =>
    ((topoSort rules).run ⟨[], .empty, upd⟩).2.sorted
  let middle := filtered.map fun upd => upd[upd.length / 2]!
  return middle.sum

--#eval secondPart testinput1           --(ans: )
--#eval secondPart realinput           --(ans: )

end Day05
