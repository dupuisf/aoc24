import Aoc24.Utils
import Aoc24.Direction
import Aoc24.PriorityQueue

-- https://www.dorais.org/lean4-parser/doc/

open System Parser

namespace Day18

def testinput1 : FilePath := "input_18_test1"
def testinput2 : FilePath := "input_18_test2"
def realinput : FilePath := "input_18"

/-
PART 1:
-/

structure DijkstraData (α : Type _) (n m : Nat) where
  grid : Vector₂ α n m
  distances : Std.HashMap (Int × Int) Nat
  queue : PriorityQueue Nat (Int × Int)

def getGrid : StateM (DijkstraData α n m) (Vector₂ α n m) := do
  let ⟨grid, _, _,⟩ ← get
  return grid

def wasVisited (y x : Int) : StateM (DijkstraData α n m) Bool := do
  let ⟨_, v, _,⟩ ← get
  return v.contains ⟨y, x⟩

def visit (y x : Int) (dist : Nat) : StateM (DijkstraData α n m) Unit := do
  let ⟨g, v, q⟩ ← get
  let v' := v.insert ⟨y, x⟩ dist
  set (σ := DijkstraData α n m) ⟨g, v', q⟩

def popQueue : StateM (DijkstraData α n m) (Option (Nat × Int × Int)) := do
  let ⟨g, v, q⟩ ← get
  match q with
  | [] => return none
  | head :: tail =>
      set (σ := DijkstraData α n m) ⟨g, v, tail⟩
      return some head

def requeue (prio : Nat) (y x : Int) : StateM (DijkstraData α n m) Unit := do
  let ⟨g, v, q⟩ ← get
  let q' := q.insertOrLowerPriority prio ⟨y, x⟩
  set (σ := DijkstraData α n m) ⟨g, v, q'⟩

partial def dijkstra : StateM (DijkstraData Bool n n) Unit := do
  let some ⟨dist, y, x⟩ ← popQueue | return
  let ⟨_, v, _⟩ ← get
  visit y x dist
  let grid ← getGrid
  for dir in [NSEW.n, .s, .e, .w] do
    let ⟨ny, nx⟩ := dir.step y x 1
    match ny.toNat', nx.toNat' with
    | none, _ => noop
    | _, none => noop
    | some ny', some nx' =>
        if h : ny' < n ∧ nx' < n then
          if !grid[ny'][nx'] && !(← wasVisited ny' nx') then
            requeue (dist + 1) ny' nx'
  dijkstra

def parseLine : StringParser (Nat × Nat) := do
  let x ← Char.ASCII.parseNat
  let _ ← Char.chars ","
  let y ← Char.ASCII.parseNat
  return ⟨x, y⟩

def printGrid (grid : Vector₂ Bool n n) : IO Unit := do
  IO.print s!"\n"
  for hy : y in [:n] do
    for hx : x in [:n] do
      let c := if grid[y][x] then '#' else '.'
      IO.print s!"{c}"
    IO.print s!"\n"

def firstPart (input : FilePath) (n : Nat) (cap : Nat) : IO Nat := do
  let bytes := (← IO.FS.lines input).map (·.yoloParse parseLine) |>.take cap
  let grid : Vector₂ Bool n n := bytes.foldl (init := .mkVector₂ n n false) fun acc cur =>
    acc.setIfInBounds cur.2 cur.1 true
  --printGrid grid
  let ⟨_, distances, _⟩ := dijkstra.runState ⟨grid, .empty, [⟨0, ⟨0, 0⟩⟩]⟩
  let some ans := distances[(⟨n-1, n-1⟩ : Int × Int)]? | IO.exitWithError "Can't reach bottom right"
  return ans

--#eval firstPart testinput1 7 12           --(ans: )
--#eval firstPart testinput2 71 1024         --(ans: )
--#eval firstPart realinput           --(ans: )

/-
PART 2:
-/

def secondPart (input : FilePath) (n : Nat) (lb : Nat) : IO String := do
  let rawbytes := (← IO.FS.lines input).map (·.yoloParse parseLine)
  let mut ans : Nat × Nat := ⟨0, 0⟩
  let mut finalcap : Nat := 0
  for cap in [lb:rawbytes.size] do
    let bytes := rawbytes.take cap
    let grid : Vector₂ Bool n n := bytes.foldl (init := .mkVector₂ n n false) fun acc cur =>
      acc.setIfInBounds cur.2 cur.1 true
    let ⟨_, distances, _⟩ := dijkstra.runState ⟨grid, .empty, [⟨0, ⟨0, 0⟩⟩]⟩
    match distances[(⟨n-1, n-1⟩ : Int × Int)]? with
    | some _ => noop
    | none =>
      ans := bytes[cap-1]!
      finalcap := cap
      break
  --IO.println finalcap
  --printGrid <| (rawbytes.take finalcap).foldl (init := .mkVector₂ n n false) fun acc cur =>
  --    acc.setIfInBounds cur.2 cur.1 true
  return s!"{ans.1},{ans.2}"

--#eval secondPart testinput1           --(ans: )
--#eval secondPart testinput2           --(ans: )
--#eval secondPart realinput           --(ans: )

end Day18
