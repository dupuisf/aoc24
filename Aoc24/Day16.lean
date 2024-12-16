import Aoc24.Utils
import Aoc24.Direction
import Aoc24.PriorityQueue

-- https://www.dorais.org/lean4-parser/doc/

-- input: 141×141

open System Parser

namespace Day16

def testinput1 : FilePath := "input_16_test1"
def testinput2 : FilePath := "input_16_test2"
def realinput : FilePath := "input_16"

/-
PART 1:
-/

structure DijkstraData (n m : Nat) where
  grid : Vector₂ Char n m
  distances : Std.HashMap (Nat × Nat × NSEW) Nat
  queue : PriorityQueue Nat (Nat × Nat × NSEW)

def getGrid : StateM (DijkstraData n m) (Vector₂ Char n m) := do
  let ⟨grid, _, _,⟩ ← get
  return grid

def wasVisited (y x : Nat) (dir : NSEW) : StateM (DijkstraData n m) Bool := do
  let ⟨_, v, _,⟩ ← get
  return v.contains ⟨y, x, dir⟩

def visit (y x : Nat) (dir : NSEW) (dist : Nat) : StateM (DijkstraData n m) Unit := do
  let ⟨g, v, q⟩ ← get
  let v' := v.insert ⟨y, x, dir⟩ dist
  set (σ := DijkstraData n m) ⟨g, v', q⟩

def popQueue : StateM (DijkstraData n m) (Option (Nat × Nat × Nat × NSEW)) := do
  let ⟨g, v, q⟩ ← get
  match q with
  | [] => return none
  | head :: tail =>
      set (σ := DijkstraData n m) ⟨g, v, tail⟩
      return some head

def requeue (prio y x : Nat) (dir : NSEW) : StateM (DijkstraData n m) Unit := do
  let ⟨g, v, q⟩ ← get
  let q' := q.insertOrLowerPriority prio ⟨y, x, dir⟩
  set (σ := DijkstraData n m) ⟨g, v, q'⟩

partial def dijkstra : StateM (DijkstraData n m) Unit := do
  let some ⟨dist, y, x, dir⟩ ← popQueue | return
  visit y x dir dist
  let grid ← getGrid
  let ⟨ny, nx⟩ := dir.step y x 1
  if grid[ny]![nx]! != '#' && !(← wasVisited ny nx dir) then
    requeue (dist + 1) ny nx dir
  for ndir in [dir.rotateCCW, dir.rotateCW] do
    if !(← wasVisited y x ndir) then
      requeue (dist + 1000) y x ndir
  dijkstra

def getMin (l : List (Option Nat)) : Option Nat :=
  l.foldl (init := none) fun cur new =>
    match cur, new with
    | none, _ => new
    | some x, none => some x
    | some x, some y => if x ≤ y then some x else some y

def getDist (distances : Std.HashMap (Nat × Nat × NSEW) Nat) (y x : Nat) : Option (Nat × NSEW) :=
  let dn := distances[(⟨y, x, .n⟩ : Nat × Nat × NSEW)]?
  let ds := distances[(⟨y, x, .s⟩ : Nat × Nat × NSEW)]?
  let de := distances[(⟨y, x, .e⟩ : Nat × Nat × NSEW)]?
  let dw := distances[(⟨y, x, .w⟩ : Nat × Nat × NSEW)]?
  let m := getMin [dn, ds, de, dw]
  match m with
  | none => none
  | some d =>
      if m == dn then some ⟨d, .n⟩
      else if m == ds then some ⟨d, .s⟩
      else if m == de then some ⟨d, .e⟩
      else some ⟨d, .w⟩


def firstPart (input : FilePath) : IO Nat := do
  let raw := (← IO.FS.lines input)
  let some ⟨n, m, grid⟩ := raw.map (·.toCharArray) |>.toVector₂ | IO.exitWithError "parse error";
  let some ⟨sy, sx⟩ := grid.findElem 'S' | IO.exitWithError "Can't find start"
  let some ⟨ey, ex⟩ := grid.findElem 'E' | IO.exitWithError "Can't find end"
  let initdata : DijkstraData n m := ⟨grid, .empty, [⟨0, sy, sx, .e⟩]⟩
  let ⟨_, distances, _⟩ := dijkstra.runState initdata
  let some ⟨d, _⟩ := getDist distances ey ex | IO.exitWithError "did not reach E"
  return d

--#eval firstPart testinput1           --(ans: 7036)
--#eval firstPart testinput2           --(ans: 11048)
--#eval firstPart realinput           --(ans: )

/-
PART 2:
-/

def secondPart (input : FilePath) : IO Nat := do
  let raw := (← IO.FS.lines input)
  let some ⟨n, m, grid⟩ := raw.map (·.toCharArray) |>.toVector₂ | IO.exitWithError "parse error";
  let some ⟨sy, sx⟩ := grid.findElem 'S' | IO.exitWithError "Can't find start"
  let some ⟨ey, ex⟩ := grid.findElem 'E' | IO.exitWithError "Can't find end"
  let initdata₁ : DijkstraData n m := ⟨grid, .empty, [⟨0, sy, sx, .e⟩]⟩
  let ⟨_, distancesFromS, _⟩ := dijkstra.runState initdata₁
  let some ⟨d, dir⟩ := getDist distancesFromS ey ex | IO.exitWithError "did not reach E"
  let initdata₂ : DijkstraData n m := ⟨grid, .empty, [⟨0, ey, ex, dir.reverse⟩]⟩
  let ⟨_, distancesFromE, _⟩ := dijkstra.runState initdata₂
  let mut out := 0
  for y in [:n] do
    for x in [:m] do
      let mut flag := false
      for dir in [NSEW.n, .s, .e, .w] do
        match distancesFromS[(⟨y, x, dir⟩ : Nat × Nat × NSEW)]? with
        | none => noop
        | some dist₁ =>
          match distancesFromE[(⟨y, x, dir.reverse⟩ : Nat × Nat × NSEW)]? with
          | none => noop
          | some dist₂ => if dist₁ + dist₂ == d then flag := true
      if flag then out := out + 1
  return out

--#eval secondPart testinput1           --(ans: )
--#eval secondPart testinput2           --(ans: )
--#eval secondPart realinput           --(ans: )

end Day16
