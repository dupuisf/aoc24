import Aoc24.Utils
import Aoc24.Direction

open System Parser

namespace Day06

def testinput1 : FilePath := "input_06_test1"
def testinput2 : FilePath := "input_06_test2"
def realinput : FilePath := "input_06"

/-
PART 1:
-/

-- Input was padded manually with `O`'s on all four sides

instance : HAdd (Nat × Nat) NSEW (Nat × Nat) where
  hAdd pos dir := match dir with
                  | .n => ⟨pos.1 - 1, pos.2⟩
                  | .s => ⟨pos.1 + 1, pos.2⟩
                  | .e => ⟨pos.1, pos.2 + 1⟩
                  | .w => ⟨pos.1, pos.2 - 1⟩

structure WalkData where
  grid : Array₂ Char
  visited : Std.HashSet (Nat × Nat × NSEW)

def getGrid : StateM WalkData (Array₂ Char) := do
  let ⟨grid, _⟩ ← get
  return grid

def wasVisited (pos : Nat × Nat) (dir : NSEW) : StateM WalkData Bool := do
  let ⟨_, v⟩ ← get
  if v.contains ⟨pos.1, pos.2, dir⟩ then return true else return false

def visit (pos : Nat × Nat) (dir : NSEW) : StateM WalkData Unit := do
  let ⟨grid, v⟩ ← get
  let newv := v.insert ⟨pos.1, pos.2, dir⟩
  set (σ := WalkData) ⟨grid, newv⟩

def findGuard (grid : Array₂ Char) : Nat × Nat := Id.run do
  for hi : i in [:grid.size] do
    for hj : j in [:grid[i].size] do
      if grid[i][j] = '^' then return ⟨i, j⟩
  panic! "Can't find the guard"

/-- Return `true` if we get stuck in a loop. -/
partial def walk (pos : Nat × Nat) (dir : NSEW) : StateM WalkData Bool := do
  let grid ← getGrid
  if ← wasVisited pos dir then return true
  visit pos dir
  let newpos := pos + dir
  match grid[newpos.1]![newpos.2]! with
  | '.' => walk newpos dir
  | '^' => walk newpos dir
  | '#' => walk pos dir.rotateCW
  | 'O' => return false
  | _   => panic! "Found garbage"

def firstPart (input : FilePath) : IO Nat := do
  let grid := (← IO.FS.lines input).map String.toCharArray      -- read line by line into an array
  let initpos := findGuard grid
  let initWalkData : WalkData := ⟨grid, .empty⟩
  let ⟨_, visited⟩ := (walk initpos .n).runState initWalkData
  let visitedPos : Std.HashSet (Nat × Nat) := visited.fold (init := .empty) fun s ⟨y, x, _⟩ =>
    s.insert ⟨y, x⟩
  return visitedPos.size

--#eval firstPart testinput1           --(ans: )
--#eval firstPart realinput           --(ans: )

/-
PART 2:
-/

def secondPart (input : FilePath) : IO Nat := do
  let grid := (← IO.FS.lines input).map String.toCharArray      -- read line by line into an array
  let initpos := findGuard grid
  let ⟨_, visited⟩ := (walk initpos .n).runState ⟨grid, .empty⟩
  let firstWalkVisitedPos : Std.HashSet (Nat × Nat) := visited.fold (init := .empty) fun s ⟨y, x, _⟩ =>
    s.insert ⟨y, x⟩
  let mut cnt := 0
  for ⟨i, j⟩ in firstWalkVisitedPos do
    if ⟨i, j⟩ ≠ initpos then
      let trialGrid := grid.set₂ i j '#'
      let initWalkData : WalkData := ⟨trialGrid, .empty⟩
      let isLoop : Bool := (walk initpos .n).run' initWalkData
      if isLoop then
        cnt := cnt + 1
  return cnt

--#eval secondPart testinput1           --(ans: )
--#eval secondPart realinput           --(ans: )

end Day06
