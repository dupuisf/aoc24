import Aoc24.Utils
import Aoc24.Direction

open System Parser

namespace Day10

def testinput1 : FilePath := "input_10_test1"
def testinput2 : FilePath := "input_10_test2"
def realinput : FilePath := "input_10"

-- input: 60×60

/-
PART 1:
-/

structure WalkData (n m : Nat) where
  grid : Vector₂ Nat n m
  visited : Std.HashSet (Int × Int)

def getGrid : StateM (WalkData n m) (Vector₂ Nat n m) := do
  let ⟨grid, _⟩ ← get
  return grid

def wasVisited (y x : Int) : StateM (WalkData n m) Bool := do
  let ⟨_, v⟩ ← get
  if v.contains ⟨y, x⟩ then return true else return false

def visit (y x : Int) : StateM (WalkData n m) Unit := do
  let ⟨grid, v⟩ ← get
  let newv := v.insert ⟨y, x⟩
  set (σ := WalkData n m) ⟨grid, newv⟩

partial def walk (y x : Int) (curheight cnt : Nat) : StateM (WalkData n m) Nat := do
  let grid ← getGrid
  if ← wasVisited y x then return cnt
  visit y x
  if curheight = 9 then return 1
  let mut extracnt := 0
  for dir in [NSEW.n, .s, .e, .w] do
    let ⟨newy, newx⟩ := dir.step y x 1
    match grid.get₂? newy newx with
    | none => noop
    | some height =>
      if height = curheight + 1 then
        extracnt := extracnt + (← walk newy newx height cnt)
  return cnt + extracnt

def firstPart (input : FilePath) : IO Nat := do
  let some ⟨n, m, grid⟩ := (← IO.FS.lines input).map (·.toCharArray)
        |>.map (·.map Char.toNatDigit)
        |>.toVector₂ | panic! "not a grid"
  let mut cnt := 0
  for hi : i in [:n] do
    for hj : j in [:m] do
      if grid[i][j] = 0 then
        let walkdata : WalkData n m := ⟨grid, .empty⟩
        let curcnt : Nat := (walk i j 0 0).run' walkdata
        cnt := cnt + curcnt
  return cnt

--#eval firstPart testinput1           --(ans: )
--#eval firstPart testinput2           --(ans: )
--#eval firstPart realinput           --(ans: )

/-
PART 2:
-/

partial def walk₂ (y x : Int) (curheight cnt : Nat) (visited : Std.HashSet (Int × Int)) :
    StateM (WalkData n m) Nat := do
  let grid ← getGrid
  if visited.contains ⟨y, x⟩ then return cnt
  let newvisited := visited.insert ⟨y, x⟩
  if curheight = 9 then return 1
  let mut extracnt := 0
  for dir in [NSEW.n, .s, .e, .w] do
    let ⟨newy, newx⟩ := dir.step y x 1
    match grid.get₂? newy newx with
    | none => noop
    | some height =>
      if height = curheight + 1 then
        extracnt := extracnt + (← walk₂ newy newx height cnt newvisited)
  return cnt + extracnt

def secondPart (input : FilePath) : IO Nat := do
  let some ⟨n, m, grid⟩ := (← IO.FS.lines input).map (·.toCharArray)
        |>.map (·.map Char.toNatDigit)
        |>.toVector₂ | panic! "not a grid"
  let mut cnt := 0
  for hi : i in [:n] do
    for hj : j in [:m] do
      if grid[i][j] = 0 then
        let walkdata : WalkData n m := ⟨grid, .empty⟩
        let curcnt : Nat := (walk₂ i j 0 0 .empty).run' walkdata
        cnt := cnt + curcnt
  return cnt

--#eval secondPart testinput1           --(ans: )
--#eval secondPart testinput2           --(ans: )
--#eval secondPart realinput           --(ans: )

end Day10
