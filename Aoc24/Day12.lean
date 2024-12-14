import Aoc24.Utils
import Aoc24.Direction

open System Parser

namespace Day12

def testinput1 : FilePath := "input_12_test1"
def testinput2 : FilePath := "input_12_test2"
def testinput3 : FilePath := "input_12_test3"
def testinput4 : FilePath := "input_12_test4"
def realinput : FilePath := "input_12"

-- input: 140×140

/-
PART 1:
-/

structure WalkData (n m : Nat) where
  grid : Vector₂ Char n m
  -- ⟨region id, num of neighbors⟩
  visitdata : Std.HashMap (Int × Int) (Nat × Nat)

def getGrid : StateM (WalkData n m) (Vector₂ Char n m) := do
  let ⟨grid, _⟩ ← get
  return grid

def wasVisited (y x : Int) : StateM (WalkData n m) Bool := do
  let ⟨_, v⟩ ← get
  if v.contains ⟨y, x⟩ then return true else return false

def visit (y x : Int) (id : Nat) : StateM (WalkData n m) Unit := do
  let ⟨grid, v⟩ ← get
  let some curchar := grid.get₂? y x | panic! "out of bounds"
  let bordersize := NSEW.fold (init := 0) fun cnt dir =>
    let ⟨ny, nx⟩ := dir.step y x 1
    match grid.get₂? ny nx with
    | none => cnt + 1
    | some nchar => if nchar != curchar then cnt + 1 else cnt
  let newv := v.insert ⟨y, x⟩ ⟨id, bordersize⟩
  set (σ := WalkData n m) ⟨grid, newv⟩

partial def walk (y x : Int) (id : Nat) (letter : Char) : StateM (WalkData n m) Unit := do
  if ← wasVisited y x then return
  if (← getGrid).get₂? y x != some letter then return
  visit y x id
  NSEW.foldM (init := ⟨⟩) fun _ dir =>
    let ⟨ny, nx⟩ := dir.step y x 1
    walk ny nx id letter

def printVisitdata (data : Std.HashMap (Int × Int) (Nat × Nat)) : IO Unit := do
  for hk : k in data.keys do
    IO.println s!"{k} => {data[k]}"

def firstPart (input : FilePath) : IO Nat := do
  let some ⟨n, m, grid⟩ := (← IO.FS.lines input).map (·.toCharArray)
        |>.toVector₂ | panic! "not a grid"
  let initdata : WalkData n m := ⟨grid, .empty⟩
  let mut curid := 0
  let mut visitdata : Std.HashMap (Int × Int) (Nat × Nat) := .empty
  for hy : y in [:n] do
    for hx : x in [:m] do
      if !visitdata.contains ⟨y, x⟩ then
        let letter := grid[y][x]
        let ⟨_, v⟩ := (walk y x curid letter).runState ⟨grid, visitdata⟩
        visitdata := v
        curid := curid + 1
  let mut total := 0
  for id in [:curid] do
    let mut area := 0
    let mut perimeter := 0
    for hk : k in visitdata.keys do
      if visitdata[k].1 == id then
        area := area + 1
        perimeter := perimeter + visitdata[k].2
    total := total + area * perimeter
  return total

--#eval firstPart testinput1           --(ans: )
--#eval firstPart testinput2           --(ans: )
--#eval firstPart realinput           --(ans: )

/-
PART 2:
-/

def getIdNhb (grid : Std.HashMap (Int × Int) Nat) (y x : Int) (dir : NSEW) : Option Nat := do
  let ⟨ny, nx⟩ := dir.step y x 1
  return ← grid[(⟨ny, nx⟩ : Int × Int)]?

def findStartingPoint (fence : Std.HashMap (Int × Int) (Array NSEW))
    (visited : Std.HashSet (Int × Int × NSEW)) : Option (Int × Int × NSEW) := do
  for hk : k in fence.keys do
    for dir in fence[k] do
      if !visited.contains ⟨k.1, k.2, dir⟩ then return ⟨k.1, k.2, dir⟩
  failure

def getNextDir (curdir : NSEW) (next : Array NSEW) : NSEW := Id.run do
  if next.contains curdir.rotateCW then return curdir.rotateCW
  if next.contains curdir then return curdir
  if next.contains curdir.rotateCCW then return curdir.rotateCCW
  panic! s!"reversing!"
  return curdir.reverse

partial def countFenceAux (fence : Std.HashMap (Int × Int) (Array NSEW)) (y x : Int) (dir : NSEW)
    (visited : Std.HashSet (Int × Int × NSEW)) (started : Bool) (cnt : Nat) : Nat :=
  if visited.contains ⟨y, x, dir⟩ then
    match findStartingPoint fence visited with
    | none => cnt
    | some ⟨ny, nx, d⟩ => countFenceAux fence ny nx d visited false cnt
  else
    let ⟨ny, nx⟩ := dir.step y x 1
    match fence[(⟨ny, nx⟩ : Int × Int)]? with
    | none => panic! "shit"
    | some nextdirs =>
        let nextdir := getNextDir dir nextdirs
        if started then
          if dir = nextdir then
            countFenceAux fence ny nx nextdir (visited.insert ⟨y, x, dir⟩) true cnt
          else
            countFenceAux fence ny nx nextdir (visited.insert ⟨y, x, dir⟩) true (cnt + 1)

        else
          if dir = nextdir then
            countFenceAux fence ny nx nextdir visited false cnt
          else
            countFenceAux fence ny nx nextdir visited true cnt

def countFence (fence : Std.HashMap (Int × Int) (Array NSEW)) : Nat :=
  match findStartingPoint fence .empty with
  | none => 0
  | some start => countFenceAux fence start.1 start.2.1 start.2.2 .empty false 0

def secondPart (input : FilePath) : IO Nat := do
  let some ⟨n, m, grid⟩ := (← IO.FS.lines input).map (·.toCharArray)
        |>.toVector₂ | panic! "not a grid"
  let initdata : WalkData n m := ⟨grid, .empty⟩
  let mut curid := 0
  let mut visitdata : Std.HashMap (Int × Int) (Nat × Nat) := .empty
  for hy : y in [:n] do
    for hx : x in [:m] do
      if !visitdata.contains ⟨y, x⟩ then
        let letter := grid[y][x]
        let ⟨_, v⟩ := (walk y x curid letter).runState ⟨grid, visitdata⟩
        visitdata := v
        curid := curid + 1
  let newgrid := visitdata.map fun _ ⟨id, _⟩ => id
  -- ⟨y, x, dir⟩
  let mut fences : Vector (Std.HashMap (Int × Int) (Array NSEW)) curid := .mkVector curid .empty
  for id in [:curid] do
    -- horizontal edges
    for y in [:n] do
      for x in [:m] do
        if newgrid[(⟨y, x⟩ : Int × Int)]? == some id then
          -- above
          if getIdNhb newgrid y x .n ≠ some id then fences := fences.set! id <| fences[id]!.push ⟨y, x⟩ .e
          -- below
          if getIdNhb newgrid y x .s ≠ some id then fences := fences.set! id <| fences[id]!.push ⟨y+1, x+1⟩ .w
    -- vertical edges
    for y in [:n] do
      for x in [:m] do
        if newgrid[(⟨y, x⟩ : Int × Int)]? == some id then
          -- left
          if getIdNhb newgrid y x .w ≠ some id then fences := fences.set! id <| fences[id]!.push ⟨y+1, x⟩ .n
          -- right
          if getIdNhb newgrid y x .e ≠ some id then fences := fences.set! id <| fences[id]!.push ⟨y, x+1⟩ .s
  let mut total := 0
  for hid : id in [:curid] do
    let perimeter := countFence fences[id]
    let mut area := 0
    for hk : k in visitdata.keys do
      if visitdata[k].1 == id then
        area := area + 1
    total := total + area * perimeter
  return total

--#eval secondPart testinput1           --(ans: 80)
--#eval secondPart testinput2           --(ans: 1206)
--#eval secondPart testinput3           --(ans: 236)
--#eval secondPart testinput4           --(ans: 368)
--#eval secondPart realinput           --(ans: )

end Day12
