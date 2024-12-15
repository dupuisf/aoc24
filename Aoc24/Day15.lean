import Aoc24.Utils
import Aoc24.Direction

-- https://www.dorais.org/lean4-parser/doc/
-- map: 50×50, 20000 commands

def IO.exitWithError (e : String) : IO α := do
  IO.println e
  IO.Process.exit 0

open System Parser

namespace Day15

def testinput1 : FilePath := "input_15_test1"
def testinput2 : FilePath := "input_15_test2"
def testinput3 : FilePath := "input_15_test3"
def realinput : FilePath := "input_15"

/-
PART 1:
-/

def printGrid (grid : Vector₂ Char n m) : IO Unit := do
  for hy : y in [:n] do
    for hx : x in [:m] do
      IO.print grid[y][x]
    IO.print '\n'
  IO.print '\n'

def parseCommand : StringParser NSEW := do
  match ← anyToken with
  | '^' => return .n
  | '>' => return .e
  | '<' => return .w
  | 'v' => return .s
  | _ => throwUnexpected

def parseCommands : StringParser (Array NSEW) := takeMany parseCommand

def findRobot (grid : Vector₂ Char n m) : Option (Nat × Nat) := do
  for hy : y in [:n] do
    for hx : x in [:m] do
      if grid[y][x] == '@' then return ⟨y, x⟩
  failure

partial def push (grid : Vector₂ Char n m) (y x : Nat) (dir : NSEW) :
    --(hy : y < n := by get_elem_tactic) (hx : x < m := by get_elem_tactic) :
    Bool × Vector₂ Char n m :=
  let curchar := grid[y]![x]!
  let ⟨ny, nx⟩ := dir.step y x 1
  if hny : ny < n then
    if hnx : nx < m then
      match grid[ny][nx] with
      | '.' =>
          let grid₁ := grid.set ny nx curchar
          let grid₂ := grid₁.set! y x '.'
          ⟨true, grid₂⟩
      | '#' => ⟨false, grid⟩
      | 'O' =>
          let ⟨pushed, grid'⟩ := push grid ny nx dir
          if !pushed then ⟨false, grid⟩
          else push grid' y x dir
      | _ => ⟨false, grid⟩
    else ⟨false, grid⟩
  else ⟨false, grid⟩

def sumCoords (grid : Vector₂ Char n m) (c : Char) : Nat := Id.run do
  let mut out := 0
  for hy : y in [:n] do
    for hx : x in [:m] do
      if grid[y][x] == c then
        out := out + 100*y + x
  return out

def firstPart (input : FilePath) : IO Nat := do
  let raw := (← IO.FS.lines input)
  let rawgrid := raw.take (raw.size - 2)
  let commands := raw[raw.size-1]!.yoloParse parseCommands
  let some ⟨n, m, grid⟩ := rawgrid.map (·.toCharArray) |>.toVector₂ | IO.exitWithError "parse error";
  let some ⟨ry, rx⟩ := findRobot grid | IO.exitWithError "no robot!"
  let mut y := ry
  let mut x := rx
  let mut ngrid := grid
  for cmd in commands do
    let ⟨pushed, ngrid'⟩ := push ngrid y x cmd
    let ⟨ny, nx⟩ := if pushed then cmd.step y x 1 else ⟨y, x⟩
    y := ny
    x := nx
    ngrid := ngrid'
  return sumCoords ngrid 'O'

--#eval firstPart testinput1           --(ans: )
--#eval firstPart testinput2           --(ans: )
--#eval firstPart realinput           --(ans: )

/-
PART 2:
-/

partial def pushBoxNS (grid : Vector₂ Char n m) (y x : Nat) (dir : NSEW) :
    Bool × Vector₂ Char n m :=
  let ⟨ny, nx⟩ := dir.step y x 1
  let lc := grid[ny]![nx]!
  let rc := grid[ny]![nx+1]!
  match lc, rc with
  | '.', '.' =>
      let grid₁ := grid.set! ny nx '['
      let grid₂ := grid₁.set! ny (nx+1) ']'
      let grid₃ := grid₂.set! y x '.'
      let grid₄ := grid₃.set! y (x+1) '.'
      ⟨true, grid₄⟩
  | '#', _ => ⟨false, grid⟩
  | _, '#' => ⟨false, grid⟩
  | '[', ']' =>
      let ⟨pushed, grid'⟩ := pushBoxNS grid ny nx dir
      if !pushed then ⟨false, grid⟩
      else pushBoxNS grid' y x dir
  | ']', '.' =>
      let ⟨pushed, grid'⟩ := pushBoxNS grid ny (nx-1) dir
      if !pushed then ⟨false, grid⟩
      else pushBoxNS grid' y x dir
  | '.', '[' =>
      let ⟨pushed, grid'⟩ := pushBoxNS grid ny (nx+1) dir
      if !pushed then ⟨false, grid⟩
      else pushBoxNS grid' y x dir
  | ']', '[' =>
      let ⟨pushedleft, grid'⟩ := pushBoxNS grid ny (nx-1) dir
      if !pushedleft then ⟨false, grid⟩
      else
        let ⟨pushedright, grid''⟩ := pushBoxNS grid' ny (nx+1) dir
        if !pushedright then ⟨false, grid⟩
        else pushBoxNS grid'' y x dir
  | _, _ => ⟨false, grid⟩

partial def pushNS (grid : Vector₂ Char n m) (y x : Nat) (dir : NSEW) :
    Bool × Vector₂ Char n m :=
  let curchar := grid[y]![x]!
  let ⟨ny, nx⟩ := dir.step y x 1
  if hny : ny < n then
    if hnx : nx < m then
      match grid[ny][nx] with
      | '.' =>
          let grid₁ := grid.set ny nx curchar
          let grid₂ := grid₁.set! y x '.'
          ⟨true, grid₂⟩
      | '#' => ⟨false, grid⟩
      | '[' =>
          let ⟨pushed, grid'⟩ := pushBoxNS grid ny nx dir
          if !pushed then ⟨false, grid⟩
          else pushNS grid' y x dir
      | ']' =>
          let ⟨pushed, grid'⟩ := pushBoxNS grid ny (nx-1) dir
          if !pushed then ⟨false, grid⟩
          else pushNS grid' y x dir
      | _ => ⟨false, grid⟩
    else ⟨false, grid⟩
  else ⟨false, grid⟩

partial def pushEW (grid : Vector₂ Char n m) (y x : Nat) (dir : NSEW) :
    Bool × Vector₂ Char n m :=
  let curchar := grid[y]![x]!
  let ⟨ny, nx⟩ := dir.step y x 1
  if hny : ny < n then
    if hnx : nx < m then
      match grid[ny][nx] with
      | '.' =>
          let grid₁ := grid.set ny nx curchar
          let grid₂ := grid₁.set! y x '.'
          ⟨true, grid₂⟩
      | '#' => ⟨false, grid⟩
      | '[' =>
          let ⟨pushed, grid'⟩ := pushEW grid ny nx dir
          if !pushed then ⟨false, grid⟩
          else pushEW grid' y x dir
      | ']' =>
          let ⟨pushed, grid'⟩ := pushEW grid ny nx dir
          if !pushed then ⟨false, grid⟩
          else pushEW grid' y x dir
      | _ => ⟨false, grid⟩
    else ⟨false, grid⟩
  else ⟨false, grid⟩

partial def push₂ (grid : Vector₂ Char n m) (y x : Nat) (dir : NSEW) :
    Bool × Vector₂ Char n m :=
  match dir with
  | .n => pushNS grid y x dir
  | .s => pushNS grid y x dir
  | .e => pushEW grid y x dir
  | .w => pushEW grid y x dir

def makeThick (row : Array Char) : Array Char := Id.run do
  let mut out : Array Char := .empty
  for c in row do
    match c with
    | 'O' => out := (out.push '[').push ']'
    | '@' => out := (out.push '@').push '.'
    | x => out := (out.push x).push x
  return out

def secondPart (input : FilePath) : IO Nat := do
  let raw := (← IO.FS.lines input)
  let rawgrid := raw.take (raw.size - 2) |>.map (·.toCharArray) |>.map makeThick
  let commands := raw[raw.size-1]!.yoloParse parseCommands
  let some ⟨n, m, grid⟩ := rawgrid.toVector₂ | IO.exitWithError "parse error";
  let some ⟨ry, rx⟩ := findRobot grid | IO.exitWithError "no robot!"
  let mut y := ry
  let mut x := rx
  let mut ngrid := grid
  for cmd in commands do
    let ⟨pushed, ngrid'⟩ := push₂ ngrid y x cmd
    let ⟨ny, nx⟩ := if pushed then cmd.step y x 1 else ⟨y, x⟩
    y := ny
    x := nx
    ngrid := ngrid'
  return sumCoords ngrid '['

--#eval secondPart testinput1           --(ans: )
--#eval secondPart testinput2           --(ans: )
--#eval secondPart testinput3           --(ans: )
#eval secondPart realinput           --(ans: )

end Day15
