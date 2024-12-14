import Aoc24.Utils

open System Parser

def Parser.Char.ASCII.newline : StringParser Unit := do
  let _ ← takeMany1 (Char.ASCII.lf <|> Char.ASCII.cr)
  return

namespace Day13

def testinput1 : FilePath := "input_13_test1"
def testinput2 : FilePath := "input_13_test2"
def realinput : FilePath := "input_13"

-- https://www.dorais.org/lean4-parser/doc/

/-
PART 1:
-/

structure Game where
  xa : Int
  ya : Int
  xb : Int
  yb : Int
  xp : Int
  yp : Int
deriving Repr, Inhabited, DecidableEq, Hashable

instance : ToString Game where
  toString g := s!"A: X+{g.xa} Y+{g.ya}\nB: X+{g.xb} Y+{g.yb}\nPrize: X={g.xp} Y={g.yp}"

def parseButton : StringParser (Nat × Nat) := do
  let _ ← Char.chars "Button "
  let _ ← Char.ASCII.alpha
  let _ ← Char.chars ": X+"
  let x ← Char.ASCII.parseNat
  let _ ← Char.chars ", Y+"
  let y ← Char.ASCII.parseNat
  return ⟨x, y⟩

def parsePrize (fudge : Nat) : StringParser (Nat × Nat) := do
  let _ ← Char.chars "Prize: X="
  let x ← Char.ASCII.parseNat
  let _ ← Char.chars ", Y="
  let y ← Char.ASCII.parseNat
  return ⟨fudge + x, fudge + y⟩

def parseGame (fudge : Nat) : StringParser Game := do
  let ⟨xa, ya⟩ ← parseButton
  let _ ← Char.ASCII.newline
  let ⟨xb, yb⟩ ← parseButton
  let _ ← Char.ASCII.newline
  let ⟨xp, yp⟩ ← parsePrize fudge
  return ⟨xa, ya, xb, yb, xp, yp⟩

def candiv (x y : Int) : Bool :=
  let x' := x.natAbs
  let y' := y.natAbs
  x' % y' == 0

def solveOptim (x y c : Int) : Option Int := Id.run do
  let mut best := 100000000
  for a in [:100] do
    for b in [:100] do
      if a * x + b * y == c then
        if 3*a + b ≤ best then best := 3*a + b
  if best == 100000000 then return none else return some best

def solveGame (g : Game) : Option Int :=
  if g.xb * g.ya = g.xa * g.yb then
    -- Singular
    if g.xp * g.ya = g.yp * g.xa then
      --dbg_trace s!"ici"
       -- many solutions, must pick best one
       -- For some reason this never happens on the input in part 2, I wrote this stuff for nothing
      match solveOptim g.xa g.xb g.xp with
      | none => none
      | some best => best
    else none
  else
    -- unique solution
    if candiv (g.xp * g.ya - g.yp * g.xa) (g.xb * g.ya - g.xa * g.yb) then
      -- `b` is an integer
      let b := (g.xp * g.ya - g.yp * g.xa) / (g.xb * g.ya - g.xa * g.yb)
      if candiv (g.xp - b * g.xb) g.xa then
        -- `a` is also an integer
        let a := (g.xp - b * g.xb) / g.xa
        let tokens := 3*a + b
        --if a ≤ 100 && b ≤ 100 then some tokens else none
        some tokens
      else none
    else none


def firstPart (input : FilePath) : IO Int := do
  let some games := (← IO.FS.readFile input).parse? (sepBy Char.ASCII.newline (parseGame 0)) | panic! "Parse error"
  let soln := games.foldl (init := (0 : Int)) fun total cur =>
    match solveGame cur with
    | none => total
    | some val => total + val
  return soln

--#eval firstPart testinput1           --(ans: )
--#eval firstPart realinput           --(ans: )

/-
PART 2:
-/

def secondPart (input : FilePath) : IO Int := do
  let some games := (← IO.FS.readFile input).parse? (sepBy Char.ASCII.newline (parseGame 10000000000000)) | panic! "Parse error"
  let soln := games.foldl (init := (0 : Int)) fun total cur =>
    match solveGame cur with
    | none => total
    | some val => total + val
  return soln

--#eval secondPart testinput1           --(ans: )
--#eval secondPart realinput           --(ans: )

end Day13
