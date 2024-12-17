import Aoc24.Utils

-- https://www.dorais.org/lean4-parser/doc/

open System Parser

namespace DayXX

def testinput1 : FilePath := "input_XX_test1"
def testinput2 : FilePath := "input_XX_test2"
def realinput : FilePath := "input_XX"

/-
PART 1:
-/

def firstPart (input : FilePath) : IO Nat := do
  --let raw := (← IO.FS.readFile input)
  let raw := (← IO.FS.lines input)
  return 0

--#eval firstPart testinput1           --(ans: )
--#eval firstPart testinput2           --(ans: )
--#eval firstPart realinput           --(ans: )

/-
PART 2:
-/

def secondPart (input : FilePath) : IO Nat := do
  --let raw := (← IO.FS.readFile input)
  let raw := (← IO.FS.lines input)
  return 0

--#eval secondPart testinput1           --(ans: )
--#eval secondPart testinput2           --(ans: )
--#eval secondPart realinput           --(ans: )

end DayXX
