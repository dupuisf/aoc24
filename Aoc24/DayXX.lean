import Parser

open System

namespace DayXX

def testinput1 : FilePath := "/home/fred/lean/aoc24/input_XX_test1"
def testinput2 : FilePath := "/home/fred/lean/aoc24/input_XX_test2"
def realinput : FilePath := "/home/fred/lean/aoc24/input_XX"

/-
PART 1:
-/

def firstPart (input : FilePath) : IO String := do
  let rawdata := (← IO.FS.lines input)
  return s!"bla"

--#eval firstPart testinput1           --(ans: )
--#eval firstPart realinput           --(ans: )

/-
PART 2:
-/

def secondPart (input : FilePath) : IO String := do
  let rawdata := (← IO.FS.lines input)
  return s!"bla"

--#eval secondPart testinput1           --(ans: )
--#eval secondPart realinput           --(ans: )

end DayXX
