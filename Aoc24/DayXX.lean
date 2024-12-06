import Aoc24.Utils
import Parser

open System

namespace DayXX

def testinput1 : FilePath := "input_XX_test1"
def testinput2 : FilePath := "input_XX_test2"
def realinput : FilePath := "input_XX"

/-
PART 1:
-/

def firstPart (input : FilePath) : IO Nat := do
  --let rawdata := (← IO.FS.lines input)    -- read whole file
  let rawdata := (← IO.FS.lines input)      -- read line by line into an array
  --return s!"bla"
  return 0

--#eval firstPart testinput1           --(ans: )
--#eval firstPart realinput           --(ans: )

/-
PART 2:
-/

def secondPart (input : FilePath) : IO Nat := do
  --let rawdata := (← IO.FS.lines input)
  let rawdata := (← IO.FS.lines input)
  --return s!"bla"
  return 0

--#eval secondPart testinput1           --(ans: )
--#eval secondPart realinput           --(ans: )

end DayXX
