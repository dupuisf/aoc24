import Aoc24.Utils
import Parser

open System
open Parser

namespace Day03

def testinput1 : FilePath := "/home/fred/lean/aoc24/input_03_test1"
def testinput2 : FilePath := "/home/fred/lean/aoc24/input_03_test2"
def realinput : FilePath := "/home/fred/lean/aoc24/input_03"

/-
PART 1:
-/

def parseMul : StringParser (Nat × Nat) := do
  let _ ← Char.chars "mul("
  let x ← Char.ASCII.parseNat
  let _ ← Char.char ','
  let y ← Char.ASCII.parseNat
  let _ ← Char.char ')'
  return ⟨x, y⟩

def globalParse : StringParser (Array (Nat × Nat)) :=
  foldl (init := #[]) (p := dropUntil parseMul anyToken) fun as pair => as.push pair

def firstPart (input : FilePath) : IO Nat := do
  let rawdata := (← IO.FS.readFile input).yoloParse globalParse
  let output := rawdata.foldl (init := 0) fun res pair => res + pair.1 * pair.2
  return output

--#eval firstPart testinput1           --(ans: 161)
--#eval firstPart realinput           --(ans: )

/-
PART 2:
-/

inductive Instruction where
| mul (x y : Nat) : Instruction
| doIt : Instruction
| dontDoIt : Instruction
deriving BEq, Inhabited, Repr

instance : ToString Instruction := ⟨reprStr⟩

def parseMulInst : StringParser Instruction := do
  let _ ← Char.chars "mul("
  let x ← Char.ASCII.parseNat
  let _ ← Char.char ','
  let y ← Char.ASCII.parseNat
  let _ ← Char.char ')'
  return .mul x y

def parseDoInst : StringParser Instruction := do
  let _ ← Char.chars "do()"
  return .doIt

def parseDontInst : StringParser Instruction := do
  let _ ← Char.chars "don't()"
  return .dontDoIt

def parseInst : StringParser Instruction := parseDoInst <|> parseDontInst <|> parseMulInst

def globalParseInst : StringParser (Array Instruction) :=
  foldl (init := #[]) (p := dropUntil parseInst anyToken) fun as pair => as.push pair

def secondPart (input : FilePath) : IO Nat := do
  let rawdata := (← IO.FS.readFile input).yoloParse globalParseInst
  let mut output := 0
  let mut enabled := true
  for inst in rawdata do
    match inst with
    | .mul x y => if enabled then output := output + x * y
    | .doIt => enabled := true
    | .dontDoIt => enabled := false
  return output

--#eval secondPart testinput2           --(ans: 48)
--#eval secondPart realinput           --(ans: )

end Day03
