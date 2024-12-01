import Aoc24.Utils

open System

namespace Day01

def testinput1 : FilePath := "/home/fred/lean/aoc24/input_01_test1"
def testinput2 : FilePath := "/home/fred/lean/aoc24/input_01_test2"
def realinput : FilePath := "/home/fred/lean/aoc24/input_01"

/-
PART 1:
-/

def firstPart (input : FilePath) : IO Nat := do
  let rawdata := (← IO.FS.lines input).map String.splitOn
  let fstlist := rawdata.map (List.getD · 0 "0") |>.map String.toNat! |>.qsortOrd
  let sndlist := rawdata.map (List.getD · 1 "0") |>.map String.toNat! |>.qsortOrd
  let diffs := fstlist.zipWith sndlist fun x y => if x ≤ y then y - x else x - y
  return diffs.sum

--#eval firstPart testinput1           --(ans: 11)
--#eval firstPart realinput           --(ans: 2264607)

/-
PART 2:
-/

-- Assumes identical elements are contiguous in `xs`
def counter [Inhabited α] [BEq α] (xs : Array α) : Array (α × Nat) :=
  let rec go (out : Array (α × Nat)) (i : Nat) (last : α) (cnt : Nat) : Array (α × Nat) :=
    if h : xs.size ≤ i then out.push ⟨last, cnt⟩
    else if xs[i] == last then go out (i+1) last (cnt+1)
      else go (out.push ⟨last, cnt⟩) (i+1) xs[i] 1
  termination_by xs.size - i
  if h' : 0 < xs.size then go #[] 1 xs[0] 1 else #[]

def secondPart (input : FilePath) : IO Nat := do
  let rawdata := (← IO.FS.lines input).map String.splitOn
  let fstlist := rawdata.map (List.getD · 0 "0") |>.map String.toNat! |>.qsortOrd
  let sndlist := rawdata.map (List.getD · 1 "0") |>.map String.toNat! |>.qsortOrd
  let sndcnt := counter sndlist
  let scores := fstlist.map fun x =>
    match sndcnt.binSearchMap x (fun a => a.1) with
    | none => 0
    | some z => z.2 * x
  return scores.sum

--#eval secondPart testinput1           --(ans: 31)
--#eval secondPart realinput           --(ans: 19457120)

end Day01
