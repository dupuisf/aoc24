import Aoc24.Utils

open System Parser

namespace Day11

def testinput1 : FilePath := "input_11_test1"
def testinput2 : FilePath := "input_11_test2"
def realinput : FilePath := "input_11"

/-
PART 1:
-/

partial def bruteforce (stones : List (Nat × Nat)) (cur : Nat) : Nat :=
  match stones with
  | [] => cur
  | ⟨x, todo⟩ :: tail =>
      if 0 < todo then
        if x = 0 then
          bruteforce (⟨x+1, todo-1⟩ :: tail) cur
        else if x.log10 % 2 == 0 then
          let d := x.log10 / 2
          let x₁ := x / 10^d
          let x₂ := x % 10^d
          bruteforce (⟨x₁, todo-1⟩ :: ⟨x₂, todo-1⟩ :: tail) cur
        else
          bruteforce (⟨x*2024, todo-1⟩ :: tail) cur
      else
        bruteforce tail (cur+1)

def firstPart (input : FilePath) (blinks : Nat) : IO Nat := do
  let stones := (← IO.FS.readFile input).trim.splitOn " " |>.map (·.yoloParse Char.ASCII.parseNat)
  let stonesAnx : List (Nat × Nat) := stones.map fun x => ⟨x, blinks⟩
  return (bruteforce stonesAnx 0)

--#eval firstPart testinput2           --(ans: )
--#eval firstPart realinput           --(ans: )

/-
PART 2:
-/

def stoneOrd (s₁ s₂ : Nat × Nat × Nat) : Ordering :=
  match compare s₁.1 s₂.1 with
  | .lt => .lt
  | .gt => .gt
  | .eq => compare s₁.2.1 s₂.2.1

def placeStone (lst : List (Nat × Nat × Nat)) (st : Nat × Nat × Nat) : List (Nat × Nat × Nat) :=
  match lst with
  | [] => [st]
  | b :: l => match stoneOrd st b with
              | .gt => b :: placeStone l st
              | .lt => st :: b :: l
              | .eq => ⟨st.1, st.2.1, st.2.2 + b.2.2⟩ :: l

/-- Less brutal but not good enough. -/
partial def lessbrutal (stones : List (Nat × Nat × Nat)) (cur : Nat) : Nat :=
  match stones with
  | [] => cur
  | ⟨x, todo, mult⟩ :: tail =>
      if 0 < todo then
        if x = 0 then
          let newstones := placeStone tail ⟨1, todo-1, mult⟩
          lessbrutal newstones cur
        else if x.log10 % 2 == 0 then
          let d := x.log10 / 2
          let x₁ := x / 10^d
          let x₂ := x % 10^d
          let prenewstones := placeStone tail ⟨x₁, todo-1, mult⟩
          let newstones := placeStone prenewstones ⟨x₂, todo-1, mult⟩
          lessbrutal newstones cur
        else
          let newstones := placeStone tail ⟨x*2024, todo-1, mult⟩
          lessbrutal newstones cur
      else
        lessbrutal tail (cur+mult)

partial def buildCache (stones : List (Nat × Nat)) (cache : Std.HashMap (Nat × Nat) Nat) :
    Std.HashMap (Nat × Nat) Nat :=
  match stones with
  | [] => cache
  | ⟨x, todo⟩ :: tail =>
      if cache.contains ⟨x, todo⟩ then cache
      else
        if 0 < todo then
          if x = 0 then
            let newcache := buildCache (⟨x+1, todo-1⟩ :: tail) cache
            newcache.insert ⟨x, todo⟩ newcache[(⟨x+1, todo-1⟩ : Nat × Nat)]!
          else if x.log10 % 2 == 0 then
            let d := x.log10 / 2
            let x₁ := x / 10^d
            let x₂ := x % 10^d
            let prenewcache := buildCache (⟨x₁, todo-1⟩ :: tail) cache
            let newcache := buildCache (⟨x₂, todo-1⟩ :: tail) prenewcache
            newcache.insert ⟨x, todo⟩
              (newcache[(⟨x₁, todo-1⟩ : Nat × Nat)]! + newcache[(⟨x₂, todo-1⟩ : Nat × Nat)]!)
          else
            let newcache := buildCache (⟨x*2024, todo-1⟩ :: tail) cache
            newcache.insert ⟨x, todo⟩ newcache[(⟨x*2024, todo-1⟩ : Nat × Nat)]!
        else
          let newcache := buildCache tail cache
          newcache.insert ⟨x, 0⟩ 1

def secondPart (input : FilePath) (blinks : Nat) : IO Nat := do
  let stones := (← IO.FS.readFile input).trim.splitOn " " |>.map (·.yoloParse Char.ASCII.parseNat)
  let stonesAnx : List (Nat × Nat) := stones.map fun x => ⟨x, blinks⟩
  let cache := buildCache stonesAnx .empty
  let mut out := 0
  for i in stones do
    out := out + cache[(⟨i, blinks⟩ : Nat × Nat)]!
  return out

--#eval secondPart testinput1           --(ans: )
--#eval secondPart testinput2           --(ans: )
--#eval secondPart realinput           --(ans: )

end Day11
