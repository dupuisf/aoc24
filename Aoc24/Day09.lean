import Aoc24.Utils

open System Parser

namespace Day09

def testinput1 : FilePath := "input_09_test1"
def testinput2 : FilePath := "input_09_test2"
def realinput : FilePath := "input_09"

/-
PART 1:
-/

def uncompress (disk : Array Char) : Array (Option Nat) := Id.run do
  let mut out : Array (Option Nat) := .empty
  let mut isBlock := true
  let mut blockId := 0
  for c in disk do
    let some d := c.toNatDigit? | panic! "not a digit"
    if isBlock then
      for _ in [:d] do
        out := out.push (some blockId)
      isBlock := !isBlock
      blockId := blockId + 1
    else
      for _ in [:d] do
        out := out.push none
      isBlock := !isBlock
  return out

def printUncompressed (disk : Array (Option Nat)) : String := Id.run do
  let mut out := ""
  for b in disk do
    match b with
    | none => out := out.append "."
    | some d => out := out.append s!"{d}"
  return out

def pack (disk : Array (Option Nat)) (i j : Nat) : Array (Option Nat) :=
  if j ≤ i then disk
  else
    match disk[i]!, disk[j]! with
    | none, none => pack disk i (j-1)
    | none, some id₂ =>
        let newdisk := (disk.set! i (some id₂)).set! j none
        pack newdisk (i+1) (j-1)
    | some _, none => pack disk (i+1) (j-1)
    | some _, some _ => pack disk (i+1) j
termination_by j - i

def checksum (disk : Array (Option Nat)) : Nat := Id.run do
  let mut out := 0
  for hi : i in [:disk.size] do
    out := match disk[i] with
           | none => out
           | some id => out + i * id
  return out

def firstPart (input : FilePath) : IO Nat := do
  let disk := (← IO.FS.readFile input).trim.toCharArray
  let uncompressedDisk : Array (Option Nat) := uncompress disk
  let packed := pack uncompressedDisk 0 (uncompressedDisk.size - 1)
  return (checksum packed)

--#eval firstPart testinput1           --(ans: )
--#eval firstPart realinput           --(ans: )

/-
PART 2:
-/

partial def findEmptyBlock (disk : Array (Option Nat)) (len pos currun : Nat) : Option Nat :=
  if currun = len then pos - currun
  else if pos ≥ disk.size - 1 then none
  else match disk[pos]! with
       | none => findEmptyBlock disk len (pos + 1) (currun + 1)
       | some _ => findEmptyBlock disk len (pos + 1) 0

def noop [Monad m] : m Unit := do
  return ⟨⟩

def updateFree (disk : Array (Option Nat)) (free : Vector (Option Nat) 10) : Vector (Option Nat) 10 := Id.run do
  let mut out := free
  for len in [1:10] do
    match free[len]! with
    | none => noop
    | some pos =>
        let newpos := findEmptyBlock disk len pos 0
        out := out.set! len newpos
  return out

def moveBlock (disk : Array (Option Nat)) (pos blkleft blkright : Nat) : Array (Option Nat) := Id.run do
  let mut out := disk
  let some id := disk[blkleft]! | panic! "shit1"
  for i in [:blkright-blkleft+1] do
    out := out.set! (pos + i) (some id)
    out := out.set! (blkleft + i) none
  return out

-- this is just sad
def natmin (as : Vector (Option Nat) n) : Nat := Id.run do
  let mut out := 0
  for hi : i in [:n] do
    match as[i] with
    | none => noop
    | some x => if x ≤ out then out := x
  return out

def findNextBlock (disk : Array (Option Nat)) (pos : Nat) : Nat × Nat := Id.run do
  let mut cur := pos
  for _ in [:pos] do
    if disk[cur]! != none then break
    cur := cur - 1
  let hi := cur
  let some id := disk[cur]! | panic! "shit2"
  let mut cur2 := cur-1
  for _ in [:hi] do
    if disk[cur2]! != some id then break
    cur2 := cur2 - 1
  return ⟨cur2 + 1, hi⟩

partial def pack₂ (disk : Array (Option Nat)) (j : Nat) (free : Vector (Option Nat) 10) : Array (Option Nat) :=
  let i := natmin free
  if j ≤ i then disk
  else
    let ⟨lo, hi⟩ := findNextBlock disk j
    match free[hi-lo+1]! with
    | none => pack₂ disk (lo - 1) free
    | some freepos =>
        if freepos < lo then
          let newdisk := moveBlock disk freepos lo hi
          let newfree := updateFree newdisk free
          pack₂ newdisk (lo - 1) newfree
        else
          pack₂ disk (lo - 1) free

def secondPart (input : FilePath) : IO Nat := do
  let rawdisk := (← IO.FS.readFile input).trim.toCharArray
  let disk : Array (Option Nat) := uncompress rawdisk
  let packed := pack₂ disk (disk.size - 1) (updateFree disk (.mkVector 10 (some 0)))
  return (checksum packed)

--#eval secondPart testinput1           --(ans: )
--#eval secondPart realinput           --(ans: )

end Day09
