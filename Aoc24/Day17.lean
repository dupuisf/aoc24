import Aoc24.Utils

-- https://www.dorais.org/lean4-parser/doc/

open System Parser

namespace Day17

def testinput1 : FilePath := "input_17_test1"
def testinput2 : FilePath := "input_17_test2"
def realinput : FilePath := "input_17"

/-
PART 1:
-/

-- Note: Input must be manually stripped of useless text

structure Computer where
  pointer : Nat
  a : Nat
  b : Nat
  c : Nat
  program : Array (Fin 8)
  output : Array Nat
  clock : Nat
deriving Repr, Inhabited, DecidableEq

def getA : StateM Computer Nat := return (← get).a
def getB : StateM Computer Nat := return (← get).b
def getC : StateM Computer Nat := return (← get).c
def getPointer : StateM Computer Nat := return (← get).pointer
def getClock : StateM Computer Nat := return (← get).clock
def getInst (addr : Nat) : StateM Computer (Option (Fin 8 × Fin 8)) := do
  let p := (← get).program
  let some opcode := p[addr]? | return none
  let some operand := p[addr+1]? | return none
  return some ⟨opcode, operand⟩

def setA (a : Nat) : StateM Computer Unit := do
  let C ← get
  set (σ := Computer) { C with a := a }

def setB (b : Nat) : StateM Computer Unit := do
  let C ← get
  set (σ := Computer) { C with b := b }

def setC (c : Nat) : StateM Computer Unit := do
  let C ← get
  set (σ := Computer) { C with c := c }

def setPointer (p : Nat) : StateM Computer Unit := do
  let C ← get
  set (σ := Computer) { C with pointer := p }

def advPointer : StateM Computer Unit := do
  let C ← get
  set (σ := Computer) { C with pointer := C.pointer + 2 }

def pushOutput (n : Nat) : StateM Computer Unit := do
  let C ← get
  set (σ := Computer) { C with output := C.output.push n }

def tick : StateM Computer Unit := do
  let C ← get
  set (σ := Computer) { C with clock := C.clock + 1 }

def Computer.exec (opcode : Fin 8) (lit : Fin 8) : StateM Computer Unit := do
  let a ← getA
  let b ← getB
  let c ← getC
  let combo : Nat := match lit with
                     | 4 => a
                     | 5 => b
                     | 6 => c
                     | _ => lit
  match opcode with
  -- adv
  | 0 => setA <| a >>> combo; advPointer
  -- bxl
  | 1 => setB <| b ^^^ lit; advPointer
  -- bst
  | 2 => setB <| combo % 8; advPointer
  -- jnz
  | 3 => if a == 0 then advPointer else setPointer lit
  -- bxc
  | 4 => setB <| b ^^^ c; advPointer
  -- out
  | 5 => pushOutput (combo % 8); advPointer
  -- bdv
  | 6 => setB <| a >>> combo; advPointer
  -- cdv
  | 7 => setC <| a >>> combo; advPointer

partial def Computer.runProg : StateM Computer (Array Nat) := do
  let addr ← getPointer
  let some ⟨opcode, operand⟩ ← getInst addr | return (← get).output
  dbg_trace s!"addr: {addr}, {opcode} {operand}"
  exec opcode operand
  tick
  --if (← getClock) ≥ 100 then return (← get).output
  runProg

def parseRegisters : StringParser (Nat × Nat × Nat) := do
  let registers ← (sepBy (Char.chars ",") Char.ASCII.parseNat)
  if h : registers.size < 3 then throwUnexpected
  else return ⟨registers[0], registers[1], registers[2]⟩

def formatOutput (as : Array Nat) : String := Id.run do
  if as == #[] then return ""
  let mut out := s!"{as[0]!}"
  for i in [1:as.size] do
    out := out ++ s!",{as[i]!}"
  return out

def firstPart (input : FilePath) : IO Nat := do
  let raw := (← IO.FS.lines input)
  let some registers := raw[0]!.parse? parseRegisters | IO.exitWithError "parse error (registers)"
  let some program := raw[1]!.parse? (sepBy (Char.chars ",") (Char.ASCII.parseFin 8)) | IO.exitWithError "parse error (program)"
  let comp : Computer := ⟨0, registers.1, registers.2.1, registers.2.2, program, #[], 0⟩
  let output := comp.runProg.run.1
  IO.print (formatOutput output)
  return 0

--#eval firstPart testinput1           --(ans: )
--#eval firstPart testinput2           --(ans: )
--#eval firstPart realinput           --(ans: )

/-
PART 2:
-/

def Computer.exec₂ (opcode : Fin 8) (lit : Fin 8) : StateM Computer Unit := do
  let a ← getA
  let b ← getB
  let c ← getC
  let combo : Nat := match lit with
                     | 4 => a
                     | 5 => b
                     | 6 => c
                     | _ => lit
  match opcode with
  -- adv
  | 0 => setA <| a >>> combo; advPointer
  -- bxl
  | 1 => setB <| b ^^^ lit; advPointer
  -- bst
  | 2 => setB <| combo % 8; advPointer
  -- jnz
  | 3 => if a == 0 then advPointer else setPointer 0
  -- bxc
  | 4 => setB <| b ^^^ c; advPointer
  -- out
  | 5 => pushOutput (combo % 8); advPointer
  -- bdv
  | 6 => setB <| a >>> combo; advPointer
  -- cdv
  | 7 => setC <| a >>> combo; advPointer

partial def Computer.runProg₂ : StateM Computer (Array Nat) := do
  let addr ← getPointer
  let some ⟨opcode, operand⟩ ← getInst addr | return (← get).output
  dbg_trace s!"addr: {addr}, {opcode} {operand}"
  exec opcode operand
  tick
  --if (← getClock) ≥ 100 then return (← get).output
  runProg₂

def printProgram (prog : Array (Fin 8)) : IO Unit := do
  for i in [:prog.size/2] do
    let lit := prog[2*i+1]!
    let combo : String := match lit with
                       | 4 => "a"
                       | 5 => "b"
                       | 6 => "c"
                       | x => s!"{x}"
    match prog[2*i]! with
    -- adv
    | 0 => IO.println s!"a := a >>> {combo}"
    -- bxl
    | 1 => IO.println s!"b := b ^^^ {lit}"
    -- bst
    | 2 => IO.println s!"b := {combo} % 8"
    -- jnz
    | 3 => IO.println s!"jnz {lit}"
    -- bxc
    | 4 => IO.println s!"b := b ^^^ c"
    -- out
    | 5 => IO.println s!"out {combo}"
    -- bdv
    | 6 => IO.println s!"b := a >>> {combo}"
    -- cdv
    | 7 => IO.println s!"c := a >>> {combo}"

def dp (target : Vector (Fin 8) n) : Vector₂ Bool (n+1) 1024 := Id.run do
  let mut table : Vector₂ Bool (n+1) 1024 := .mkVector₂ _ _ false
  table := table.set 0 0 true
  for hpos : pos in [:n] do
    have hpos' : pos < n+1 := by apply Nat.lt_add_one_of_lt; exact Membership.get_elem_helper hpos rfl  -- WTF
    for ha : a in [:1024] do
      let mut flag := false
      for hpA : prevA in [:1024] do
        if a >>> 3 == prevA % 2^7 && table[pos][prevA] then flag := true
      if flag then
        -- there's some previous value that matches
        let b := (a % 8) ^^^ 3
        let c := a >>> b
        let a' := a >>> 3
        let b' := b ^^^ 5 ^^^ c
        if b' % 8 == target[pos] then
          table := table.set (pos+1) a true <| by
              apply Nat.succ_lt_succ; exact Membership.get_elem_helper hpos rfl  -- WTF
  return table

def findBestA (table : Vector₂ Bool (n+1) 1024) : Nat := Id.run do
  let mut a := 0
  for hpos : pos in [1:n+1] do
    for hx : x in [:1024] do
      if table[pos][x] then
        a := (a <<< 3) + x % 8
        break
  return a

--def mytarget : Vector (Fin 8) 6 := ⟨#[0, 3, 4, 5, 3, 0], by simp⟩
--
--#eval findBestA <| dp mytarget

def secondPart (input : FilePath) : IO Nat := do
  let raw := (← IO.FS.lines input)
  --let some registers := raw[0]!.parse? parseRegisters | IO.exitWithError "parse error (registers)"
  let some program := raw[1]!.parse? (sepBy (Char.chars ",") (Char.ASCII.parseFin 8)) | IO.exitWithError "parse error (program)"
  dbg_trace "ici1"
  let ⟨n, target⟩ := program.reverse.toVector
  let table := dp target
  IO.print (repr table)
  let answer := findBestA table
  dbg_trace "ici2"
  return answer

--#eval secondPart testinput1           --(ans: )
--#eval secondPart testinput2           --(ans: )
--#eval secondPart realinput           --(ans: )

end Day17
