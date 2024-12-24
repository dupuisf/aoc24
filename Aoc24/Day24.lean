import Aoc24.Utils
import Aoc24.Direction
import Aoc24.Graphs

-- https://www.dorais.org/lean4-parser/doc/

open System Parser

namespace Day24

def testinput1 : FilePath := "input_24_test1"
def testinput2 : FilePath := "input_24_test2"
def realinput : FilePath := "input_24"

/-
PART 1:
-/

abbrev Wire := Array Char

inductive Gate where
| and (a b c : Wire) : Gate
| or (a b c : Wire) : Gate
| xor (a b c : Wire) : Gate
deriving DecidableEq, Hashable, Repr, Inhabited

def Gate.output (g : Gate) : Wire :=
  match g with
  | .and _ _ c => c
  | .xor _ _ c => c
  | .or _ _ c => c

def Gate.eval (g : Gate) (a b : Bool) : Bool :=
  match g with
  | .and _ _ _ => a && b
  | .xor _ _ _ => a ^^ b
  | .or _ _ _ => a || b

def Gate.operands (g : Gate) : Array Wire :=
  match g with
  | .and a b _ => #[a, b]
  | .xor a b _ => #[a, b]
  | .or a b _ => #[a, b]

def Gate.op1 (g : Gate) : Wire :=
  match g with | .and a _ _ => a | .xor a _ _ => a | .or a _ _ => a

def Gate.op2 (g : Gate) : Wire :=
  match g with | .and _ b _ => b | .xor _ b _ => b | .or _ b _ => b

def parseWireVal : StringParser (Wire × Bool) := do
  let s ← takeMany Char.ASCII.alphanum
  let _ ← Char.chars ": "
  let bit ← Char.ASCII.parseNat
  return ⟨s, bit != 0⟩

def parseAndGate : StringParser Gate := do
  let a ← takeMany Char.ASCII.alphanum
  let _ ← Char.chars " AND "
  let b ← takeMany Char.ASCII.alphanum
  let _ ← Char.chars " -> "
  let c ← takeMany Char.ASCII.alphanum
  return .and a b c

def parseOrGate : StringParser Gate := do
  let a ← takeMany Char.ASCII.alphanum
  let _ ← Char.chars " OR "
  let b ← takeMany Char.ASCII.alphanum
  let _ ← Char.chars " -> "
  let c ← takeMany Char.ASCII.alphanum
  return .or a b c

def parseXorGate : StringParser Gate := do
  let a ← takeMany Char.ASCII.alphanum
  let _ ← Char.chars " XOR "
  let b ← takeMany Char.ASCII.alphanum
  let _ ← Char.chars " -> "
  let c ← takeMany Char.ASCII.alphanum
  return .xor a b c

def parseGate := parseAndGate <|> parseOrGate <|> parseXorGate

def parseInput : StringParser (Array (Wire × Bool) × Array Gate) := do
  let wires ← sepBy Char.ASCII.newline parseWireVal
  let _ ← Char.ASCII.newline
  let gates ← sepBy Char.ASCII.newline parseGate
  return ⟨wires, gates⟩

def getAnswer (vals : Std.HashMap Wire Bool) : Nat := Id.run do
  let mut out := 0
  for w in vals.keys do
    if vals[w]! then
      match w[0]! with
      | 'z' =>
          let num := ((String.ofCharArray w).drop 1).toNat!
          out := out ||| (1 <<< num)
      | _ => noop
  return out

def firstPart (input : FilePath) : IO Nat := do
  let some ⟨initwires, gates⟩ := (← IO.FS.readFile input).parse? parseInput | IO.exitWithError "Parse error"
  let graph : Std.HashMap Wire Gate := gates.foldl (init := .empty) fun acc cur =>
    acc.insert cur.output cur
  let wires : Std.HashSet Wire := gates.foldl (init := .ofArray (initwires.map Prod.fst)) fun acc cur =>
    acc.insert cur.output
  let topoconfig : TopologicalSort.Config Wire (Std.HashMap Wire Gate) :=
  { startvertices := wires.toArray
    graph := graph
    getNeighbors g v := match g[v]? with
                        | none => #[]
                        | some gate => gate.operands }
  let sortedwires := topoconfig.sort.reverse

  let mut wirevals : Std.HashMap Wire Bool := .ofList initwires.toList
  for w in sortedwires do
    if !wirevals.contains w && graph.contains w then
      let g := graph[w]!
      let aval := wirevals[g.op1]!
      let bval := wirevals[g.op2]!
      wirevals := wirevals.insert w (g.eval aval bval)
  IO.println (repr wirevals)
  return (getAnswer wirevals)

--#eval firstPart testinput1           --(ans: )
--#eval firstPart testinput2           --(ans: )
--#eval firstPart realinput           --(ans: )

/-
PART 2:
-/

-- 312 wires, 222 gates, x and y are 44 bits each

def secondPart (input : FilePath) : IO String := do
  let some ⟨initwires, gates⟩ := (← IO.FS.readFile input).parse? parseInput | IO.exitWithError "Parse error"
  let graph : Std.HashMap Wire Gate := gates.foldl (init := .empty) fun acc cur =>
    acc.insert cur.output cur
  let wires : Std.HashSet Wire := gates.foldl (init := .ofArray (initwires.map Prod.fst)) fun acc cur =>
    acc.insert cur.output
  let topoconfig : TopologicalSort.Config Wire (Std.HashMap Wire Gate) :=
  { startvertices := wires.toArray
    graph := graph
    getNeighbors g v := match g[v]? with
                        | none => #[]
                        | some gate => gate.operands }
  let sortedwires := topoconfig.sort.reverse

  let mut wirevals : Std.HashMap Wire Bool := .ofList initwires.toList
  for w in sortedwires do
    if !wirevals.contains w && graph.contains w then
      let g := graph[w]!
      let aval := wirevals[g.op1]!
      let bval := wirevals[g.op2]!
      wirevals := wirevals.insert w (g.eval aval bval)
  IO.println gates.size
  return "foo"

--#eval secondPart testinput1           --(ans: )
--#eval secondPart testinput2           --(ans: )
--#eval secondPart realinput           --(ans: )

end Day24
