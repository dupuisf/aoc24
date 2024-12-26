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

inductive Role where
| xinput (n : Nat) : Role
| yinput (n : Nat) : Role
| xorlevel1 (n : Nat) : Role   -- xn XOR yn  (except z00, which is an output)
| andlevel1 (n : Nat) : Role   -- xn AND yn
| andlevel2 (n : Nat) : Role   -- (xn XOR yn) AND carry (n-1)
| output (n : Nat) : Role   -- (xn XOR yn) XOR carry (n-1)  (= zn)
| carry (n : Nat) : Role    -- only OR gates
deriving DecidableEq, Hashable, Repr, Inhabited

partial def lightcone (graph : Std.HashMap Wire Gate) (v : Wire) : StateM (Std.HashSet Wire) Unit := do
  if graph.contains v then
    set <| (← get).insert v
    let g := graph[v]!
    lightcone graph g.op1
    lightcone graph g.op2
  else
    set <| (← get).insert v

def Gate.toString (g : Gate) : String :=
  match g with
  | .xor a b c => s!"{String.ofCharArray a} XOR {String.ofCharArray b} -> {String.ofCharArray c}"
  | .and a b c => s!"{String.ofCharArray a} AND {String.ofCharArray b} -> {String.ofCharArray c}"
  | .or a b c =>  s!"{String.ofCharArray a} OR {String.ofCharArray b} -> {String.ofCharArray c}"

def printPartialGraph (graph : Std.HashMap Wire Gate) (wires : Std.HashSet Wire) : IO Unit := do
  for w in wires do
    match graph[w]? with
    | none => noop
    | some g => IO.println g.toString

def getXorLevel1 (graph : Std.HashMap Wire Gate) : Std.HashMap Wire Role := Id.run do
  let mut out : Std.HashMap Wire Role := .empty
  for v in graph.keys do
    match graph[v]! with
    | .xor a b c =>
        if (String.ofCharArray c) != "z00" then
          match a[0]!, b[0]! with
          | 'x', 'y' =>
              let xnum := ((String.ofCharArray a).drop 1).toNat!
              let ynum := ((String.ofCharArray b).drop 1).toNat!
              if xnum != ynum then panic! "level one with mismatched numbers"
              out := out.insert v (.xorlevel1 xnum)
          | 'y', 'x' =>
              let xnum := ((String.ofCharArray b).drop 1).toNat!
              let ynum := ((String.ofCharArray a).drop 1).toNat!
              if xnum != ynum then panic! "level one with mismatched numbers"
              out := out.insert v (.xorlevel1 xnum)
          | _, _ => noop
    | _ => noop
  return out

def getAndLevel1 (graph : Std.HashMap Wire Gate) (roles : Std.HashMap Wire Role := .empty) : Std.HashMap Wire Role := Id.run do
  let mut out : Std.HashMap Wire Role := roles
  for v in graph.keys do
    match graph[v]! with
    | .and a b c =>
        if (String.ofCharArray c) != "mcg" then
          match a[0]!, b[0]! with
          | 'x', 'y' =>
              let xnum := ((String.ofCharArray a).drop 1).toNat!
              let ynum := ((String.ofCharArray b).drop 1).toNat!
              if xnum != ynum then panic! "level one with mismatched numbers"
              out := out.insert v (.andlevel1 xnum)
          | 'y', 'x' =>
              let xnum := ((String.ofCharArray b).drop 1).toNat!
              let ynum := ((String.ofCharArray a).drop 1).toNat!
              if xnum != ynum then panic! "level one with mismatched numbers"
              out := out.insert v (.andlevel1 xnum)
          | _, _ => noop
        else out := out.insert v (.carry 0)
    | _ => noop
  return out

def getAndLevel2 (graph : Std.HashMap Wire Gate) (roles : Std.HashMap Wire Role := .empty) : Std.HashMap Wire Role := Id.run do
  let mut out : Std.HashMap Wire Role := roles
  for v in graph.keys do
    match graph[v]! with
    | .and a b c =>
          match roles[a]?, roles[b]? with
          | some (.xorlevel1 n), some (.carry m) =>
              if n != m+1 then panic! s!"and level two with mismatched numbers: {a} {b} {c}"
              out := out.insert v (.andlevel2 n)
          | r, some (.xorlevel1 n) =>
              match r with
              | some (.carry m) =>
                if n != m+1 then panic! s!"and level two with mismatched numbers: {a} {b} {c}"
                out := out.insert v (.andlevel2 n)
              | _ => noop
          | _, _ => noop
    | _ => noop
  return out

def getRole (graph : Std.HashMap Wire Gate) (roles : Std.HashMap Wire Role) (w : Wire) : Except String Role := do
  if !graph.contains w then
    match w[0]! with
    | 'x' =>
        let num := ((String.ofCharArray w).drop 1).toNat!
        return .xinput num
    | 'y' =>
        let num := ((String.ofCharArray w).drop 1).toNat!
        return .yinput num
    | _ => throw "input is neither x nor y"
  match graph[w]! with
  | .xor a b _ =>
      match roles[a]?, roles[b]? with
      | none, _ => throw "out of order"
      | some (.xinput 0), some (.yinput 0) => return .output 0
      | some (.xinput x), some (.yinput y) =>
          if x != y then throw s!"level one xor with mismatched numbers: gate {graph[w]!.toString}"
          return .xorlevel1 x
      | some (.yinput y), some (.xinput x) =>
          if x != y then throw s!"level one xor with mismatched numbers: gate {graph[w]!.toString}"
          return .xorlevel1 x
      | some (.xorlevel1 n), some (.carry m) =>
          if n != m then throw s!"XOR output level: mismatched numbers: gate {graph[w]!.toString} ({n}, {m})"
          if w[0]! != 'z' then throw s!"Output gate {graph[w]!.toString} not a z, num {n}"
          return .output n
      | some (.carry m), some (.xorlevel1 n) =>
          if n != m then throw s!"XOR output level: mismatched numbers: gate {graph[w]!.toString} ({n}, {m})"
          if w[0]! != 'z' then throw s!"Output gate {graph[w]!.toString} not a z, num {n}"
          return .output n
      | r1, r2 =>
          let s := graph[w]!.toString
          throw s!"XOR: illegal found, {s}, r1 = {repr r1}, r2 = {repr r2}"
  | .and a b _ =>
      match roles[a]?, roles[b]? with
      | none, _ => throw "out of order found"
      | some (.xinput 0), some (.yinput 0) => return .carry 1
      | some (.xinput x), some (.yinput y) =>
          if x != y then throw s!"level one AND with mismatched numbers: gate {graph[w]!.toString}"
          return .andlevel1 x
      | some (.yinput y), some (.xinput x) =>
          if x != y then throw s!"level one AND with mismatched numbers: gate {graph[w]!.toString}"
          return .andlevel1 x
      | some (.xorlevel1 x), some (.carry y) =>
          if x != y then throw s!"level one AND with mismatched numbers: gate {graph[w]!.toString}"
          return .andlevel2 x
      | some (.carry y), some (.xorlevel1 x) =>
          if x != y then throw s!"level one AND with mismatched numbers: gate {graph[w]!.toString}"
          return .andlevel2 x
      | r1, r2 =>
          let s := graph[w]!.toString
          throw s!"AND: illegal found, {s}, r1 = {repr r1}, r2 = {repr r2}"
  | .or a b _ =>
      match roles[a]!, roles[b]! with   -- FIXME
      | .andlevel1 n, .andlevel2 m =>
          if n != m then throw s!"OR output level: mismatched numbers: gate {graph[w]!.toString}"
          return .carry (n+1)
      | .andlevel2 m, .andlevel1 n =>
          if n != m then throw s!"OR output level: mismatched numbers: gate {graph[w]!.toString}"
          return .carry (n+1)
      | r1, r2 =>
          let s := graph[w]!.toString
          throw s!"OR: illegal found, {s}, r1 = {repr r1}, r2 = {repr r2}"

def getRoles (graph : Std.HashMap Wire Gate) (wires : Array Wire) : IO Unit := do
  let mut roles : Std.HashMap Wire Role := .empty
  for w in wires do
    match getRole graph roles w with
    | .ok role =>
       if graph.contains w then IO.println s!"{graph[w]!.toString}, role {repr role}"
       roles := roles.insert w role
    | .error s =>
       IO.println s
       return


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
  --let lc00 := (lightcone graph "z00".toCharArray).runState .empty
  --let lc01 := (lightcone graph "z01".toCharArray).runState .empty
  --let lc02 := (lightcone graph "z02".toCharArray).runState .empty

  --let mut roles := getXorLevel1 graph
  --roles := getAndLevel1 graph roles
  --roles := getAndLevel2 graph roles
  --IO.print (repr roles)
  --IO.println roles.size
  getRoles graph sortedwires
  return "foo"

--#eval secondPart testinput1           --(ans: )
--#eval secondPart testinput2           --(ans: )
--#eval secondPart realinput           --(ans: )

end Day24

/-
Bad gates:
shh should be andlevel2 21, swapped with output 21?
jsq AND vcj -> z21

- swap 1; shh and z21
- swap 2: dtk and vgs
- swap 3: dqr and z33
- swap 4: pfw and z39
-/

--#eval #["shh", "z21", "dtk", "vgs", "dqr", "z33", "pfw", "z39"].qsortOrd  -- dqr,dtk,pfw,shh,vgs,z21,z33,z39
