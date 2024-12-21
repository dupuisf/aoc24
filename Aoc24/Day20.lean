import Aoc24.Utils
import Aoc24.Direction
import Aoc24.Graphs

-- https://www.dorais.org/lean4-parser/doc/

open System Parser

namespace Day20

def testinput1 : FilePath := "input_20_test1"
def testinput2 : FilePath := "input_20_test2"
def realinput : FilePath := "input_20"

/-
PART 1:
-/

def getNeighbors (graph : Vector₂ Char n m) (pos : Nat × Nat) (_ : Nat) : Array NSEW := Id.run do
  let mut out := #[]
  for dir in [NSEW.n, .s, .e, .w] do
    match dir.stepNat? pos.1 pos.2 1 with
    | none => noop
    | some ⟨ny, nx⟩ =>
        if ny < n && nx < m && graph[ny]![nx]! != '#' then out := out.push dir
  return out

def getNeighborsInclWalls (radius : Nat) (_ : Vector₂ Char n m) (pos : Nat × Nat) (dist : Nat) : Array NSEW := Id.run do
  if radius ≤ dist then return #[]
  let mut out := #[]
  for dir in [NSEW.n, .s, .e, .w] do
    match dir.stepNat? pos.1 pos.2 1 with
    | none => noop
    | some ⟨ny, nx⟩ =>
        if ny < n && nx < m then out := out.push dir
  return out

def getCheats (graph : Vector₂ Char n m) (src : Nat × Nat) (radius : Nat) : Array (Nat × Nat × Nat) :=
  let dijkconfig : Dijkstra.Config (StateM (Array (Nat × Nat × Nat))) (Nat × Nat) NSEW (Vector₂ Char n m) Nat :=
  { graph := graph
    weight _ _ _ := 1
    target _ v dir := dir.step v.1 v.2 1
    add := (· + ·)
    le := (· ≤ ·)
    getNeighbors := getNeighborsInclWalls radius
    visit _ v dist := do
      if graph[v.1]![v.2]! != '#' && v != src then set ((← get).push ⟨dist, v⟩)
    earlyStop _ _ _ := false }
  let ⟨_, nhbs⟩ := (dijkconfig.run src 0).run .empty
  nhbs

inductive Edge where
| before (dist : Nat) : Edge
| during (dist : Nat) (tgt : Nat × Nat) : Edge
| after : Edge
deriving DecidableEq, Hashable

def getNeighbors₂ (radius : Nat) (g : ((Array (Nat × Nat)) × (Std.HashMap (Nat × Nat) Nat) × (Vector₂ Char n m)))
     (v : (Nat × Nat) × Fin 3) : Array Edge := Id.run do
  let ⟨pos, cheat⟩ := v
  let ⟨path, _, graph⟩ := g
  let distToE := path.size
  if graph[v.1.1]![v.1.2]! == 'E' then return #[]
  match cheat with
  | 0 => return (Array.range (distToE - 1)).map fun dist => .before dist
  | 1 =>
      let out := getCheats graph pos radius
      return out.map fun ⟨dist, w⟩ => .during dist w
  | 2 => return #[.after]

def main (input : FilePath) (savings : Nat) (radius : Nat) : IO Nat := do
  let raw := (← IO.FS.lines input)
  let some ⟨n, m, grid⟩ := raw.map (·.toCharArray) |>.toVector₂ | IO.exitWithError "parse error";
  let some ⟨sy, sx⟩ := grid.findElem 'S' | IO.exitWithError "Can't find start"
  let some ⟨ey, ex⟩ := grid.findElem 'E' | IO.exitWithError "Can't find end"
  let dijkconfig : Dijkstra.Config (StateM (Array (Nat × Nat))) (Nat × Nat) NSEW (Vector₂ Char n m) Nat :=
  { graph := grid
    weight _ _ _ := 1
    target _ v dir := dir.step v.1 v.2 1
    add := (· + ·)
    le := (· ≤ ·)
    getNeighbors := getNeighbors
    visit _ v _ := do set ((← get).push v)
    earlyStop g v _ := g[v.1]![v.2]! == 'E' }
  let ⟨distances, path⟩ := (dijkconfig.run ⟨sy, sx⟩ 0).run .empty
  let distToE := distances[(⟨ey, ex⟩ : Nat × Nat)]!
  let dfsconfig : DFS.Config Id ((Nat × Nat) × Fin 3) Edge ((Array (Nat × Nat)) × (Std.HashMap (Nat × Nat) Nat) × (Vector₂ Char n m)) Nat Nat :=
  { graph := ⟨path, distances, grid⟩
    weight g v e := match e with
                    | .before dist => dist
                    | .during dist _ => dist
                    | .after => distToE - g.2.1[v.1]!
    target g _ e := match e with
                    | .before dist => ⟨g.1[dist]!, 1⟩
                    | .during _ tgt => ⟨tgt, 2⟩
                    | .after => ⟨⟨ey, ex⟩, 2⟩
    add := (· + ·)
    getNeighbors := getNeighbors₂ radius
    preprocess _ _ _ := noop
    postprocess g v dist _ results :=
      if g.2.2[v.1.1]![v.1.2]! == 'E' && dist ≤ distToE - savings then 1
      else results.sum }
  let numcheats := (dfsconfig.run ⟨⟨sy, sx⟩, 0⟩ 0).run
  return numcheats

def firstPart (input : FilePath) (savings : Nat) : IO Nat :=
  main input savings 2

--#eval firstPart testinput1           --(ans: )
--#eval firstPart testinput2           --(ans: )
--#eval firstPart realinput           --(ans: )

/-
PART 2:
-/

def secondPart (input : FilePath) (savings : Nat) : IO Nat :=
  main input savings 20


--#eval secondPart testinput1           --(ans: )
--#eval secondPart testinput2           --(ans: )
--#eval secondPart realinput           --(ans: )

end Day20
