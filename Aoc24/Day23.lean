import Aoc24.Utils
import Aoc24.Direction
import Aoc24.Graphs

-- https://www.dorais.org/lean4-parser/doc/

-- input 520 vertices, 3380 edges, regular graph, every vertex of degree 13
-- test input: 16 vertices of degree 4

open System Parser

namespace Day23

def testinput1 : FilePath := "input_23_test1"
def testinput2 : FilePath := "input_23_test2"
def realinput : FilePath := "input_23"

/-
PART 1:
-/

abbrev Vertex := Array Char

instance : Ord Vertex := Ord.arrayOrd
instance : Ord (Array Vertex) := Ord.arrayOrd

def parseEdge : StringParser (Vertex × Vertex) := do
  let c₁ ← Char.ASCII.alpha
  let c₂ ← Char.ASCII.alpha
  let _ ← Char.char '-'
  let c₃ ← Char.ASCII.alpha
  let c₄ ← Char.ASCII.alpha
  return ⟨#[c₁, c₂], #[c₃, c₄]⟩

def containsT (vs : Array Vertex) : Bool :=
  vs.foldl (init := false) fun acc cur => if cur[0]! == 't' then true else acc

partial def countTriangles (graph : Std.HashMap Vertex (Array Vertex)) (vs : Array Vertex) : Nat :=
  let v := vs[vs.size-1]!
  let steps := vs.size - 1
  let nhbs := graph[v]!
  if steps == 2 then
    if nhbs.contains vs[0]! && (containsT vs) then 1 else 0
  else
    nhbs.foldl (init := 0) fun acc cur =>
      if !vs.contains cur then acc + countTriangles graph (vs.push cur) else acc

partial def getTriangles (graph : Std.HashMap Vertex (Array Vertex)) (vs : Array Vertex) :
    Array (Array Vertex) :=
  let v := vs[vs.size-1]!
  let steps := vs.size - 1
  let nhbs := graph[v]!
  if steps == 2 then
    --if nhbs.contains vs[0]! && (containsT vs) then #[vs] else #[]
    if nhbs.contains vs[0]! then #[vs] else #[]
  else
    nhbs.foldl (init := #[]) fun acc cur =>
      if !vs.contains cur then acc ++ getTriangles graph (vs.push cur) else acc

def firstPart (input : FilePath) : IO Nat := do
  let raw := (← IO.FS.lines input).map (·.yoloParse parseEdge)
  let graph : Std.HashMap Vertex (Array Vertex):= raw.foldl (init := .empty) fun acc cur =>
    let ⟨src, tgt⟩ := cur
    (acc.push src tgt).push tgt src
  let vertices : Std.HashSet Vertex := .ofList graph.keys
  let triangles : Std.HashSet (Array Vertex) := vertices.fold (init := .empty) fun acc cur =>
    let fromCur := (getTriangles graph #[cur]).map Array.qsortOrd
    fromCur.foldl (init := acc) fun acc' cur' => acc'.insert cur'
  return (triangles.filter containsT).size

--#eval firstPart testinput1           --(ans: )
--#eval firstPart testinput2           --(ans: )
--#eval firstPart realinput           --(ans: )

/-
PART 2:
-/

def _root_.String.V (str : String) : Vertex := str.toCharArray

def _root_.Std.HashSet.intersect [BEq α] [Hashable α] (s₁ s₂ : Std.HashSet α) : Std.HashSet α :=
  s₁.fold (init := .empty) fun acc cur => if s₂.contains cur then acc.insert cur else acc

def walkStep (graph : Std.HashMap Vertex (Array Vertex)) (set : Std.HashSet Vertex) :
    Std.HashSet Vertex :=
  set.fold (init := set) fun acc cur =>
    graph[cur]!.foldl (init := acc) fun acc' cur' => acc'.insert cur'

def printClique (clique : Std.HashSet Vertex) : String := Id.run do
  let mut out := ""
  let strings := (clique.toArray.map fun v => String.ofCharArray v).qsortOrd
  out := out ++ strings[0]!
  for i in [1:strings.size] do
    out := out ++ s!",{strings[i]!}"
  return out

def checkClique (graph : Std.HashMap Vertex (Array Vertex)) (clique : Std.HashSet Vertex) : Bool := Id.run do
  let mut out := true
  for v in clique do
    for w in clique do
      if v != w then
        if !graph[v]!.contains w then out := false
  return out

def secondPart (input : FilePath) : IO String := do
  let raw := (← IO.FS.lines input).map (·.yoloParse parseEdge)
  let graph : Std.HashMap Vertex (Array Vertex):= raw.foldl (init := .empty) fun acc cur =>
    let ⟨src, tgt⟩ := cur
    (acc.push src tgt).push tgt src
  let vertices : Std.HashSet Vertex := .ofList graph.keys
  --IO.println s!"number of vertices: {vertices.size}"
  --let degrees : Std.HashMap Nat Nat := vertices.fold (init := .empty) fun acc cur =>
  --  acc.insertOrModify graph[cur]!.size (· + 1) 1
  --IO.print (repr degrees)
  --let mut blowups : Std.HashMap Nat Nat := .empty
  let mut win : Std.HashSet Vertex := .empty
  for v in vertices do
    for w in graph[v]! do
      let vstep := walkStep graph (.ofList [v])
      let wstep := walkStep graph (.ofList [w])
      let intersection := vstep.intersect wstep
      if intersection.size == 13 then -- we have a candidate clique
        if checkClique graph intersection then
          win := intersection
  return (printClique win)

--#eval secondPart testinput1           --(ans: )
--#eval secondPart testinput2           --(ans: )
--#eval secondPart realinput           --(ans: )

end Day23
