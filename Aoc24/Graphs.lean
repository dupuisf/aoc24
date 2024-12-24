import Aoc24.Utils

open Parser

structure AdjacencyHashMap (α β : Type _) [DecidableEq α] [Hashable α] [LawfulHashable α] where
  V : Std.HashMap α (Array (α × β))
  edges_lawful : ∀ (v : α) (hv : v ∈ V), ∀ e ∈ V[v], e.1 ∈ V

structure AdjacencyArray (β : Type _) (n : Nat) where
  V : Vector (Array ((Fin n) × β)) n

namespace AdjacencyArray

def ofArray (g : Array (Array (Nat × β))) : Option (Σ n, AdjacencyArray β n) := do
  let n := g.size
  let g₁ : Array (Array (Fin n × β)) ← g.mapM (m := Option) fun as => as.mapM fun ⟨v, d⟩ => do
    let ⟨h⟩ ← checkThat v (fun z => z < n)
    return (⟨⟨v, h⟩, d⟩ : Fin n × β)
  let some ⟨h₀⟩ := checkThat g₁ (fun z => z.size = n) | failure
  let g₂ : Vector (Array (Fin n × β)) n := ⟨g₁, h₀⟩
  return ⟨n, ⟨g₂⟩⟩

structure DFSData (β : Type _) (n : Nat) where
  graph : AdjacencyArray β n
  visited : Std.HashSet (Fin n)

end AdjacencyArray

/-
DFS (where we find all paths)
-/

namespace DFS

structure Config (m : Type _ → Type _) [Monad m] (V : Type _) (E : Type _) (G : Type _) (R : Type _) (α : Type _) where
  graph : G
  weight : G → V → E → R
  target : G → V → E → V
  add : R → R → R
  getNeighbors : G → V → Array E
  preprocess : G → V → R → m Unit
  postprocess : G → V → R → Array E → Array α → m α
deriving Inhabited

@[specialize, inline]
partial def Config.run [Monad m] [BEq V] [Hashable V] [Inhabited α] (config : Config m V E G R α) (v : V) (dist : R)
    (visited : Std.HashSet V := .empty) : m α := do
  config.preprocess config.graph v dist
  let nhbs := config.getNeighbors config.graph v
  let outputs ← nhbs.filterMapM fun e => do
    let tgt := config.target config.graph v e
    let weight := config.weight config.graph v e
    if !visited.contains tgt then
      return some (← config.run tgt (config.add dist weight) (visited.insert v))
    else
      return none
  config.postprocess config.graph v dist nhbs outputs

end DFS

/-
Dijkstra
-/

namespace Dijkstra

structure Config (m : Type _ → Type _) [Monad m] (V : Type _) (E : Type _) (G : Type _) (R : Type _) where
  graph : G
  weight : G → V → E → R
  target : G → V → E → V
  add : R → R → R
  le : R → R → Bool
  getNeighbors : G → V → R → Array E
  visit : G → V → R → m Unit
  earlyStop : G → V → R → Bool
deriving Inhabited

structure DijkstraData (m : Type _ → Type _) (V : Type _) (E : Type _) (G : Type _) (R : Type _) [Monad m] [BEq V] [Hashable V] where
  config : Config m V E G R
  queue : Batteries.BinomialHeap (R × V) (fun ⟨p, _⟩ ⟨q, _⟩ => config.le p q)
  visited : Std.HashMap V R

variable [BEq V] [Hashable V] [Monad m]

@[specialize, inline]
def popQueue : StateT (DijkstraData m V E G R) m (Option (R × V)) := do
  let data ← get
  match data.queue.deleteMin with
  | none => return none
  | some ⟨elem, q'⟩ =>
      set (σ := DijkstraData m V E G R) { data with queue := q' }
      return some elem

@[specialize, inline]
def requeue (prio : R) (v : V) : StateT (DijkstraData m V E G R) m Unit := do
  let data ← get
  let queue' := data.queue.insert ⟨prio, v⟩
  set (σ := DijkstraData m V E G R) { data with queue := queue' }

@[specialize, inline]
def visit (v : V) (dist : R) : StateT (DijkstraData m V E G R) m Unit := do
  let data ← get
  let nvisited := data.visited.insert v dist
  set (σ := DijkstraData m V E G R) { data with visited := nvisited }

--variable [ToString V] [ToString R]

@[specialize, inline]
partial def dijkstraAux : StateT (DijkstraData m V E G R) m Unit := do
  let some ⟨dist, v⟩ ← popQueue | return
  let ⟨config, _, visited⟩ ← get
  if visited.contains v then dijkstraAux
  else
    visit v dist
    config.visit config.graph v dist
    if config.earlyStop config.graph v dist then return
    (config.getNeighbors config.graph v dist).foldlM (init := ⟨⟩) fun _ e =>
      let nv := config.target config.graph v e
      let ndist := config.add dist (config.weight config.graph v e)
      requeue ndist nv
    dijkstraAux

@[specialize, inline]
def Config.run (config : Config m V E G R) (start : V) (zero : R) : m (Std.HashMap V R) := do
  let data : DijkstraData m V E G R :=
    { config := config
      queue := Batteries.BinomialHeap.empty.insert ⟨zero, start⟩
      visited := .empty }
  let ⟨_, data'⟩ ← dijkstraAux.run data
  return data'.visited

end Dijkstra

namespace TopologicalSort

structure Config (V : Type _) (G : Type _) where
  startvertices : Array V  -- full set of start vertices
  graph : G
  getNeighbors : G → V → Array V
deriving Inhabited

structure SortData (V : Type _) (G : Type _) [BEq V] [Hashable V] where
  config : Config V G
  visited : Std.HashSet V
  sorted : Array V   -- sorted backwards during the algo

variable [BEq V] [Hashable V]

@[specialize, inline]
def visit (v : V) : StateM (SortData V G) Unit := do
  let data ← get
  let nvisited := data.visited.insert v
  set (σ := SortData V G) { data with visited := nvisited }

@[specialize, inline]
def addtosorted (v : V) : StateM (SortData V G) Unit := do
  let data ← get
  let nsorted := data.sorted.push v
  set (σ := SortData V G) { data with sorted := nsorted }

partial def sortFrom (v : V) : StateM (SortData V G) Unit := do
  let ⟨config, visited, _⟩ ← get
  if visited.contains v then return
  visit v
  let nhbs := config.getNeighbors config.graph v
  for w in nhbs do
    sortFrom w
  addtosorted v

def sortAux : StateM (SortData V G) Unit := do
  let ⟨config, visited, _⟩ ← get
  for v in config.startvertices do
    if !visited.contains v then sortFrom v

def Config.sort (config : Config V G) : Array V :=
  let data : SortData V G := ⟨config, .empty, #[]⟩
  let ⟨_, _, sorted⟩ := sortAux.runState data
  sorted.reverse

end TopologicalSort
