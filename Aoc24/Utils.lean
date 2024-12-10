import Init.Data.Array.Lemmas
import Init.Data.Vector.Basic
import Parser
import Std.Data.HashMap.Lemmas

--notation "Array₂ " α => Array (Array α)
abbrev Array₂ (α : Type _) := Array (Array α)
abbrev Vector₂ (α : Type _) (n m : Nat) := Vector (Vector α m) n

macro_rules | `(tactic| get_elem_tactic_trivial) => `(tactic| apply Std.HashMap.mem_keys.mp; assumption)

section general

def checkThat {α : Type _} (x : α) (p : α → Prop) [∀ a, Decidable (p a)] :
    Option (PLift (p x)) :=
  if h : p x then some ⟨h⟩
  else none

def Array.checkThatAll {α : Type _} (xs : Array α) (p : α → Prop) [∀ a, Decidable (p a)] :
    Option (PLift (∀ i, (h : i < xs.size) → p xs[i])) :=
  match h : xs.all p with
  | false => none
  | true =>
      have hmain : ∀ (i : Fin xs.size), p xs[i] := by
        have htmp := (xs.all_eq_true).mp h
        simpa [decide_eq_true_iff] using htmp
      some ⟨fun i hi => hmain ⟨i, hi⟩⟩

def Array.checkThatUpTo {α : Type _} (xs : Array α) (n : Nat) (hn : n ≤ xs.size) (p : α → Prop)
    [∀ a, Decidable (p a)] :
    Option (PLift (∀ i, (h : i < n) → p (xs[i]'(Nat.lt_of_lt_of_le h hn)))) :=
  if hzero : xs.size = 0 then
    have hmain : ∀ i, (h : i < n) → p (xs[i]'(Nat.lt_of_lt_of_le h hn)) := by
      intro i hi
      have : i < 0 := by
        calc i < n := hi
             _ ≤ xs.size := hn
             _ = 0 := hzero
      exact False.elim <| Nat.not_lt_zero i this
    some ⟨hmain⟩
  else
    match h : xs.all p (start := 0) (stop := n) with
    | false => none
    | true =>
        have hmain := by
          have htmp := (xs.all_iff_forall).mp h
          simpa [decide_eq_true_iff] using htmp
        have hmain' (i : Nat) (hi : i < n) : p (xs[i]'(Nat.lt_of_lt_of_le hi hn)) := by
          refine hmain ⟨i, Nat.lt_of_lt_of_le hi hn⟩ ?_
          exact hi
        some ⟨hmain'⟩

end general

namespace Char

def toNatDigit (c : Char) : Nat :=
  c.toNat - 48

def toNatDigit? (c : Char) : Option Nat :=
  if c.isDigit then some c.toNatDigit else none

end Char

namespace String

def ofCharList (l : List Char) : String :=
  match l with
  | [] => ""
  | [c] => c.toString
  | c :: tail => c.toString ++ ofCharList tail

def toCharArray (s : String) : Array Char := s.data.toArray

def ofCharArray (a : Array Char) : String := { data := a.toList }

end String

namespace Parser

abbrev StringParser := TrivialParser Substring Char

def RegEx.takeStr (re : RegEx Char) : StringParser String :=
  return String.ofCharList (← re.take)

def _root_.String.yoloParse [Inhabited α] (str : String) (p : StringParser α) : α :=
  match Parser.run p str with
  | .ok _ res => res
  | .error _ _ => panic! "Parse error!"

def _root_.String.parse? [Inhabited α] (str : String) (p : StringParser α) : Option α :=
  match Parser.run p str with
  | .ok _ res => some res
  | .error _ _ => none

end Parser

namespace Array

def sum [Add α] [OfNat α 0] (a : Array α) : α := a.foldl (init := 0) (· + ·)

/-- Search for an element in an array that is sorted by the value of `f`. -/
partial def binSearchMap [Inhabited α] [Ord β] (as : Array α) (k : β) (f : α → β) (lo : Nat := 0)
    (hi : Nat := as.size - 1) : Option α :=
  if lo ≤ hi then
    let _ : LT β := ltOfOrd
    let m := (lo + hi)/2
    let a := as[m]!
    if f a < k then binSearchMap as k f (m+1) hi
    else if k < f a then
      if m == 0 then none
      else binSearchMap as k f lo (m-1)
    else some a
  else none

/-- Search for the first element that satisfies `p : α → Bool` (assumed to be monotone) in an array
that is sorted by the value of `f`. Returns the position if one such element is found. -/
partial def binSearchMapSat [Inhabited α] [Ord β] (as : Array α) (p : α → Bool) (f : α → β)
    (lo : Nat := 0) (hi : Nat := as.size - 1) : Option Nat :=
  if lo = hi then
    if p as[lo]! then some lo else none
  else if lo < hi then
    let _ : LT β := ltOfOrd
    let m := (lo + hi)/2
    let a := as[m]!
    if p a then binSearchMapSat as p f lo m
    else binSearchMapSat as p f (m+1) hi
  else none

def max [Inhabited α] [Max α] (a : Array α) : α :=
  if h : a.size = 0 then
    default
  else
    have : 0 < a.size := Nat.pos_of_ne_zero h
    a.foldl (init := a[0]) Max.max

def findIdx! (as : Array α) (p : α → Bool) : Nat :=
  match as.findIdx? p with
  | some x => x
  | none => panic!"Element not found"

def filterWithIdx (as : Array α) (p : Nat → α → Bool) : Array α :=
  (·.2) <| as.foldl (init := (0, Array.empty)) fun (idx, r) a =>
    if p idx a then
      (idx+1, r.push a)
    else
      (idx+1, r)

def foldlIdx (as : Array α) (f : Nat → β → α → β) (init : β) : β :=
  (as.foldl (β := β × Nat) (init := ⟨init, 0⟩) fun acc elem => ⟨f acc.2 acc.1 elem, acc.2 + 1⟩).1

def mkArray₂ (m n : Nat) (v : α) : Array (Array α) :=
  Array.mkArray m (Array.mkArray n v)

def foldtlM [Monad m] (f : β → α → m β) (init : β) (a : Array (Array α)) : m β :=
  a.foldlM (fun x row => row.foldlM f x) init

def foldtl (f : β → α → β) (init : β) (a : Array (Array α)) : β :=
  a.foldl (fun x row => row.foldl f x) init

def transpose [Inhabited α] (as : Array₂ α) : Option (Array₂ α) := do
  let dim := as.size
  if hdim : dim ≤ 0 then
    return #[]
  else
    have _ := Nat.lt_of_not_ge hdim
    let width := as[0].size
    let some ⟨_⟩ := as.checkThatAll fun row => row.size = width | failure
    let mut output : Array₂ α := #[]
    for i in [0:width] do
      let curCol := as.map (fun row => row[i]!)
      output := output.push curCol
    return output

def zipWith2D (a : Array (Array α)) (b : Array (Array β)) (f : α → β → γ) : Array (Array γ) :=
  a.zipWith b (fun ra rb => ra.zipWith rb f)

def modify₂ (a : Array (Array α)) (i j : Nat) (f : α → α) : Array (Array α) :=
  a.modify i (·.modify j f)

def get₂! [Inhabited α] (a : Array₂ α) (i j : Nat) : α :=
  (a.get! i).get! j

def set₂ (a : Array (Array α)) (i j : Nat) (x : α) : Array (Array α) :=
  a.modify i (·.modify j (fun _ => x))

def containsAny (as : Array α) (p : α → Bool) : Bool := Id.run do
  for a in as do
    if p a then return true
  return false

def last? (as : Array α) : Option α := as[as.size-1]?

def last (as : Array α) (h : 0 < as.size) : α := as[as.size-1]

def drop (as : Array α) (n : Nat) : Array α := Id.run do
  let mut out := #[]
  for h : i in [n:as.size] do
    out := out.push as[i]
  return out

def maybePush (as : Array α) (a? : Option α) : Array α :=
  match a? with
  | none => as
  | some x => as.push x

def best? (as : Array α) (keep : α → α → α) : Option α :=
  as.foldl (init := none) fun acc x => match acc with
                                       | none => some x
                                       | some z => some (keep z x)

def count (as : Array α) (p : α → Bool) : Nat :=
  as.foldl (init := 0) fun acc x => if p x then acc + 1 else acc

def getAllIdx (as : Array α) (p : α → Bool) : Array Nat :=
  as.foldlIdx (init := #[]) fun i ar elem => if p elem then ar.push i else ar

def foldlMSlidingWinIdx [Monad m] (as : Array α) (n : Nat) (init : β)
    (f : β → Array α → Nat → m β) : m β := do
  let out ← as.foldlM (init := (⟨init, ⟨#[], 0⟩⟩ : β × Array α × Nat)) fun (st : β × Array α × Nat) a => do
    let newwin : Array α := if st.2.1.size = n then (st.2.1.drop 1).push a else st.2.1.push a
    return ⟨← f st.1 newwin st.2.2, ⟨newwin, st.2.2 + 1⟩⟩
  return out.1

def foldlSlidingWinIdx (as : Array α) (n : Nat) (init : β)
    (f : β → Array α → Nat → β) : β :=
  as.foldlMSlidingWinIdx (m := Id) n init f

def toVector (as : Array α) : Σ n : Nat, (Vector α n) := ⟨as.size, ⟨as, rfl⟩⟩

def toVector' (as : Array α) (n : Nat) : Option (Vector α n) :=
  match checkThat as (fun bs => bs.size = n) with
  | none => none
  | some ⟨hmain⟩ => some ⟨as, hmain⟩

def toVector₂ (as : Array₂ α) : Option (Σ (n m : Nat), Vector₂ α n m) := do
  if h : 0 < as.size then
    let m := as[0].size
    let n := as.size
    let as' ← as.mapM (m := Option) fun a => do
      let out ← a.toVector' m
      return out
    let out ← as'.toVector' n
    return ⟨n, m, out⟩
  else
    return ⟨0, 0, #v[]⟩

def toVector₂' (as : Array₂ α) (n m : Nat) : Option (Vector₂ α n m) := do
  let as' ← as.mapM fun a => return ← a.toVector' m
  return ← as'.toVector' n

end Array

namespace Array₂

def printBoolGrid (grid : Array₂ Bool) : IO Unit := do
  for ln in grid do
    let charline := ln.map fun b => if b then '#' else '·'
    let str := String.ofCharArray charline
    IO.println str

def printCharGrid (grid : Array₂ Char) : IO Unit := do
  for ln in grid do
    let str := String.ofCharArray ln
    IO.println str

end Array₂

namespace Vector₂

def set (v : Vector₂ α n m) (i j : Nat) (x : α) (hi : i < n := by get_elem_tactic)
    (hj : j < m := by get_elem_tactic) : Vector₂ α n m :=
  Vector.set v i (v[i].set j x)

def setIfInBounds (v : Vector₂ α n m) (i j : Int) (x : α) : Vector₂ α n m := Id.run do
  let some i' := i.toNat' | return v
  let some j' := j.toNat' | return v
  if hi : i' < n then
    if hj : j' < m then
      return v.set i' j' x
  return v

def set! [Inhabited α] (v : Vector₂ α n m) (i j : Nat) (x : α) : Vector₂ α n m :=
  Vector.set! v i (v[i]!.set! j x)

def map (v : Vector₂ α n m) (f : α → β) : Vector₂ β n m :=
  Vector.map (fun w => w.map f) v

def zipWith (a : Vector₂ α n m) (b : Vector₂ β n m) (f : α → β → γ) : Vector₂ γ n m :=
  Vector.zipWith a b (fun x y => x.zipWith y f)

def mkVector₂ (n m : Nat) (v : α) : Vector₂ α n m :=
  Vector.mkVector n (Vector.mkVector m v)

def toArray₂ (a : Vector₂ α n m) : Array₂ α :=
  a.toArray.map Vector.toArray

def printBoolGrid (grid : Vector₂ Bool n m) : IO Unit :=
  grid.toArray₂.printBoolGrid

def printCharGrid (grid : Vector₂ Char n m) : IO Unit :=
  grid.toArray₂.printCharGrid

end Vector₂


namespace Std.HashMap

variable [BEq α] [Hashable α]

def push (m : Std.HashMap α (Array β)) (a : α) (b : β) : Std.HashMap α (Array β) :=
  m.alter a fun bs =>
    match bs with
    | none => #[b]
    | some bs' => bs'.push b

end Std.HashMap

/- Stuff about the state monad. -/
namespace StateM

def runState (x : StateM σ α) (s : σ) : σ := (x.run s).2

end StateM

section misc

def Array.toCharGrid (lines : Array String) : Option (Σ (n m : Nat), Vector₂ Char n m) :=
  (lines.map (·.toCharArray)).toVector₂

end misc
