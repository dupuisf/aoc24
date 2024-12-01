import Init.Data.Array.Lemmas

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

end Array
