/- I should use the following, but changing priorities is not
implemented yet -/

--abbrev PriorityQueue (α : Type _) [Ord α] (β : Type _) :=
--  Batteries.BinomialHeap (α × β) (fun x y => compare x.1 y.1 != .gt)

abbrev PriorityQueue (α : Type _) [Ord α] (β : Type _) := List (α × β)

namespace PriorityQueue

variable [Ord α]

def empty : PriorityQueue α β := []

def insert [BEq β] (q : PriorityQueue α β) (p : α) (x : β) : PriorityQueue α β :=
  match q with
  | [] => [⟨p, x⟩]
  | ⟨p', x'⟩ :: tail =>
      match compare p p' with
      | .gt => ⟨p', x'⟩ :: PriorityQueue.insert tail p x
      | _ => if x != x' then ⟨p, x⟩ :: ⟨p', x'⟩ :: tail else ⟨p, x⟩ :: tail

def extractMin (q : PriorityQueue α β) : Option (α × β) := q.head?

-- Only acts on the first one it finds
def deleteElem [BEq β] (q : PriorityQueue α β) (x : β) : PriorityQueue α β :=
  match q with
  | [] => []
  | ⟨p', x'⟩ :: tail =>
      if x != x' then ⟨p', x'⟩ :: deleteElem tail x
      else tail

def deleteElemIfAbove [BEq β] (q : PriorityQueue α β) (prio : α) (x : β) : PriorityQueue α β :=
  match q with
  | [] => []
  | ⟨p', x'⟩ :: tail =>
      if x != x' then ⟨p', x'⟩ :: deleteElemIfAbove tail prio x
      else
        if compare prio p' == .lt then tail else q

def insertOrLowerPriority [BEq β] (q : PriorityQueue α β) (p : α) (x : β) :
    PriorityQueue α β :=
  let q' := q.deleteElemIfAbove p x
  q'.insert p x

end PriorityQueue
