
inductive NSEW where
| n : NSEW
| s : NSEW
| e : NSEW
| w : NSEW
deriving Repr, Inhabited, DecidableEq, Hashable

namespace NSEW

instance : ToString NSEW where
  toString dir := match dir with | .n => "N" | .s => "S" | .e => "E" | .w => "W"

def rotateCW (dir : NSEW) : NSEW :=
  match dir with | .n => .e | .e => .s | .s => .w | .w => .n

def rotateCCW (dir : NSEW) : NSEW :=
  match dir with | .n => .w | .w => .s | .s => .e | .e => .n

def reverse (dir : NSEW) : NSEW :=
  match dir with | .n => .s | .s => .n | .e => .w | .w => .e

def foldM [Monad m] (f : α → NSEW → m α) (init : α) : m α := do
  let north ← f init .n
  let east ← f north .e
  let south ← f east .s
  let west ← f south .w
  return west

def fold (f : α → NSEW → α) (init : α) : α := foldM (m := Id) f init

def step [Add α] [Sub α] (dir : NSEW) (y x len : α) : α × α :=
  match dir with
  | .n => ⟨y - len, x⟩
  | .s => ⟨y + len, x⟩
  | .e => ⟨y, x + len⟩
  | .w => ⟨y, x - len⟩

def toNatCW (dir : NSEW) (start : NSEW) : Nat :=
  let d := match start with
           | .n => 0
           | .e => 1
           | .s => 2
           | .w => 3
  match dir with
  | .n => d % 4
  | .e => (d + 3) % 4
  | .s => (d + 2) % 4
  | .w => (d + 1) % 4

def toNatCCW (dir : NSEW) (start : NSEW) : Nat :=
  let d := match start with
           | .n => 0
           | .w => 1
           | .s => 2
           | .e => 3
  match dir with
  | .n => d % 4
  | .w => (d + 3) % 4
  | .s => (d + 2) % 4
  | .e => (d + 1) % 4

end NSEW

inductive Corner where
| tl : Corner
| tr : Corner
| bl : Corner
| br : Corner
deriving Repr, Inhabited, DecidableEq, Hashable
