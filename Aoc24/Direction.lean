
inductive NSEW where
| n : NSEW
| s : NSEW
| e : NSEW
| w : NSEW
deriving BEq, Repr, Inhabited, DecidableEq, Hashable

namespace NSEW

instance : ToString NSEW where
  toString dir := match dir with | .n => "N" | .s => "S" | .e => "E" | .w => "W"

def rotateCW (dir : NSEW) : NSEW :=
  match dir with | .n => .e | .e => .s | .s => .w | .w => .n

def rotateCCW (dir : NSEW) : NSEW :=
  match dir with | .n => .w | .w => .s | .s => .e | .e => .n

def reverse (dir : NSEW) : NSEW :=
  match dir with | .n => .s | .s => .n | .e => .w | .w => .e

def fold (f : α → NSEW → α) (init : α) : α :=
  f (f (f (f init .n) .e) .s) .w

def step (dir : NSEW) (y x : Int) (len : Nat) : Int × Int :=
  match dir with
  | .n => ⟨y - len, x⟩
  | .s => ⟨y + len, x⟩
  | .e => ⟨y, x + len⟩
  | .w => ⟨y, x - len⟩

end NSEW
