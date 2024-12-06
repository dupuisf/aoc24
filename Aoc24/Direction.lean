
inductive NSEW where
| n : NSEW
| s : NSEW
| e : NSEW
| w : NSEW
deriving BEq, Repr, Inhabited, DecidableEq, Hashable

namespace NSEW

def rotateCW (dir : NSEW) : NSEW :=
  match dir with | .n => .e | .e => .s | .s => .w | .w => .n

def rotateCCW (dir : NSEW) : NSEW :=
  match dir with | .n => .w | .w => .s | .s => .e | .e => .n

def reverse (dir : NSEW) : NSEW :=
  match dir with | .n => .s | .s => .n | .e => .w | .w => .e

end NSEW
