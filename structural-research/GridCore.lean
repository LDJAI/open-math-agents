import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise

namespace GridCounter

/-- Row-major index of the left endpoint of horizontal edge i. Vertical
edge i starts at vertex i, and ends n+1 positions later. -/
def hOrigin (n i : Nat) : Nat := (i/n)*(n+1) + i%n

/-- A mask whose set bits are the supplied vertex indices. -/
def positions (xs : List Nat) : Nat := xs.foldr (fun k bits => bits ||| (1 <<< k)) 0

def horizontalMask (n : Nat) (deleted : List Nat) : Nat :=
  positions (((List.range (n*(n+1))).filter (fun e => !deleted.contains e)).map (hOrigin n))

def verticalMask (n : Nat) (deleted : List Nat) : Nat :=
  positions ((List.range (n*(n+1))).filter (fun e => !deleted.contains e))

/-- One undirected nearest-neighbor expansion, retaining the current vertices. -/
def expand (n H V s : Nat) : Nat :=
  s ||| ((s &&& H) <<< 1) ||| ((s >>> 1) &&& H) |||
      ((s &&& V) <<< (n+1)) ||| ((s >>> (n+1)) &&& V)

def rounds (n H V : Nat) : Nat → Nat → Nat
  | 0, s => s
  | k+1, s =>
    let u := expand n H V s
    if u == s then s else rounds n H V k u

def forward (n : Nat) (hdel vdel : List Nat) (x y : Nat) : Bool :=
  (rounds n (horizontalMask n hdel) (verticalMask n vdel) ((n+1)*(n+1)) 1).testBit (y*(n+1)+x)

/-- Increasing lists describing each choice of exactly k distinct deleted edges once. -/
def choices (n k : Nat) : List (List Nat) := (List.range (n*(n+1))).sublistsLen k

/-- Enumerate spanning subgraphs by the complements of their horizontal and vertical
edge sets. m,p count retained edges. -/
def count (n x y m p : Nat) : Nat :=
  let N := n*(n+1)
  if m > N || p > N then 0 else
  ((choices n (N-m)).map fun h => ((choices n (N-p)).filter fun v => forward n h v x y).length).sum

end GridCounter
