import OMAStatements.S_mo_15242
import Mathlib.Data.Nat.Bitwise
import Mathlib.Logic.Function.Iterate
import Mathlib.Combinatorics.SimpleGraph.Paths

/-! Disproof of the finite square-grid comparison, https://mathoverflow.net/questions/15242.
Credit: @LDJAI. At target (2,4) in the 5-by-5 grid, the two connection counts differ by one. -/

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

namespace GridCounter

/-- Edges represented by the two endpoint masks, with both traversal directions. -/
def edge (n H V a b : Nat) : Prop :=
  (b = a+1 ∧ H.testBit a) ∨ (a = b+1 ∧ H.testBit b) ∨
  (b = a+(n+1) ∧ V.testBit a) ∨ (a = b+(n+1) ∧ V.testBit b)

/-- At most k edges are used, with an initial set of vertices encoded by the bit mask s. -/
def boundedWalk (n H V s : Nat) : Nat → Nat → Prop
  | 0, b => s.testBit b
  | k+1, b => boundedWalk n H V s k b ∨ ∃ a, boundedWalk n H V s k a ∧ edge n H V a b

theorem expand_correct (n H V s b : Nat) :
    (expand n H V s).testBit b ↔ s.testBit b ∨ ∃ a, s.testBit a ∧ edge n H V a b := by
  simp only [expand, Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft,
    Nat.testBit_shiftRight, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · intro h
    rcases h with ((((hs|hr)|hl)|hd)|hu)
    · exact Or.inl hs
    · exact Or.inr ⟨b-1,hr.2.1,Or.inl ⟨by omega,hr.2.2⟩⟩
    · exact Or.inr ⟨1+b,hl.1,Or.inr (Or.inl ⟨by omega,hl.2⟩)⟩
    · exact Or.inr ⟨b-(n+1),hd.2.1,Or.inr (Or.inr (Or.inl ⟨by omega,hd.2.2⟩))⟩
    · exact Or.inr ⟨n+1+b,hu.1,Or.inr (Or.inr (Or.inr ⟨by omega,hu.2⟩))⟩
  · rintro (hs|⟨a,hs,he⟩)
    · exact Or.inl (Or.inl (Or.inl (Or.inl hs)))
    · rcases he with ⟨e,h⟩ | ⟨e,h⟩ | ⟨e,h⟩ | ⟨e,h⟩
      · subst b; exact Or.inl (Or.inl (Or.inl (Or.inr ⟨by omega, by simpa using hs, by simpa using h⟩)))
      · subst a; exact Or.inl (Or.inl (Or.inr ⟨by simpa [Nat.add_comm] using hs,h⟩))
      · subst b; exact Or.inl (Or.inr ⟨by omega, by simpa using hs, by simpa using h⟩)
      · subst a; exact Or.inr ⟨by simpa [Nat.add_comm] using hs,h⟩

theorem rounds_iterate (n H V k s : Nat) :
    rounds n H V k s = (expand n H V)^[k] s := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    rw [rounds, Function.iterate_succ_apply]
    by_cases h : expand n H V s = s
    · simp [h,Function.iterate_fixed h k]
    · simp [h,ih]

theorem rounds_correct (n H V s k b : Nat) :
    (rounds n H V k s).testBit b ↔ boundedWalk n H V s k b := by
  rw [rounds_iterate]
  induction k generalizing b with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', expand_correct]
    simp only [ih,boundedWalk]

theorem forward_walk (n : Nat) (hdel vdel : List Nat) (x y : Nat) :
    forward n hdel vdel x y ↔ boundedWalk n (horizontalMask n hdel) (verticalMask n vdel)
        1 ((n+1)*(n+1)) (y*(n+1)+x) := rounds_correct _ _ _ _ _ _

end GridCounter

namespace GridCounter


/-- Exact numbers of connected spanning subgraphs in the two orientations. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nineteen_eighteen : count 4 2 4 19 18 = 3780 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem eighteen_nineteen : count 4 2 4 18 19 = 3779 := by decide +kernel

def assertion : Prop :=
  ∀ n x y m p : Nat, x ≤ n → y ≤ n → x < y → p < m → count n x y m p ≤ count n x y p m

theorem disproof : ¬ assertion := by
  intro h
  have wrong := h 4 2 4 19 18 (by decide) (by decide) (by decide) (by decide)
  rw [nineteen_eighteen,eighteen_nineteen] at wrong
  exact (by decide : ¬(3780 ≤ 3779)) wrong

end GridCounter

namespace GridCounter

open OMA.S_mo_15242 hiding count

theorem mask_positions (xs : List Nat) (b : Nat) : (positions xs).testBit b ↔ b ∈ xs := by
  induction xs with
  | nil => simp [positions]
  | cons a xs ih =>
    change ((positions xs ||| (1 <<< a)).testBit b = true) ↔ _
    simp only [Nat.testBit_or, Bool.or_eq_true, Nat.one_shiftLeft, Nat.testBit_two_pow,
       decide_eq_true_eq, List.mem_cons, ih]
    exact ⟨fun h => h.elim Or.inr (fun e => Or.inl e.symm),
      fun h => h.elim (fun e => Or.inr e.symm) Or.inl⟩

theorem horizontal_bit (n : Nat) (h : List Nat) (a : Nat) :
    (horizontalMask n h).testBit a ↔
      ∃ i < n*(n+1), i ∉ h ∧ a = (i/n)*(n+1)+i%n := by
  rw [horizontalMask, mask_positions]
  simp only [List.mem_map, List.mem_filter, List.mem_range, Bool.not_eq_true',
    List.contains_eq_mem, decide_eq_false_iff_not]
  constructor
  · rintro ⟨i,⟨hi,hd⟩,e⟩
    exact ⟨i,hi,hd,e.symm⟩
  · rintro ⟨i,hi,hd,e⟩
    exact ⟨i,⟨hi,hd⟩,e.symm⟩

theorem vertical_bit (n : Nat) (v : List Nat) (a : Nat) :
    (verticalMask n v).testBit a ↔ a < n*(n+1) ∧ a ∉ v := by
  rw [verticalMask, mask_positions]
  simp

theorem edge_iff_adjacent (n : Nat) (h v : List Nat) (a b : Nat) :
    edge n (horizontalMask n h) (verticalMask n v) a b ↔ adjacent n h v a b := by
  simp only [edge, adjacent, horizontal_bit, vertical_bit]
  constructor
  · rintro (⟨h1,i,h2,h3,h4⟩|⟨h1,i,h2,h3,h4⟩|⟨h1,h2,h3⟩|⟨h1,h2,h3⟩)
    · exact Or.inl ⟨i,h2,h3,h4,h1⟩
    · exact Or.inr (Or.inl ⟨i,h2,h3,h4,h1⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨h2,h3,h1⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h2,h3,h1⟩))
  · rintro (⟨i,h2,h3,h4,h1⟩|⟨i,h2,h3,h4,h1⟩|⟨h2,h3,h1⟩|⟨h2,h3,h1⟩)
    · exact Or.inl ⟨h1,i,h2,h3,h4⟩
    · exact Or.inr (Or.inl ⟨h1,i,h2,h3,h4⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨h1,h2,h3⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h1,h2,h3⟩))

private theorem h_bounded {i n : Nat} (hi : i < n*(n+1)) :
    (i/n)*(n+1)+i%n+1 < size n := by
  have hn : 0 < n := by by_contra! h; simp_all
  have hm := Nat.mod_lt i hn
  have hd : i/n < n+1 := (Nat.div_lt_iff_lt_mul hn).2 (by rwa [Nat.mul_comm])
  have hh := Nat.mul_le_mul_right (n+1) (show i/n ≤ n by omega)
  simp only [size, Nat.add_mul, Nat.one_mul]
  omega

private theorem bounded_target {n a b : Nat} {h v : List Nat} (hh : adjacent n h v a b) :
    b < size n := by
  rcases hh with ⟨i, hi, _, ha, hb⟩ | ⟨i, hi, _, hb, _⟩ | ⟨ha, _, hb⟩ | ⟨hb, _, _⟩
  · rw [hb,ha]; exact h_bounded hi
  · have := h_bounded hi; omega
  · simp only [size, Nat.add_mul,Nat.one_mul]; omega
  · simp only [size, Nat.add_mul,Nat.one_mul]; omega

private theorem bounded_sound (n : Nat) (h v : List Nat) (k b : Nat)
    (hh : boundedWalk n (horizontalMask n h) (verticalMask n v) 1 k b) :
    ∃ t : Fin (size n), t.val=b ∧ (grid n h v).Reachable (origin n) t := by
  induction k generalizing b with
  | zero =>
    have hb := Nat.testBit_one_eq_true_iff_self_eq_zero.mp hh
    exact ⟨origin n,hb.symm,SimpleGraph.Reachable.rfl⟩
  | succ k ih =>
    rcases hh with hh | ⟨a,ha,hab⟩
    · exact ih b hh
    · obtain ⟨t, rfl, ht⟩ := ih a ha
      have hed := (edge_iff_adjacent n h v t b).1 hab
      let u : Fin (size n) := ⟨b, bounded_target hed⟩
      have he : (grid n h v).Adj t u := hed
      exact ⟨u,rfl,ht.trans he.reachable⟩

private theorem bounded_mono (n H V k l b : Nat) (hkl : k ≤ l)
    (hw : boundedWalk n H V 1 k b) : boundedWalk n H V 1 l b := by
  induction hkl with
  | refl => exact hw
  | step _ ih => exact Or.inl ih

private theorem walk_bounded {n : Nat} {h v : List Nat} {b a : Fin (size n)}
    (w : (grid n h v).Walk b a) (hr : a=origin n) :
    boundedWalk n (horizontalMask n h) (verticalMask n v) 1 w.length b.val := by
  induction w with
  | @nil u => subst u; exact Nat.testBit_one_zero
  | @cons a b c he w ih =>
    exact Or.inr ⟨b.val, ih hr, (edge_iff_adjacent n h v b a).2 (SimpleGraph.adj_symm _ he)⟩

theorem forward_connected (n : Nat) (h v : List Nat) (x y : Nat) :
    forward n h v x y ↔ connectedTo n h v x y := by
  rw [forward_walk]
  constructor
  · exact bounded_sound n h v _ _
  · rintro ⟨t, et, ht⟩
    obtain ⟨w, hw⟩ := ht.symm.exists_isPath
    have hl : w.length < size n := by simpa using hw.length_lt
    rw [← et]
    exact bounded_mono _ _ _ _ _ _ hl.le (walk_bounded w rfl)

theorem semantic_count (n x y m p : Nat) :
    OMA.S_mo_15242.count n x y m p = count n x y m p := by
  classical
  have hf (h v : List Nat) : decide (connectedTo n h v x y) = forward n h v x y := by
    apply Bool.eq_iff_iff.2
    simp only [decide_eq_true_eq, forward_connected]
  simp only [OMA.S_mo_15242.count, count, choices, hf]

theorem semantic_disproof : ¬ (∀ n x y m p : Nat, x ≤ n → y ≤ n → x < y → p < m →
    OMA.S_mo_15242.count n x y m p ≤ OMA.S_mo_15242.count n x y p m) := by
  simpa only [semantic_count, assertion] using disproof


end GridCounter

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_15242.main) := GridCounter.semantic_disproof
