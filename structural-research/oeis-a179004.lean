import OMAStatements.S_oeis_a179004
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Sum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Tauto
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.Order.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Limiting density in local anti-majority voting

Credit: @LDJAI. Source: https://oeis.org/A179004

For side lengths at least four, stable arrays have at most (2nm+2)/3 ones.
Diagonal stripes with complemented border rows and columns supply at least
2(n-2)(m-2)/3 ones. The bounds are uniform in the aspect ratio.
-/

namespace GridAnti

def pay (a b : Bool) : ℤ := if a = b then -1 else 1
def Directional (n m : ℕ) (col : ℤ → ℤ → Bool) : Prop :=
  ∀ (i j : ℤ), 0 ≤ i → i < n → 0 ≤ j → j < m →
  0 ≤ (if 0 < i then pay (col i j) (col (i-1) j) else 0) +
      (if i+1 < n then pay (col i j) (col (i+1) j) else 0) +
      (if 0 < j then pay (col i j) (col i (j-1)) else 0) +
      (if j+1 < m then pay (col i j) (col i (j+1)) else 0)

def prevF {n} (i : Fin n) : Fin n := ⟨i.val - 1, by omega⟩
def nextF {n} (i : Fin n) : Fin n := ⟨min (i.val+1) (n-1), by omega⟩

/-- The four neighbors that actually exist, in compass order. -/
def around {n m} (v : Cell n m) : List (Cell n m) :=
  (if 0<v.1.val then [(prevF v.1, v.2)] else []) ++
  (if v.1.val+1<n then [(nextF v.1, v.2)] else []) ++
  (if 0<v.2.val then [(v.1, prevF v.2)] else []) ++
  (if v.2.val+1<m then [(v.1, nextF v.2)] else [])

theorem around_spec {n m} (v w : Cell n m) : w ∈ around v ↔ Adj v w := by
  obtain ⟨i,j⟩ := v
  obtain ⟨k,l⟩ := w
  unfold around Adj
  split_ifs <;> simp_all [Prod.mk.injEq, Fin.ext_iff, prevF, nextF] <;> omega

theorem around_unique {n m} (v : Cell n m) : (around v).Nodup := by
  obtain ⟨i,j⟩ := v
  unfold around
  split_ifs <;> simp_all [Prod.mk.injEq, Fin.ext_iff, prevF, nextF] <;> omega

theorem around_finset {n m} (v : Cell n m) : (around v).toFinset = neighbors v := by
  ext w
  simp [neighbors, around_spec]

theorem degree_formula {n m} (v : Cell n m) : (neighbors v).card =
    (if 0<v.1.val then 1 else 0) + (if v.1.val+1<n then 1 else 0) +
    (if 0<v.2.val then 1 else 0) + (if v.2.val+1<m then 1 else 0) := by
  rw [← around_finset, List.toFinset_card_of_nodup (around_unique v)]
  unfold around
  split_ifs <;> simp

theorem degree_le_four {n m} (v : Cell n m) : (neighbors v).card ≤ 4 := by
  rw [degree_formula]; split_ifs <;> decide

private theorem pay_sum (a : Bool) (l : List Bool) :
    (l.map (pay a)).sum = 2*(l.filter (fun w => decide (w ≠ a))).length - (l.length : ℤ) := by
  induction l with
  | nil => simp
  | cons b l ih => cases a <;> cases b <;> simp_all [pay] <;> omega

theorem happy_of_directional {n m} {col : ℤ → ℤ → Bool} (h : Directional n m col) :
    Happy (fun v : Cell n m => col v.1.val v.2.val) := by
  rintro ⟨i,j⟩
  let v : Cell n m := (i,j)
  let c : Cell n m → Bool := fun w => col w.1.val w.2.val
  change (neighbors v).card ≤ 2 * ((neighbors v).filter (fun w => c w ≠ c v)).card
  rw [← around_finset, List.filter_toFinset]
  rw [List.toFinset_card_of_nodup (around_unique v),
      List.toFinset_card_of_nodup ((around_unique v).filter _)]
  have hs := pay_sum (c v) ((around v).map c)
  simp only [List.length_map] at hs
  have heq : (((around v).map c).filter (fun w => decide (w ≠ c v))).length =
      ((around v).filter (fun w => decide (c w ≠ c v))).length := by
    rw [List.filter_map, List.length_map]; rfl
  rw [heq] at hs
  have hv := h i.val j.val (by positivity) (by exact_mod_cast i.isLt) (by positivity) (by exact_mod_cast j.isLt)
  have hnon : 0 ≤ (List.map (pay (c v)) ((around v).map c)).sum := by
    dsimp only [v,c] at *
    have ai : i.val+1<n → min (i.val+1) (n-1) = i.val+1 := fun hi => min_eq_left (by omega)
    have aj : j.val+1<m → min (j.val+1) (m-1) = j.val+1 := fun hj => min_eq_left (by omega)
    unfold around
    split_ifs <;> simp_all [prevF,nextF, ai, aj, Nat.cast_sub, Nat.cast_add] <;>
      first | assumption | push_cast at *; omega
  omega

def axisPay (n : ℕ) (f : ℤ → Bool) (i : ℤ) : ℤ :=
  (if 0 < i then pay (f i) (f (i-1)) else 0) +
  (if i+1 < (n:ℤ) then pay (f i) (f (i+1)) else 0)

/-- Extend a row by assigning each end the opposite of its inward neighbour. -/
def extend (n : ℕ) (f : ℤ → Bool) (i : ℤ) : Bool :=
  if i = 0 then !(f 1) else if i = (n:ℤ)-1 then !(f ((n:ℤ)-2)) else f i

def stripe (phase i j : ℤ) : Bool := decide ((i+j+phase)%3 ≠ 0)

def witnessColor (n m : ℕ) (p i j : ℤ) : Bool :=
  extend m (fun y => extend n (fun x => stripe p x y) i) j

def NoRun (f : ℤ → Bool) : Prop := ∀ i, f i ≠ f (i-1) ∨ f i ≠ f (i+1)

private theorem noRunX (p j : ℤ) : NoRun (fun i => stripe p i j) := by
  intro i
  simp only [stripe, ne_eq, decide_eq_decide, not_iff]
  omega

private theorem noRunY (p i : ℤ) : NoRun (stripe p i) := by
  intro j
  simp only [stripe, ne_eq, decide_eq_decide, not_iff]
  omega

private theorem noRunNot {f : ℤ → Bool} (h : NoRun f) : NoRun (fun i => !(f i)) := by
  intro i
  simpa using h i

private theorem payNot (a b : Bool) : pay (!a) (!b) = pay a b := by cases a <;> cases b <;> rfl

private theorem axisNot (n : ℕ) (f : ℤ → Bool) (i : ℤ) :
    axisPay n (fun x => !(f x)) i = axisPay n f i := by simp [axisPay, payNot]

/-- Both neighbors of an interior site are available. The extension either
preserves the original pair or replaces one neighbor by a disagreeing one. -/
private theorem extendLine (n : ℕ) (hn : 4 ≤ n) (f : ℤ → Bool) (hf : NoRun f)
    (i : ℤ) (hi : 0 ≤ i) (hin : i < (n:ℤ)) : 0 ≤ axisPay n (extend n f) i := by
  have hmid := hf i
  have hneg (b : Bool) : pay (!b) b = 1 := by cases b <;> rfl
  have hpos (b : Bool) : pay b (!b) = 1 := by cases b <;> rfl
  have hlo (a b : Bool) : -1 ≤ pay a b := by cases a <;> cases b <;> decide
  by_cases hz : i = 0
  · subst i
    simp [axisPay, extend, show (1:ℤ) < n by omega, show (1:ℤ) ≠ (n:ℤ)-1 by omega, hneg]
  by_cases ht : i = (n:ℤ)-1
  · subst i
    have z1 : (n:ℤ)-1 - 1 = (n:ℤ)-2 := by omega
    simp [axisPay, extend, show (1:ℤ)<n by omega, show (n:ℤ)-1≠0 by omega,
      z1, show (n:ℤ)-2≠0 by omega, show (n:ℤ)-2≠n-1 by omega, hneg]
  have hp : 0 < i := by omega
  have hr : i+1 < (n:ℤ) := by omega
  simp only [axisPay, if_pos hp, if_pos hr]
  have hi' : extend n f i = f i := by simp [extend,hz,ht]
  rw [hi']
  by_cases hl : i-1=0
  · have h1 : i=1 := by omega
    have hleft : extend n f (i-1) = !(f i) := by
      rw [hl]
      simp [extend,h1]
    rw [hleft,hpos]
    have := hlo (f i) (extend n f (i+1))
    omega
  by_cases hh : i+1=(n:ℤ)-1
  · have h2 : i=(n:ℤ)-2 := by omega
    have hright : extend n f (i+1) = !(f i) := by
      unfold extend
      rw [if_neg (show i+1≠0 by omega), if_pos hh, h2]
    rw [hright,hpos]
    have := hlo (f i) (extend n f (i-1))
    omega
  simp only [extend, if_neg hl, if_neg (show i-1≠(n:ℤ)-1 by omega),
    if_neg (show i+1≠0 by omega), if_neg hh]
  rcases hmid with h|h
  · simp only [pay, if_neg h]; split <;> decide
  · simp only [pay, if_neg h]; split <;> decide

theorem witness_directional (n m : ℕ) (hn : 4 ≤ n) (hm : 4 ≤ m) (p : ℤ) :
    Directional n m (witnessColor n m p) := by
  intro i j hi hj hJ hM
  have hx : 0 ≤ axisPay n (fun x => witnessColor n m p x j) i := by
    unfold witnessColor
    by_cases h : j=0
    · simp only [extend, if_pos h]
      change 0 ≤ axisPay n (fun x => !(extend n (fun x' => stripe p x' 1) x)) i
      rw [axisNot]; exact extendLine n hn _ (noRunX p 1) i hi hj
    by_cases h' : j=(m:ℤ)-1
    · simp only [extend, if_neg h, if_pos h']
      change 0 ≤ axisPay n (fun x => !(extend n (fun x' => stripe p x' ((m:ℤ)-2)) x)) i
      rw [axisNot]; exact extendLine n hn _ (noRunX p _) i hi hj
    · simp only [extend,if_neg h,if_neg h']
      change 0 ≤ axisPay n (extend n (fun x => stripe p x j)) i
      exact extendLine n hn _ (noRunX p j) i hi hj
  have hrow : NoRun (fun y => extend n (fun x => stripe p x y) i) := by
    by_cases h : i=0
    · simp only [extend, if_pos h]
      exact noRunNot (noRunY p 1)
    by_cases h' : i=(n:ℤ)-1
    · simp only [extend, if_neg h, if_pos h']
      exact noRunNot (noRunY p _)
    · simpa only [extend,if_neg h,if_neg h'] using noRunY p i
  have hy : 0 ≤ axisPay m (witnessColor n m p i) j :=
    extendLine m hm _ hrow j hJ hM
  simp only [axisPay] at hx hy
  omega

private def coreEmbedding (n m : ℕ) : Cell n m ↪ Cell (n+2) (m+2) where
  toFun z := (⟨z.1+1, by have := z.1.isLt; omega⟩, ⟨z.2+1, by have := z.2.isLt; omega⟩)
  inj' := by
    intro a b h
    have h1 := congrArg (fun z : Cell (n+2) (m+2) => z.1.val) h
    have h2 := congrArg (fun z : Cell (n+2) (m+2) => z.2.val) h
    have e1 : a.1.val+1 = b.1.val+1 := h1
    have e2 : a.2.val+1 = b.2.val+1 := h2
    exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))

def restrictedColor (n m : ℕ) (p : ℤ) (v : Cell n m) : Bool :=
  witnessColor n m p v.1.val v.2.val

private def coreColor (n m : ℕ) (p : ℤ) (v : Cell n m) : Bool :=
  stripe p ((v.1.val:ℤ)+1) ((v.2.val:ℤ)+1)

private theorem embedding_color (n m : ℕ) (p : ℤ) (v : Cell n m) :
    restrictedColor (n+2) (m+2) p (coreEmbedding n m v) = coreColor n m p v := by
  have hi := v.1.isLt
  have hj := v.2.isLt
  change witnessColor (n+2) (m+2) p ((v.1.val+1:ℕ):ℤ) ((v.2.val+1:ℕ):ℤ) = _
  simp only [witnessColor, coreColor, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, extend]
  split_ifs <;> first | omega | rfl

private theorem core_le (n m : ℕ) (p : ℤ) :
    ones (coreColor n m p) ≤ ones (restrictedColor (n+2) (m+2) p) := by
  let s := Finset.univ.filter fun v : Cell n m => coreColor n m p v = true
  let t := Finset.univ.filter fun v : Cell (n+2) (m+2) => restrictedColor (n+2) (m+2) p v = true
  have hs : s.map (coreEmbedding n m) ⊆ t := by
    intro v hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hv
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and] at hu
    simpa [t, embedding_color] using hu
  simpa [ones,s,t] using Finset.card_le_card hs

private theorem phaseCount (n m : ℕ) :
    ones (coreColor n m 0) + ones (coreColor n m 1) + ones (coreColor n m 2) = 2*n*m := by
  have h (v : Cell n m) :
      (if coreColor n m 0 v then 1 else 0 : ℕ) +
      (if coreColor n m 1 v then 1 else 0 : ℕ) +
      (if coreColor n m 2 v then 1 else 0 : ℕ) = 2 := by
    simp only [coreColor, stripe, decide_eq_true_eq]
    split_ifs <;> omega
  calc
    _ = ∑ v : Cell n m, ((if coreColor n m 0 v then 1 else 0 : ℕ) +
      (if coreColor n m 1 v then 1 else 0 : ℕ) +
      (if coreColor n m 2 v then 1 else 0 : ℕ)) := by simp [ones, Finset.sum_add_distrib]
    _ = ∑ _v : Cell n m, (2 : ℕ) := Finset.sum_congr rfl fun v _ => h v
    _ = _ := by simp [Cell, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

/-- Some phase occupies at least two thirds of the entire inner rectangle. -/
theorem witness_lower (n m : ℕ) : ∃ p : ℤ,
    2*n*m ≤ 3*ones (restrictedColor (n+2) (m+2) p) := by
  have h := phaseCount n m
  have h0 := core_le n m 0
  have h1 := core_le n m 1
  have h2 := core_le n m 2
  by_cases h' : 2*n*m ≤ 3*ones (restrictedColor (n+2) (m+2) 0)
  · exact ⟨0,h'⟩
  by_cases h'' : 2*n*m ≤ 3*ones (restrictedColor (n+2) (m+2) 1)
  · exact ⟨1,h''⟩
  exact ⟨2,by omega⟩

open Finset
private theorem symAdj {n m} {v w : Cell n m} : Adj v w ↔ Adj w v := by
  unfold Adj; tauto

private def corner {n m} (v : Cell n m) : Prop :=
  (v.1.val=0 ∨ v.1.val+1=n) ∧ (v.2.val=0 ∨ v.2.val+1=m)

private theorem small_corners (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) :
    ((univ : Finset (Cell n m)).filter (fun v => decide (v.1.val=0 ∨ v.1.val+1=n) &&
          decide (v.2.val=0 ∨ v.2.val+1=m))).card ≤ 4 := by
  let a : Fin n := ⟨0, by omega⟩
  let b : Fin n := ⟨n-1, by omega⟩
  let s : Fin m := ⟨0, by omega⟩
  let t : Fin m := ⟨m-1, by omega⟩
  have h := (card_insert_le (a,s) {(a,t),(b,s),(b,t)} )
  have h' := (card_insert_le (a,t) {(b,s),(b,t)} )
  have h'' := (card_insert_le (b,s) {(b,t)} )
  apply le_trans (card_le_card (t := {(a,s),(a,t),(b,s),(b,t)}) ?_)
  · simp only [card_singleton] at *; omega
  intro v hv
  have hmem := (mem_filter.mp hv).2
  rcases v with ⟨i,j⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hmem
  simp only [mem_insert, mem_singleton, Prod.mk.injEq, Fin.ext_iff]
  dsimp [a,b,s,t] at *
  omega

theorem density_upper {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m) (c : Cell n m → Bool)
    (hc : Happy c) : 3 * ones c ≤ 2*(n*m) + 2 := by
  classical
  let O := (univ : Finset (Cell n m)).filter (fun v => c v = true)
  let Z := (univ : Finset (Cell n m)).filter (fun v => c v = false)
  let B := (univ : Finset (Cell n m)).filter (fun v =>
    decide (v.1.val=0 ∨ v.1.val+1=n) && decide (v.2.val=0 ∨ v.2.val+1=m))
  have bd := small_corners n m hn hm
  change B.card ≤ 4 at bd
  have localBound (v : Cell n m) : 2 ≤ opp c v + (if v ∈ B then 1 else 0) := by
    have h := hc v
    rw [degree_formula] at h
    have hi := v.1.isLt
    have hj := v.2.isLt
    simp only [B, mem_filter, mem_univ, true_and, Bool.and_eq_true, decide_eq_true_eq]
    split_ifs at * <;> omega
  have lsum := sum_le_sum (s := O) (fun v _ => localBound v)
  simp only [sum_const, nsmul_eq_mul, Nat.cast_id, sum_add_distrib] at lsum
  have hcorner : (∑ v ∈ O, (if v ∈ B then 1 else 0 : ℕ)) ≤ B.card := by
    rw [sum_boole]; apply card_le_card; intro x hx; exact (mem_filter.mp hx).2
  have inc (v : Cell n m) (hv : v ∈ O) :
      opp c v = ∑ w ∈ Z, (if Adj v w then 1 else 0 : ℕ) := by
    rw [sum_boole]; unfold opp; congr 1; ext w
    have hh : c v = true := (mem_filter.mp hv).2
    simp [neighbors,Z,hh,and_comm]
  have inc' (w : Cell n m) : (∑ v ∈ O, (if Adj v w then 1 else 0 : ℕ)) ≤ 4 := by
    rw [sum_boole]; apply le_trans _ (degree_le_four w)
    apply card_le_card; intro v hv; simpa [neighbors, symAdj] using (mem_filter.mp hv).2
  have supply : (∑ v ∈ O, opp c v) ≤ Z.card * 4 := by
    rw [sum_congr rfl inc, sum_comm]
    simpa using (sum_le_sum (s := Z) (fun w _ => inc' w))
  have total : O.card + Z.card = n*m := by
    have h := card_filter_add_card_filter_not (s := (univ : Finset (Cell n m))) (p := fun v => c v = true)
    simpa [O,Z,Cell] using h
  change 3*O.card ≤ 2*(n*m)+2
  omega

theorem best_upper_of {n m : ℕ}
    (upper : ∀ c : Cell n m → Bool, Happy c → 3 * ones c ≤ 2 * (n*m) + 2) :
    3 * best n m ≤ 2 * (n * m) + 2 := by
  classical
  rw [Nat.mul_comm 3, ← Nat.le_div_iff_mul_le (by decide : 0 < 3)]
  unfold best
  apply Finset.sup_le_iff.mpr
  intro c hc
  apply (Nat.le_div_iff_mul_le (by decide : 0 < 3)).2
  simpa only [Nat.mul_comm (ones c) 3] using upper c (Finset.mem_filter.mp hc).2

theorem ones_le_best {n m : ℕ} (c : Cell n m → Bool) (hc : Happy c) :
    ones c ≤ best n m := by
  classical
  unfold best
  apply Finset.le_sup
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩

/-- A single lower bound on both side lengths works for every aspect ratio. -/
theorem limit_of_bounds (best : ℕ → ℕ → ℕ)
    (best_lower : ∀ {n m : ℕ}, 4 ≤ n → 4 ≤ m → 2 * (n-2) * (m-2) ≤ 3 * best n m)
    (best_upper : ∀ {n m : ℕ}, 2 ≤ n → 2 ≤ m → 3 * best n m ≤ 2 * (n*m) + 2) : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 0 < N ∧
    ∀ n m : ℕ, N ≤ n → N ≤ m →
    |(best n m : ℝ) / ((n : ℝ) * (m : ℝ)) - 2 / 3| < ε := by
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_gt (4 / ε)
  let N := max 4 k
  have N4 : 4 ≤ N := Nat.le_max_left _ _
  have Nk : k ≤ N := Nat.le_max_right _ _
  refine ⟨N, by omega, ?_⟩
  intro n m hn hm
  have hn4 := N4.trans hn
  have hm4 := N4.trans hm
  have hn4' : (4:ℝ) ≤ n := by exact_mod_cast hn4
  have hm4' : (4:ℝ) ≤ m := by exact_mod_cast hm4
  have hn' : (0:ℝ) < n := by linarith
  have hm' : (0:ℝ) < m := by linarith
  have hnm := mul_pos hn' hm'
  have hnε : (4:ℝ) < n * ε :=
    (div_lt_iff₀ hε).1 (hk.trans_le (by exact_mod_cast Nk.trans hn))
  have hmε : (4:ℝ) < m * ε :=
    (div_lt_iff₀ hε).1 (hk.trans_le (by exact_mod_cast Nk.trans hm))
  have hrow := mul_lt_mul_of_pos_left hmε hn'
  have hcol := mul_lt_mul_of_pos_left hnε hm'
  have hlow : (2:ℝ) * (n-2) * (m-2) ≤ 3 * (best n m : ℝ) := by
    have h := best_lower hn4 hm4
    have hn2 : 2 ≤ n := by omega
    have hm2 : 2 ≤ m := by omega
    have hh : (2:ℝ) * ((n-2:ℕ):ℝ) * ((m-2:ℕ):ℝ) ≤ 3 * (best n m:ℝ) := by exact_mod_cast h
    simpa only [Nat.cast_sub hn2, Nat.cast_sub hm2, Nat.cast_ofNat] using hh
  have hupp : 3 * (best n m:ℝ) ≤ 2 * ((n:ℝ) * m) + 2 := by
    exact_mod_cast best_upper (n := n) (m := m) (by omega) (by omega)
  rw [abs_lt, lt_sub_iff_add_lt, sub_lt_iff_lt_add]
  constructor
  · apply (lt_div_iff₀ hnm).2
    nlinarith only [hlow, hrow, hcol, mul_pos hε hnm]
  · apply (div_lt_iff₀ hnm).2
    nlinarith only [hupp, hrow, hn4']

theorem best_upper {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m) :
    3 * best n m ≤ 2 * (n * m) + 2 := best_upper_of (density_upper hn hm)

theorem best_lower {n m : ℕ} (hn : 4 ≤ n) (hm : 4 ≤ m) :
    2 * (n-2) * (m-2) ≤ 3 * best n m := by
  classical
  obtain ⟨p,hp⟩ := witness_lower (n-2) (m-2)
  rw [show n-2+2=n by omega, show m-2+2=m by omega] at hp
  apply hp.trans
  apply Nat.mul_le_mul_left
  exact ones_le_best _ (happy_of_directional (witness_directional n m hn hm p))

/-- A single lower bound on both side lengths works for every aspect ratio. -/
theorem limiting_density : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 0 < N ∧
    ∀ n m : ℕ, N ≤ n → N ≤ m →
    |(best n m : ℝ) / ((n : ℝ) * (m : ℝ)) - 2 / 3| < ε :=
  limit_of_bounds best best_lower best_upper

end GridAnti

theorem OMA.solution : type_of% @OMA.S_oeis_a179004.main :=
  GridAnti.limiting_density
