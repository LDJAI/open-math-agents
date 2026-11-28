import OMAReductions.R_oeis_a072567_R1
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

namespace RectFreeCounting

def rectangleFree {n : ℕ} (A : Matrix (Fin n) (Fin n) Bool) : Prop :=
  ∀ i i' j j', i ≠ i' → j ≠ j' →
    ¬ (A i j = true ∧ A i j' = true ∧ A i' j = true ∧ A i' j' = true)

def numberOfOnes {n : ℕ} (A : Matrix (Fin n) (Fin n) Bool) : ℕ :=
  (Finset.univ.filter fun p : Fin n × Fin n => A p.1 p.2 = true).card

def rowNeighbors {n : ℕ} (A : Matrix (Fin n) (Fin n) Bool) (i : Fin n) :
    Finset (Fin n) := Finset.univ.filter fun j => A i j = true

def rowDegree {n : ℕ} (A : Matrix (Fin n) (Fin n) Bool) (i : Fin n) :
    ℕ := (rowNeighbors A i).card

theorem sum_rowDegree {n : ℕ} (A : Matrix (Fin n) (Fin n) Bool) :
    ∑ i, rowDegree A i = numberOfOnes A := by
  classical
  simp only [rowDegree, rowNeighbors, numberOfOnes, Finset.card_eq_sum_ones,
    Finset.sum_filter, Fintype.sum_prod_type]

/-- Distinct pairs of columns occurring together in different rows must be disjoint. -/
theorem pair_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) Bool) (hA : rectangleFree A) :
    (∑ i, rowDegree A i * (rowDegree A i - 1)) ≤ n * (n - 1) := by
  classical
  have hd : (↑(Finset.univ : Finset (Fin n)) : Set (Fin n)).PairwiseDisjoint
      (fun i => (rowNeighbors A i).offDiag) := by
    intro i _ i' _ hne
    change Disjoint (rowNeighbors A i).offDiag (rowNeighbors A i').offDiag
    rw [Finset.disjoint_left]
    intro p hp hp'
    obtain ⟨h1, h2, h3⟩ := Finset.mem_offDiag.mp hp
    obtain ⟨h4, h5, _⟩ := Finset.mem_offDiag.mp hp'
    simp only [rowNeighbors, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2 h4 h5
    exact hA i i' p.1 p.2 hne h3 ⟨h1,h2,h4,h5⟩
  have hs : Finset.univ.biUnion (fun i => (rowNeighbors A i).offDiag) ⊆
      (Finset.univ : Finset (Fin n)).offDiag := by
    intro p hp
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hp
    exact Finset.offDiag_mono (Finset.subset_univ _) hi
  calc
    (∑ i, rowDegree A i * (rowDegree A i - 1)) =
        ∑ i, ((rowNeighbors A i).offDiag).card := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.offDiag_card]
      unfold rowDegree
      rw [Nat.mul_sub_left_distrib, Nat.mul_one]
    _ = (Finset.univ.biUnion fun i => (rowNeighbors A i).offDiag).card :=
      (Finset.card_biUnion hd).symm
    _ ≤ ((Finset.univ : Finset (Fin n)).offDiag).card := Finset.card_le_card hs
    _ = n * (n - 1) := by simp [Finset.offDiag_card, Nat.mul_sub_left_distrib]

/-- General linearized pair-counting bound, with integral tangent k. -/
theorem tangent_bound {n k : ℕ} (hn : 1 ≤ n)
    (A : Matrix (Fin n) (Fin n) Bool) (hA : rectangleFree A) :
    2*k*numberOfOnes A ≤ n*(n-1)+n*k*(k+1) := by
  classical
  have hc (i : Fin n) :
      (↑(rowDegree A i * (rowDegree A i - 1)) : ℤ) =
        (↑(rowDegree A i) : ℤ) * ((↑(rowDegree A i) : ℤ) - 1) := by
    by_cases h : rowDegree A i = 0
    · simp [h]
    · rw [Nat.cast_mul, Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr h)] <;> simp
  have hi := Int.ofNat_le.mpr (pair_bound A hA)
  rw [Nat.cast_sum, Nat.cast_mul, Nat.cast_sub hn, Nat.cast_one] at hi
  simp_rw [hc] at hi
  have hy (x : ℤ) : 0 ≤ x*(x-1) := by
    by_cases h : 0 < x
    · exact mul_nonneg (by omega) (by omega)
    · exact mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
  have hsum :
      (∑ i : Fin n, (2*(k:ℤ)*(rowDegree A i:ℤ) - (k:ℤ)*((k:ℤ)+1))) ≤
        ∑ i : Fin n, (rowDegree A i:ℤ)*((rowDegree A i:ℤ)-1) := by
    apply Finset.sum_le_sum
    intro i _
    nlinarith [hy ((rowDegree A i:ℤ) - (k:ℤ))]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← Nat.cast_sum, sum_rowDegree] at hsum
  have hInt : 2*(k:ℤ)*(numberOfOnes A:ℤ) ≤
      (n:ℤ)*((n:ℤ)-1)+(n:ℤ)*(k:ℤ)*((k:ℤ)+1) := by
    linarith [hsum.trans hi]
  have hNat : ((2*k*numberOfOnes A:ℕ):ℤ) ≤
      ((n*(n-1)+n*k*(k+1):ℕ):ℤ) := by
    simpa [Nat.cast_mul, Nat.cast_add, Nat.cast_sub hn] using hInt
  exact Int.ofNat_le.mp hNat

/-- At projective-plane parameter sizes, every rectangle-free board has at
most n(q+1) ones. -/
theorem projective_order_bound {n q : ℕ} (hsize : n = q*q+q+1)
    (A : Matrix (Fin n) (Fin n) Bool) (hA : rectangleFree A) :
    numberOfOnes A ≤ n * (q + 1) := by
  have hn : 1 ≤ n := by omega
  have h := tangent_bound (k := q+1) hn A hA
  have hsize' : n-1 = q*q+q := by omega
  have heq : n*(n-1)+n*(q+1)*(q+1+1) = 2*(q+1)*(n*(q+1)) := by
    rw [hsize']
    ring
  rw [heq] at h
  exact Nat.le_of_mul_le_mul_left h (by omega)

/-- A symmetric rectangle-free regular board at projective-plane order
is extremal among all rectangle-free square boards. -/
theorem symmetric_regular_optimal {n q : ℕ} (hsize : n = q*q+q+1)
    (B : Matrix (Fin n) (Fin n) Bool)
    (hB : B.IsSymm) (hfree : rectangleFree B)
    (hreg : ∀ i, rowDegree B i = q+1) :
    ∃ B : Matrix (Fin n) (Fin n) Bool, B.IsSymm ∧ rectangleFree B ∧
      ∀ A : Matrix (Fin n) (Fin n) Bool, rectangleFree A →
        numberOfOnes A ≤ numberOfOnes B := by
  refine ⟨B,hB,hfree,?_⟩
  intro A hA
  have hw : numberOfOnes B = n*(q+1) := by
    rw [← sum_rowDegree]
    simp [hreg, Finset.sum_const]
  rw [hw]
  exact projective_order_bound hsize A hA


end RectFreeCounting

namespace RectFreeCounting

def rectangleFreeRect {m n : ℕ} (A : Matrix (Fin m) (Fin n) Bool) : Prop :=
  ∀ i i' j j', i ≠ i' → j ≠ j' →
    ¬ (A i j = true ∧ A i j' = true ∧ A i' j = true ∧ A i' j' = true)

def rowDegRect {m n : ℕ} (A : Matrix (Fin m) (Fin n) Bool) (i : Fin m) :
    ℕ := (Finset.univ.filter fun j => A i j = true).card

def colNeighbors {m n : ℕ} (A : Matrix (Fin m) (Fin n) Bool) (s : Finset (Fin m))
    (j : Fin n) : Finset (Fin m) := s.filter fun i => A i j = true

def colDegree {m n : ℕ} (A : Matrix (Fin m) (Fin n) Bool) (s : Finset (Fin m))
    (j : Fin n) : ℕ := (colNeighbors A s j).card

theorem sum_colDegree {m n : ℕ} (A : Matrix (Fin m) (Fin n) Bool) (s : Finset (Fin m)) :
    (∑ j, colDegree A s j) = ∑ i ∈ s, rowDegRect A i := by
  classical
  simp only [rowDegRect, colDegree, colNeighbors, Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Finset.sum_comm

theorem selected_pair_bound {m n : ℕ} (A : Matrix (Fin m) (Fin n) Bool)
    (hA : rectangleFreeRect A) (s : Finset (Fin m)) :
    (∑ j, colDegree A s j * (colDegree A s j - 1)) ≤ s.card * (s.card - 1) := by
  classical
  have hd : (↑(Finset.univ : Finset (Fin n)) : Set (Fin n)).PairwiseDisjoint
      (fun j => (colNeighbors A s j).offDiag) := by
    intro j _ j' _ hne
    change Disjoint (colNeighbors A s j).offDiag (colNeighbors A s j').offDiag
    rw [Finset.disjoint_left]
    intro p hp hp'
    obtain ⟨h1, h2, h3⟩ := Finset.mem_offDiag.mp hp
    obtain ⟨h4, h5, _⟩ := Finset.mem_offDiag.mp hp'
    simp only [colNeighbors, Finset.mem_filter] at h1 h2 h4 h5
    exact hA p.1 p.2 j j' h3 hne ⟨h1.2,h4.2,h2.2,h5.2⟩
  have hs : Finset.univ.biUnion (fun j => (colNeighbors A s j).offDiag) ⊆
      s.offDiag := by
    intro p hp
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hp
    exact Finset.offDiag_mono (Finset.filter_subset _ _) hj
  calc
    (∑ j, colDegree A s j * (colDegree A s j - 1)) =
        ∑ j, ((colNeighbors A s j).offDiag).card := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.offDiag_card]
      unfold colDegree
      rw [Nat.mul_sub_left_distrib, Nat.mul_one]
    _ = (Finset.univ.biUnion fun j => (colNeighbors A s j).offDiag).card :=
      (Finset.card_biUnion hd).symm
    _ ≤ s.offDiag.card := Finset.card_le_card hs
    _ = s.card * (s.card - 1) := by simp [Finset.offDiag_card, Nat.mul_sub_left_distrib]

/-- General tangent bound for arbitrary selected rows of any rectangular matrix. -/
theorem selected_tangent_bound {m n k : ℕ}
    (A : Matrix (Fin m) (Fin n) Bool) (hA : rectangleFreeRect A)
    (s : Finset (Fin m)) (hpos : 1 ≤ s.card) :
    2*k*(∑ i ∈ s, rowDegRect A i) ≤ s.card*(s.card-1)+n*k*(k+1) := by
  classical
  have hc (j : Fin n) :
      (↑(colDegree A s j * (colDegree A s j - 1)) : ℤ) =
        (↑(colDegree A s j) : ℤ) * ((↑(colDegree A s j) : ℤ) - 1) := by
    by_cases h : colDegree A s j = 0
    · simp [h]
    · rw [Nat.cast_mul, Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr h)]
      simp
  have hi := Int.ofNat_le.mpr (selected_pair_bound A hA s)
  rw [Nat.cast_sum, Nat.cast_mul, Nat.cast_sub hpos, Nat.cast_one] at hi
  simp_rw [hc] at hi
  have hy (x : ℤ) : 0 ≤ x*(x-1) := by
    by_cases h : 0 < x
    · exact mul_nonneg (by omega) (by omega)
    · exact mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
  have hsum :
      (∑ j : Fin n, (2*(k:ℤ)*(colDegree A s j:ℤ) - (k:ℤ)*((k:ℤ)+1))) ≤
        ∑ j : Fin n, (colDegree A s j:ℤ)*((colDegree A s j:ℤ)-1) := by
    apply Finset.sum_le_sum
    intro j _
    nlinarith [hy ((colDegree A s j:ℤ) - (k:ℤ))]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← Nat.cast_sum, sum_colDegree] at hsum
  have hInt : 2*(k:ℤ)*(↑(∑ i ∈ s, rowDegRect A i):ℤ) ≤
      (s.card:ℤ)*((s.card:ℤ)-1)+(n:ℤ)*(k:ℤ)*((k:ℤ)+1) := by
    linarith [hsum.trans hi]
  have hNat : ((2*k*(∑ i ∈ s, rowDegRect A i):ℕ):ℤ) ≤
      ((s.card*(s.card-1)+n*k*(k+1):ℕ):ℤ) := by
    simpa [Nat.cast_mul, Nat.cast_add, Nat.cast_sub hpos] using hInt
  exact Int.ofNat_le.mp hNat

/-- If the tangent bound contradicts every selected row having at least k+1 ones,
then some selected row has at most k ones. -/
theorem exists_degree_le_of_tangent {m n k : ℕ}
    (A : Matrix (Fin m) (Fin n) Bool) (hA : rectangleFreeRect A)
    (s : Finset (Fin m)) (hpos : 1 ≤ s.card)
    (hlt : s.card*(s.card-1)+n*k*(k+1) < 2*k*(s.card*(k+1))) :
    ∃ i ∈ s, rowDegRect A i ≤ k := by
  by_contra! h
  have hsum : s.card*(k+1) ≤ ∑ i ∈ s, rowDegRect A i := by
    calc
      _ = ∑ i ∈ s, (k+1) := by simp
      _ ≤ _ := Finset.sum_le_sum fun i hi => by have := h i hi; omega
  have hmul := Nat.mul_le_mul_left (2*k) hsum
  exact (not_lt_of_ge (hmul.trans (selected_tangent_bound (k:=k) A hA s hpos))) hlt

/-- Sharp unrestricted upper bound one below a projective-plane order.
This only uses rectangle-freeness, not symmetry or existence of a plane. -/
theorem projective_minus_one_bound {n q : ℕ} (hq : 0 < q) (hsize : n=q*q+q)
    (A : Matrix (Fin n) (Fin n) Bool) (hA : rectangleFree A) :
    numberOfOnes A ≤ q*q*q + 2*q*q := by
  classical
  let high : Finset (Fin n) := Finset.univ.filter fun i => q < rowDegRect A i
  have hA' : rectangleFreeRect A := hA
  have hx : q*q+1-1=q*q := by omega
  have hH : high.card ≤ q*q := by
    by_contra! hh
    obtain ⟨s, hsub, hs⟩ :=
      Finset.exists_subset_card_eq (s:=high) (n:=q*q+1) (by omega)
    have hlt : s.card*(s.card-1)+n*q*(q+1) < 2*q*(s.card*(q+1)) := by
      rw [hs, hsize, hx]
      have heq : 2*q*((q*q+1)*(q+1)) =
        (q*q+1)*(q*q)+(q*q+q)*q*(q+1)+2*q := by ring
      rw [heq]
      omega
    obtain ⟨i, hi, hle⟩ := exists_degree_le_of_tangent A hA' s (by omega) hlt
    have hgt : q < rowDegRect A i := (Finset.mem_filter.mp (hsub hi)).2
    omega
  obtain ⟨s, hhs, hsU, hs⟩ :=
    Finset.exists_subsuperset_card_eq (t:=Finset.univ) (n:=q*q+1)
      (Finset.subset_univ high) (by omega) (by simp only [Finset.card_univ, Fintype.card_fin, hsize]; omega)
  have hSel : (∑ i ∈ s, rowDegRect A i) ≤ q*(q*q+q+1) := by
    have ht := selected_tangent_bound (k:=q) A hA' s (by omega)
    rw [hs, hx] at ht
    have heq : (q*q+1)*(q*q)+n*q*(q+1) = 2*q*(q*(q*q+q+1)) := by rw [hsize]; ring
    rw [heq] at ht
    exact Nat.le_of_mul_le_mul_left ht (by omega)
  have hRestCard : ((Finset.univ : Finset (Fin n)) \ s).card = q-1 := by
    rw [Finset.card_sdiff_of_subset hsU, Finset.card_univ, Fintype.card_fin, hs, hsize]
    omega
  have hRest : (∑ i ∈ (Finset.univ : Finset (Fin n)) \ s, rowDegRect A i) ≤ (q-1)*q := by
    calc
      _ ≤ ∑ _i ∈ (Finset.univ : Finset (Fin n)) \ s, q := by
        apply Finset.sum_le_sum
        intro i hi
        by_contra! hg
        have him : i ∈ high := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg⟩
        exact (Finset.mem_sdiff.mp hi).2 (hhs him)
      _ = _ := by simp [hRestCard]
  have hTotal : (∑ i ∈ (Finset.univ : Finset (Fin n)) \ s, rowDegRect A i) +
      (∑ i ∈ s, rowDegRect A i) = numberOfOnes A := by
    rw [← sum_rowDegree]
    exact Finset.sum_sdiff (f:=rowDegRect A) hsU
  have ht := Nat.add_le_add hRest hSel
  rw [hTotal] at ht
  have hEq : (q-1)*q+q*(q*q+q+1) = q*q*q+2*q*q := by
    calc
      _ = q*((q-1)+(q*q+q+1)) := by ring
      _ = q*(q*q+2*q) := by congr 1; omega
      _ = _ := by ring
  rwa [hEq] at ht



end RectFreeCounting

namespace RectFreeCounting

def rowIndicator {n : ℕ} (B : Matrix (Fin n) (Fin n) Bool) (i j : Fin n) : ℕ :=
  if B i j = true then 1 else 0

theorem rowDegree_eq_indicator {n : ℕ} (B : Matrix (Fin n) (Fin n) Bool) (i : Fin n) :
    rowDegree B i = ∑ j, rowIndicator B i j := by
  simp only [rowDegree, rowNeighbors, Finset.card_eq_sum_ones, Finset.sum_filter, rowIndicator]

def deleteZero {n : ℕ} (B : Matrix (Fin (n+1)) (Fin (n+1)) Bool) :
    Matrix (Fin n) (Fin n) Bool := fun i j => B i.succ j.succ

theorem deleteZero_free {n : ℕ} (B : Matrix (Fin (n+1)) (Fin (n+1)) Bool)
    (hB : rectangleFree B) : rectangleFree (deleteZero B) := by
  intro i i' j j' hi hj h
  exact hB i.succ i'.succ j.succ j'.succ (fun e => hi (Fin.succ_inj.mp e))
    (fun e => hj (Fin.succ_inj.mp e)) h

theorem deleteZero_symm {n : ℕ} (B : Matrix (Fin (n+1)) (Fin (n+1)) Bool)
    (hB : B.IsSymm) : (deleteZero B).IsSymm := by
  exact Matrix.IsSymm.ext_iff.mpr fun i j => Matrix.IsSymm.ext_iff.mp hB i.succ j.succ

theorem deleteZero_count {n : ℕ} (B : Matrix (Fin (n+1)) (Fin (n+1)) Bool)
    (hB : B.IsSymm) (hloop : B 0 0 = true) :
    numberOfOnes (deleteZero B) + 2 * rowDegree B 0 = numberOfOnes B + 1 := by
  have hrow (i : Fin n) : rowDegree B i.succ =
      rowIndicator B i.succ 0 + rowDegree (deleteZero B) i := by
    rw [rowDegree_eq_indicator, Fin.sum_univ_succ, rowDegree_eq_indicator]
    rfl
  have hzero : rowDegree B 0 = 1 + ∑ i : Fin n, rowIndicator B 0 i.succ := by
    rw [rowDegree_eq_indicator, Fin.sum_univ_succ]
    simp [rowIndicator, hloop]
  have hsym (i : Fin n) : rowIndicator B i.succ 0 = rowIndicator B 0 i.succ := by
    unfold rowIndicator
    rw [Matrix.IsSymm.ext_iff.mp hB 0 i.succ]
  have hsum := sum_rowDegree B
  rw [Fin.sum_univ_succ] at hsum
  simp_rw [hrow, hsym] at hsum
  rw [Finset.sum_add_distrib, sum_rowDegree] at hsum
  omega

/-- A symmetric regular projective-plane-order board with one diagonal 1
yields an extremal symmetric board one order smaller by deleting that row and column. -/
theorem deleteZero_optimal {n q : ℕ} (hq : 0<q) (hsize : n = q*q+q)
    (B : Matrix (Fin (n+1)) (Fin (n+1)) Bool)
    (hB : B.IsSymm) (hf : rectangleFree B)
    (hreg : ∀ i, rowDegree B i = q+1) (hloop : B 0 0 = true) :
    ∃ C : Matrix (Fin n) (Fin n) Bool, C.IsSymm ∧ rectangleFree C ∧
      ∀ A : Matrix (Fin n) (Fin n) Bool, rectangleFree A →
        numberOfOnes A ≤ numberOfOnes C := by
  refine ⟨deleteZero B, deleteZero_symm B hB, deleteZero_free B hf, ?_⟩
  intro A hA
  have hw : numberOfOnes B = (n+1)*(q+1) := by
    rw [← sum_rowDegree]
    simp [hreg]
  have hcount := deleteZero_count B hB hloop
  rw [hw, hreg] at hcount
  have hEq : (n+1)*(q+1)+1 = (q*q*q+2*q*q)+2*(q+1) := by rw [hsize]; ring
  rw [hEq] at hcount
  have hCard : numberOfOnes (deleteZero B) = q*q*q+2*q*q := by omega
  rw [hCard]
  exact projective_minus_one_bound hq hsize A hA

/-- It suffices that *some* diagonal cell of the regular symmetric board
equals one: simultaneously relabel rows and columns before deletion. -/
theorem deleteLoop_optimal {n q : ℕ} (hq : 0<q) (hsize : n = q*q+q)
    (B : Matrix (Fin (n+1)) (Fin (n+1)) Bool)
    (hB : B.IsSymm) (hf : rectangleFree B)
    (hreg : ∀ i, rowDegree B i = q+1) (hloop : ∃ i, B i i = true) :
    ∃ C : Matrix (Fin n) (Fin n) Bool, C.IsSymm ∧ rectangleFree C ∧
      ∀ A : Matrix (Fin n) (Fin n) Bool, rectangleFree A →
        numberOfOnes A ≤ numberOfOnes C := by
  obtain ⟨i, hi⟩ := hloop
  let e : Fin (n+1) ≃ Fin (n+1) := Equiv.swap 0 i
  let B' : Matrix (Fin (n+1)) (Fin (n+1)) Bool := fun j k => B (e j) (e k)
  apply deleteZero_optimal hq hsize B'
  · exact Matrix.IsSymm.ext_iff.mpr fun j k => Matrix.IsSymm.ext_iff.mp hB (e j) (e k)
  · intro j j' k k' hj hk
    exact hf (e j) (e j') (e k) (e k') (fun h => hj (e.injective h))
      (fun h => hk (e.injective h))
  · intro j
    rw [rowDegree_eq_indicator]
    suffices (∑ k, rowIndicator B' j k) = rowDegree B (e j) by rw [this, hreg]
    rw [rowDegree_eq_indicator]
    change (∑ k, rowIndicator B (e j) (e k)) = _
    exact Equiv.sum_comp e (fun k => rowIndicator B (e j) k)
  · change B (e 0) (e 0) = true
    simp [e, hi]



end RectFreeCounting

namespace RectangleResearch

open RectFreeCounting
open Finset

def w {n : ℕ} (A : Matrix (Fin n) (Fin n) Bool) (i j : Fin n) : ℤ :=
  if A i j = true then 1 else 0

def d {n : ℕ} (A : Matrix (Fin n) (Fin n) Bool) (i : Fin n) : ℤ :=
  (rowDegree A i : ℤ)

def a {n : ℕ} (A : Matrix (Fin n) (Fin n) Bool) (H : Finset (Fin n)) (j : Fin n) : ℤ :=
  (colDegree A H j : ℤ)

def c {n : ℕ} (A : Matrix (Fin n) (Fin n) Bool) (j : Fin n) : ℤ :=
  a A univ j

def E {n : ℕ} (A : Matrix (Fin n) (Fin n) Bool) : ℤ :=
  (numberOfOnes A : ℤ)

theorem d_sum {n : ℕ} (A : Matrix (Fin n) (Fin n) Bool) (i : Fin n) :
    d A i = ∑ j, w A i j := by
  unfold d
  rw [rowDegree_eq_indicator, Nat.cast_sum]
  apply sum_congr rfl
  intro j _
  by_cases h : A i j = true <;> simp [rowIndicator, w, h]

theorem a_sum {n : ℕ} (A : Matrix (Fin n) (Fin n) Bool) (H : Finset (Fin n)) (j : Fin n) :
    a A H j = ∑ i ∈ H, w A i j := by
  unfold a colDegree colNeighbors
  rw [card_eq_sum_ones, Nat.cast_sum, sum_filter]
  apply sum_congr rfl
  intro i _
  by_cases h : A i j = true <;> simp [w, h]

theorem c_sum {n : ℕ} (A : Matrix (Fin n) (Fin n) Bool) (j : Fin n) :
    c A j = ∑ i, w A i j := a_sum A univ j

theorem E_rows {n : ℕ} (A : Matrix (Fin n) (Fin n) Bool) :
    ∑ i, d A i = E A := by
  unfold d E
  rw [← Nat.cast_sum, sum_rowDegree]

theorem E_cols {n : ℕ} (A : Matrix (Fin n) (Fin n) Bool) :
    ∑ j, c A j = E A := by
  rw [← E_rows]
  simp_rw [c_sum, d_sum]
  exact sum_comm

theorem selected_sum {n : ℕ} (A : Matrix (Fin n) (Fin n) Bool) (H : Finset (Fin n)) :
    ∑ j, a A H j = ∑ i ∈ H, d A i := by
  simp_rw [a_sum,d_sum]
  exact sum_comm

theorem transpose_free {n : ℕ} (A : Matrix (Fin n) (Fin n) Bool) (hA : rectangleFree A) :
    rectangleFree A.transpose := by
  intro i i' j j' hi hj hr
  exact hA j j' i i' hj hi ⟨hr.1, hr.2.2.1, hr.2.1, hr.2.2.2⟩

theorem transpose_d {n : ℕ} (A : Matrix (Fin n) (Fin n) Bool) (i : Fin n) :
    d A.transpose i = c A i := by
  rw [d_sum, c_sum]
  rfl

theorem transpose_c {n : ℕ} (A : Matrix (Fin n) (Fin n) Bool) (i : Fin n) :
    c A.transpose i = d A i := by
  rw [c_sum, d_sum]
  rfl

theorem transpose_E {n : ℕ} (A : Matrix (Fin n) (Fin n) Bool) :
    E A.transpose = E A := by
  rw [← E_rows A.transpose, ← E_cols A]
  simp_rw [transpose_d]

theorem a_nonneg {n : ℕ} (A : Matrix (Fin n) (Fin n) Bool) (H : Finset (Fin n)) (j : Fin n) :
    0 ≤ a A H j := Int.natCast_nonneg _

theorem c_nonneg {n : ℕ} (A : Matrix (Fin n) (Fin n) Bool) (j : Fin n) :
    0 ≤ c A j := a_nonneg A _ _

theorem d_nonneg {n : ℕ} (A : Matrix (Fin n) (Fin n) Bool) (i : Fin n) :
    0 ≤ d A i := Int.natCast_nonneg _

theorem int_pair_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) Bool)
    (hA : rectangleFree A) (H : Finset (Fin n)) :
    ∑ j, a A H j * (a A H j - 1) ≤ (H.card : ℤ) * ((H.card : ℤ) - 1) := by
  have hposcast (k : ℕ) : ((k*(k-1) : ℕ):ℤ) = (k:ℤ)*((k:ℤ)-1) := by
    by_cases hk : k = 0
    · simp [hk]
    · rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
  have hb := Int.ofNat_le.mpr (selected_pair_bound A hA H)
  rw [Nat.cast_sum, hposcast] at hb
  simp_rw [hposcast] at hb
  exact hb

theorem localNat {n : ℕ} (A : Matrix (Fin n) (Fin n) Bool) (hA : rectangleFree A)
    (i : Fin n) :
    ∑ j ∈ rowNeighbors A i, (colDegree A univ j - 1) ≤ n - 1 := by
  classical
  let S := rowNeighbors A i
  let T (j : Fin n) := (colNeighbors A univ j).erase i
  have hd : (↑S : Set (Fin n)).PairwiseDisjoint T := by
    intro j hj j' hj' hne
    change Disjoint (T j) (T j')
    rw [disjoint_left]
    intro k hk hk'
    have hjA : A i j = true := (mem_filter.mp hj).2
    have hj'A : A i j' = true := (mem_filter.mp hj').2
    have hkA : A k j = true := (mem_filter.mp (mem_erase.mp hk).2).2
    have hk'A : A k j' = true := (mem_filter.mp (mem_erase.mp hk').2).2
    exact hA i k j j' (Ne.symm (mem_erase.mp hk).1) hne ⟨hjA,hj'A,hkA,hk'A⟩
  have hsub : S.biUnion T ⊆ (univ : Finset (Fin n)).erase i := by
    intro k hk
    obtain ⟨j,_,hm⟩ := mem_biUnion.mp hk
    exact mem_erase.mpr ⟨(mem_erase.mp hm).1, mem_univ _⟩
  have hcard (j : Fin n) (hj : j ∈ S) : (T j).card = colDegree A univ j - 1 := by
    apply card_erase_of_mem
    exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hj).2⟩
  calc
    ∑ j ∈ rowNeighbors A i, (colDegree A univ j - 1) = ∑ j ∈ S, (T j).card := by
      apply sum_congr rfl
      intro j hj
      exact (hcard j hj).symm
    _ = (S.biUnion T).card := (card_biUnion hd).symm
    _ ≤ ((univ : Finset (Fin n)).erase i).card := card_le_card hsub
    _ = n-1 := by rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]

theorem local_int {n : ℕ} (A : Matrix (Fin n) (Fin n) Bool) (hA : rectangleFree A)
    (i : Fin n) :
    ∑ j, w A i j * (c A j - 1) ≤ (n : ℤ) - 1 := by
  classical
  have hn : 1 ≤ n := by have := i.isLt; omega
  have hb := Int.ofNat_le.mpr (localNat A hA i)
  rw [Nat.cast_sum, Nat.cast_sub hn, Nat.cast_one] at hb
  have hc (j : Fin n) (hj : j ∈ rowNeighbors A i) :
      ((colDegree A univ j - 1 : ℕ):ℤ) = c A j - 1 := by
    have hmem : i ∈ colNeighbors A univ j := mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hj).2⟩
    have hp : 1 ≤ colDegree A univ j := card_pos.mpr ⟨i,hmem⟩
    rw [Nat.cast_sub hp, Nat.cast_one]
    rfl
  rw [show (∑ j ∈ rowNeighbors A i, ((colDegree A univ j - 1 : ℕ):ℤ)) =
      ∑ j ∈ rowNeighbors A i, (c A j - 1) from sum_congr rfl hc] at hb
  unfold rowNeighbors at hb
  rw [sum_filter] at hb
  convert hb using 1
  apply sum_congr rfl
  intro j _
  by_cases h : A i j = true <;> simp [w,h]

theorem weighted_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) Bool)
    (hA : rectangleFree A) (H : Finset (Fin n)) (q : ℤ) :
    q * (∑ i ∈ H, d A i) - (H.card : ℤ)*((n:ℤ)-1) ≤
      ∑ j, a A H j * (q+1-c A j) := by
  have hsum : ∑ i ∈ H, ∑ j, w A i j * (c A j - 1) ≤
      ∑ _i ∈ H, ((n:ℤ)-1) := sum_le_sum fun i _ => local_int A hA i
  rw [sum_const, nsmul_eq_mul, sum_comm (s := H)] at hsum
  simp_rw [← sum_mul, ← a_sum] at hsum
  have hid : (∑ j, a A H j * (q+1-c A j)) =
      q*(∑ i ∈ H, d A i) - ∑ j, a A H j*(c A j-1) := by
    rw [← selected_sum A H, mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro j _
    ring
  rw [hid]
  linarith

theorem top_set {α : Type*} [Fintype α] (f : α → ℤ) (m : ℕ)
    (hm : m ≤ Fintype.card α) :
    ∃ H : Finset α, H.card = m ∧ ∀ i ∈ H, ∀ j ∉ H, f j ≤ f i := by
  classical
  obtain ⟨U, hsub, hcard⟩ := exists_subset_card_eq (s := (univ : Finset α))
    (by simpa using hm)
  have hne : ((univ : Finset α).powersetCard m).Nonempty :=
    ⟨U, mem_powersetCard.mpr ⟨hsub,hcard⟩⟩
  obtain ⟨H, hH, hmax⟩ := exists_max_image _ (fun S => ∑ i ∈ S, f i) hne
  have hc := (mem_powersetCard.mp hH).2
  refine ⟨H,hc,?_⟩
  intro i hi j hj
  let H' := insert j (H.erase i)
  have hnot : j ∉ H.erase i := fun h => hj (mem_of_mem_erase h)
  have hc' : H'.card = m := by
    rw [show H' = insert j (H.erase i) from rfl, card_insert_of_notMem hnot,
      card_erase_of_mem hi, hc]
    have := card_pos.mpr ⟨i,hi⟩
    omega
  have hb := hmax H' (mem_powersetCard.mpr ⟨subset_univ _, hc'⟩)
  change (∑ k ∈ insert j (H.erase i), f k) ≤ ∑ k ∈ H, f k at hb
  rw [sum_insert hnot] at hb
  have he := sum_erase_add H f hi
  omega

theorem int_mul_pred_nonneg (z : ℤ) : 0 ≤ z*(z-1) := by
  by_cases h : 0 < z
  · exact mul_nonneg (by omega) (by omega)
  · exact mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)

theorem twice_pos_excess (z : ℤ) : 2 * max (z-1) 0 ≤ z*(z-1) := by
  by_cases hz : z ≤ 1
  · rw [max_eq_right (by omega)]
    simpa using int_mul_pred_nonneg z
  · rw [max_eq_left (by omega)]
    have h := mul_nonneg (show 0 ≤ z-2 by omega) (show 0 ≤ z-1 by omega)
    linarith [show (z-2)*(z-1) = z*(z-1)-2*(z-1) by ring]

theorem deviation_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) Bool)
    (hA : rectangleFree A) (H : Finset (Fin n)) (r : ℤ) :
    2*r*(∑ i ∈ H, d A i) - (n:ℤ)*r*(r+1) +
      ∑ j, (a A H j-r)*(a A H j-r-1) ≤ (H.card:ℤ)*((H.card:ℤ)-1) := by
  have he : (∑ j, a A H j*(a A H j-1)) =
      2*r*(∑ i ∈ H, d A i) - (n:ℤ)*r*(r+1) +
      ∑ j, (a A H j-r)*(a A H j-r-1) := by
    rw [← selected_sum A H, mul_sum]
    have hconst : (n:ℤ)*r*(r+1) =
        ∑ _j : Fin n, r*(r+1) := by simp [nsmul_eq_mul]; ring
    rw [hconst, ← sum_sub_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro j _
    ring
  rw [← he]
  exact int_pair_bound A hA H

theorem sum_max_excess {α : Type*} [Fintype α] (z : α → ℤ) (U : ℤ)
    (hz : ∑ j, z j*(z j-1) ≤ U) :
    2*(∑ j, max (z j-1) 0) ≤ U := by
  have h : (∑ j, 2*max (z j-1) 0) ≤ ∑ j, z j*(z j-1) :=
    sum_le_sum fun j _ => twice_pos_excess (z j)
  rw [← mul_sum] at h
  exact h.trans hz


end RectangleResearch

namespace RectangleResearch
open RectFreeCounting Finset

theorem compl_card {α : Type*} [Fintype α] [DecidableEq α] (H : Finset α) :
    (((univ : Finset α) \ H).card : ℤ) = (Fintype.card α : ℤ) - (H.card : ℤ) := by
  rw [card_sdiff_of_subset (subset_univ _), card_univ,
    Nat.cast_sub (card_le_univ _)]

theorem compl_card_fin {n : ℕ} (H : Finset (Fin n)) :
    (((univ : Finset (Fin n)) \ H).card : ℤ) = (n : ℤ) - H.card := by
  simpa using compl_card H

theorem top_weight_lower {n m : ℕ} {q : ℤ}
    (A : Matrix (Fin n) (Fin n) Bool)
    (H : Finset (Fin n)) (hc : H.card = m)
    (htop : ∀ i ∈ H, ∀ j ∉ H, d A j ≤ d A i)
    (hE : q*(n:ℤ)+(m:ℤ) ≤ E A) :
    (q+1)*(m:ℤ) ≤ ∑ i ∈ H, d A i := by
  classical
  by_cases h : ∀ i ∈ H, q+1 ≤ d A i
  · calc
      (q+1)*(m:ℤ) = ∑ _i ∈ H, (q+1) := by rw [sum_const,nsmul_eq_mul,hc]; ring
      _ ≤ _ := sum_le_sum h
  · push_neg at h
    obtain ⟨i,hi,hdeg⟩ := h
    have hg : ∀ j ∈ univ \ H, d A j ≤ q := by
      intro j hj
      have := htop i hi j (mem_sdiff.mp hj).2
      omega
    have hw : ∑ j ∈ univ \ H, d A j ≤ q*((n:ℤ)-(m:ℤ)) := by
      calc
        _ ≤ ∑ _j ∈ univ \ H, q := sum_le_sum hg
        _ = _ := by rw [sum_const,nsmul_eq_mul,compl_card_fin,hc]; ring
    have he := sum_sdiff (subset_univ H) (f := d A)
    rw [E_rows] at he
    linarith

theorem top_slack_four {n m : ℕ} {q : ℤ}
    (hn : (n:ℤ)=q*q+q-3) (hm : (m:ℤ)=q*q-3*q+3)
    (A : Matrix (Fin n) (Fin n) Bool) (hA : rectangleFree A)
    (H : Finset (Fin n)) (hc : H.card=m) :
    2*(q-3)*((∑ i ∈ H,d A i)-(q+1)*(m:ℤ)) +
      ∑ j, (a A H j-(q-3))*(a A H j-(q-3)-1) ≤ 6 := by
  have hb := deviation_bound A hA H (q-3)
  rw [hc] at hb
  have he : 2*(q-3)*((q+1)*(m:ℤ))-(n:ℤ)*(q-3)*(q-3+1) =
      (m:ℤ)*((m:ℤ)-1)-6 := by rw [hm,hn]; ring
  linarith

theorem top_four_exact {n m : ℕ} {q : ℤ} (hq : 7 ≤ q)
    (hn : (n:ℤ)=q*q+q-3) (hm : (m:ℤ)=q*q-3*q+3)
    (A : Matrix (Fin n) (Fin n) Bool) (hA : rectangleFree A)
    (H : Finset (Fin n)) (hc : H.card=m)
    (htop : ∀ i ∈ H, ∀ j ∉ H, d A j ≤ d A i)
    (hE : q*(n:ℤ)+(m:ℤ) ≤ E A) :
    (∑ i ∈ H,d A i)=(q+1)*(m:ℤ) ∧
      ∑ j, (a A H j-(q-3))*(a A H j-(q-3)-1) ≤ 6 := by
  have hlo := top_weight_lower A H hc htop hE
  have hb := top_slack_four hn hm A hA H hc
  have hnon : 0 ≤ ∑ j, (a A H j-(q-3))*(a A H j-(q-3)-1) :=
    sum_nonneg fun j _ => int_mul_pred_nonneg _
  have heq : (∑ i ∈ H,d A i)=(q+1)*(m:ℤ) := by
    by_contra hh
    have hgap : 1 ≤ (∑ i ∈ H,d A i)-(q+1)*(m:ℤ) := by omega
    have hp := mul_le_mul_of_nonneg_left hgap (show 0 ≤ 2*(q-3) by omega)
    linarith
  rw [heq, sub_self, mul_zero, zero_add] at hb
  exact ⟨heq,hb⟩

theorem high_cap {n m b : ℕ} {q k : ℤ} (hk : 0 ≤ k)
    (A : Matrix (Fin n) (Fin n) Bool) (hA : rectangleFree A)
    (hgap : ((m+b+1:ℕ):ℤ)*(((m+b+1:ℕ):ℤ)-1) <
      2*k*(q+1)*((m+b+1:ℕ):ℤ)-(n:ℤ)*k*(k+1)) :
    (((univ : Finset (Fin n)).filter fun i => q < d A i).card) ≤ m+b := by
  classical
  let high := (univ : Finset (Fin n)).filter fun i => q < d A i
  change high.card ≤ m+b
  by_contra! hh
  obtain ⟨S,hsub,hcard⟩ := exists_subset_card_eq (s := high) (n := m+b+1) (by omega)
  have hsum : (q+1)*((m+b+1:ℕ):ℤ) ≤ ∑ i ∈ S,d A i := by
    calc
      _ = ∑ _i ∈ S, (q+1) := by rw [sum_const,nsmul_eq_mul,hcard]; ring
      _ ≤ _ := by
        apply sum_le_sum
        intro i hi
        have := (mem_filter.mp (hsub hi)).2
        omega
  have hdev := deviation_bound A hA S k
  rw [hcard] at hdev
  have hnon : 0 ≤ ∑ j, (a A S j-k)*(a A S j-k-1) :=
    sum_nonneg fun j _ => int_mul_pred_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hsum (show 0 ≤ 2*k by omega)
  linarith

theorem high_cap_four_parameter {n m : ℕ} {q : ℤ} (hq : 7 ≤ q)
    (hn : (n:ℤ)=q*q+q-3) (hm : (m:ℤ)=q*q-3*q+3) :
    ∃ b : ℕ, 3*((b:ℤ)+1)<2*q ∧
      ∀ A : Matrix (Fin n) (Fin n) Bool, rectangleFree A →
        ((univ.filter fun i => q < d A i).card ≤ m+b) := by
  have hcases : q=7 ∨ q=8 ∨ q=9 ∨ 10≤q := by omega
  rcases hcases with he | he | he | hlarge
  · subst q
    refine ⟨2,by norm_num,?_⟩
    intro A hA
    apply high_cap (k:=5) (by norm_num) A hA
    push_cast
    rw [hn,hm]
    norm_num
  · subst q
    refine ⟨3,by norm_num,?_⟩
    intro A hA
    apply high_cap (k:=6) (by norm_num) A hA
    push_cast
    rw [hn,hm]
    norm_num
  · subst q
    refine ⟨1,by norm_num,?_⟩
    intro A hA
    apply high_cap (k:=6) (by norm_num) A hA
    push_cast
    rw [hn,hm]
    norm_num
  · refine ⟨0,by omega,?_⟩
    intro A hA
    apply high_cap (k:=q-3) (by omega) A hA
    push_cast
    rw [hn,hm]
    have heq :
        2*(q-3)*(q+1)*(q*q-3*q+3+0+1) -
        (q*q+q-3)*(q-3)*(q-3+1) -
        (q*q-3*q+3+0+1)*(q*q-3*q+3+0+1-1) = 2*q-18 := by ring
    linarith

def deficit {α : Type*} [Fintype α] (f : α → ℤ) (q : ℤ) : ℤ :=
  ∑ i,max (q-f i) 0

theorem deficit_nonneg {α : Type*} [Fintype α] (f : α → ℤ) (q : ℤ) :
    0 ≤ deficit f q := sum_nonneg fun i _ => le_max_right _ _

theorem deficit_point {α : Type*} [Fintype α] (f : α → ℤ) (q : ℤ) (i : α) :
    q-f i ≤ deficit f q := by
  have h : max (q-f i) 0 ≤ ∑ j, max (q-f j) 0 :=
    single_le_sum (f := fun j => max (q-f j) 0) (fun j _ => le_max_right _ _) (mem_univ i)
  exact (le_max_left _ _).trans h

theorem deficit_identity {n : ℕ} (f : Fin n → ℤ) (q : ℤ)
    (hmax : ∀ i, f i ≤ q+1) :
    (∑ i,f i) = q*(n:ℤ) + (((univ.filter fun i => q < f i).card : ℕ):ℤ) - deficit f q := by
  classical
  have he (i : Fin n) : f i = q + (if q < f i then (1:ℤ) else 0) - max (q-f i) 0 := by
    by_cases h : q < f i
    · rw [if_pos h,max_eq_right (by omega)]
      have := hmax i
      omega
    · rw [if_neg h,max_eq_left (by omega)]
      ring
  calc
    (∑ i,f i) = ∑ i, (q + (if q < f i then (1:ℤ) else 0) - max (q-f i) 0) :=
      sum_congr rfl fun i _ => he i
    _ = _ := by
      rw [sum_sub_distrib,sum_add_distrib,sum_const,nsmul_eq_mul,card_univ,Fintype.card_fin]
      have hc : (∑ i : Fin n, (if q < f i then (1:ℤ) else 0)) =
          (((univ.filter fun i => q < f i).card : ℕ):ℤ) := by
        rw [← sum_filter,card_eq_sum_ones,Nat.cast_sum]
        simp
      rw [hc]
      unfold deficit
      ring

theorem top_four_profile {n m b : ℕ} {q : ℤ}
    (hmpos : 0 < m) (hmn : m < n)
    (A : Matrix (Fin n) (Fin n) Bool)
    (H : Finset (Fin n)) (hc : H.card=m)
    (htop : ∀ i ∈ H, ∀ j ∉ H, d A j ≤ d A i)
    (hT : (∑ i ∈ H,d A i)=(q+1)*(m:ℤ))
    (hE : q*(n:ℤ)+(m:ℤ) ≤ E A)
    (hcap : ((univ.filter fun i => q < d A i).card) ≤ m+b) :
    deficit (d A) q ≤ b ∧
      ((∃ i,d A i > q+1) → ∀ i,q ≤ d A i) := by
  classical
  by_cases hall : ∀ i ∈ H, q+1 ≤ d A i
  · have he : ∀ i ∈ H,d A i=q+1 := by
      intro i hi
      by_contra! hne
      have hgt : q+1<d A i := by have := hall i hi; omega
      have hs : (∑ _i ∈ H,(q+1))< ∑ i ∈ H,d A i :=
        sum_lt_sum hall ⟨i,hi,hgt⟩
      rw [sum_const,nsmul_eq_mul,hc,hT] at hs
      linarith
    obtain ⟨i,hi⟩ := card_pos.mp (by rw [hc]; exact hmpos)
    have hmax (j : Fin n) : d A j ≤ q+1 := by
      by_cases hj : j∈H
      · rw [he j hj]
      · exact (htop i hi j hj).trans (le_of_eq (he i hi))
    have hd := deficit_identity (d A) q hmax
    rw [E_rows] at hd
    have hcap' : (((univ.filter fun i => q < d A i).card : ℕ):ℤ) ≤ (m:ℤ)+(b:ℤ) := by
      exact_mod_cast hcap
    refine ⟨by linarith, ?_⟩
    rintro ⟨j,hj⟩
    exact (not_lt_of_ge (hmax j) hj).elim
  · push_neg at hall
    obtain ⟨i,hi,hd⟩ := hall
    have hlow (j : Fin n) (hj : j ∈ univ \ H) : d A j ≤ q := by
      have := htop i hi j (mem_sdiff.mp hj).2
      omega
    have hsplit := sum_sdiff (subset_univ H) (f := d A)
    rw [E_rows,hT] at hsplit
    have hsum : q*((n:ℤ)-(m:ℤ)) ≤ ∑ j ∈ univ \ H,d A j := by linarith
    have he : ∀ j ∈ univ \ H,d A j=q := by
      intro j hj
      by_contra! hne
      have hlt : d A j < q := by have := hlow j hj; omega
      have h := sum_lt_sum hlow ⟨j,hj,hlt⟩
      rw [sum_const,nsmul_eq_mul,compl_card_fin,hc] at h
      linarith
    have hrest : ((univ : Finset (Fin n)) \ H).Nonempty := by
      apply card_pos.mp
      rw [card_sdiff_of_subset (subset_univ _),card_univ,Fintype.card_fin,hc]
      omega
    obtain ⟨j,hj⟩ := hrest
    have hmin (k : Fin n) : q ≤ d A k := by
      by_cases hk : k∈H
      · have ht := htop k hk j (mem_sdiff.mp hj).2
        rwa [he j hj] at ht
      · rw [he k (mem_sdiff.mpr ⟨mem_univ _,hk⟩)]
    have hD : deficit (d A) q = 0 := by
      unfold deficit
      apply (sum_eq_zero_iff_of_nonneg (fun k _ => le_max_right _ _)).mpr
      intro k _
      exact max_eq_right (by have := hmin k; omega)
    exact ⟨by rw [hD]; omega, fun _ => hmin⟩

-- A board whose columns all have degree at least q has no row above q+1
-- at order n=q²+q-3.
theorem local_forces_degree_cap {n : ℕ} {q : ℤ} (hq : 1≤q)
    (hn : (n:ℤ)=q*q+q-3)
    (A : Matrix (Fin n) (Fin n) Bool) (hA : rectangleFree A)
    (hmin : ∀ j,q≤c A j) :
    ∀ i,d A i ≤ q+1 := by
  intro i
  have hmul : d A i*(q-1) ≤ (n:ℤ)-1 := by
    rw [d_sum,sum_mul]
    apply le_trans _ (local_int A hA i)
    apply sum_le_sum
    intro j _
    apply mul_le_mul_of_nonneg_left
    · have := hmin j
      omega
    · by_cases h : A i j=true <;> simp [w,h]
  by_contra! hgt
  have h := mul_le_mul_of_nonneg_right (show q+2≤d A i by omega) (show 0≤q-1 by omega)
  rw [hn] at hmul
  have he : (q+2)*(q-1) = q*q+q-2 := by ring
  linarith


end RectangleResearch

namespace RectangleResearch
open RectFreeCounting Finset

theorem near_four_weighted_contradiction {n m b : ℕ} {q : ℤ}
    (hq : 2 ≤ q)
    (hn : (n:ℤ)=q*q+q-3)
    (hm : (m:ℤ)=q*q-3*q+3)
    (hb : 3*((b:ℤ)+1)<2*q)
    (A : Matrix (Fin n) (Fin n) Bool) (hA : rectangleFree A)
    (H : Finset (Fin n)) (hc : H.card=m)
    (hT : (q+1)*(m:ℤ) ≤ ∑ i ∈ H,d A i)
    (hdev : ∑ j,(a A H j-(q-3))*(a A H j-(q-3)-1)≤6)
    (hE : q*(n:ℤ)+(m:ℤ)≤E A)
    (hcmin : ∀ j,q-(b:ℤ)≤c A j)
    (hcmax : ∀ j,c A j≤q+1) : False := by
  let z (j : Fin n) := a A H j-(q-3)
  let W (j : Fin n) := q+1-c A j
  let Δ (j : Fin n) := max (z j-1) 0
  have hWnon (j : Fin n) : 0≤W j := by unfold W; have := hcmax j; omega
  have hWmax (j : Fin n) : W j≤(b:ℤ)+1 := by unfold W; have := hcmin j; omega
  have hWsum : ∑ j,W j ≤ (n:ℤ)-(m:ℤ) := by
    unfold W
    rw [sum_sub_distrib,sum_const,nsmul_eq_mul,card_univ,Fintype.card_fin,E_cols]
    linarith
  have hDsum : ∑ j, Δ j ≤ 3 := by
    have h := sum_max_excess z 6 hdev
    change 2*(∑ j, Δ j)≤6 at h
    omega
  have ha (j : Fin n) : a A H j≤q-2+Δ j := by
    unfold Δ z
    have h := le_max_left (a A H j-(q-3)-1) 0
    omega
  have hDnon (j : Fin n) : 0≤Δ j := le_max_right _ _
  have hpoint (j : Fin n) :
      a A H j*W j≤(q-2)*W j+((b:ℤ)+1)*Δ j := by
    have h1 := mul_le_mul_of_nonneg_right (ha j) (hWnon j)
    have h2 := mul_le_mul_of_nonneg_left (hWmax j) (hDnon j)
    linarith [show (q-2+Δ j)*W j=(q-2)*W j+Δ j*W j by ring,
      mul_comm (Δ j) ((b:ℤ)+1)]
  have hup := sum_le_sum (fun j (_ : j∈(univ : Finset (Fin n))) => hpoint j)
  rw [sum_add_distrib,← mul_sum,← mul_sum] at hup
  have hmul1 := mul_le_mul_of_nonneg_left hWsum (show 0≤q-2 by omega)
  have hmul2 := mul_le_mul_of_nonneg_left hDsum (show 0≤(b:ℤ)+1 by omega)
  have hlow := weighted_bound A hA H q
  change q*(∑ i ∈ H,d A i)-(H.card:ℤ)*((n:ℤ)-1)≤∑ j,a A H j*W j at hlow
  rw [hc] at hlow
  have hmul3 := mul_le_mul_of_nonneg_left hT (show 0≤q by omega)
  have heq : q*((q+1)*(m:ℤ))-(m:ℤ)*((n:ℤ)-1)=4*(m:ℤ) := by rw [hn]; ring
  have heq' : 4*(m:ℤ)-(q-2)*((n:ℤ)-(m:ℤ))=2*q := by rw [hn,hm]; ring
  linarith

theorem four_deletion_upper_ge_seven {n m : ℕ} {q : ℤ}
    (hq : 7≤q)
    (hn : (n:ℤ)=q*q+q-3)
    (hm : (m:ℤ)=q*q-3*q+3)
    (A : Matrix (Fin n) (Fin n) Bool) (hA : rectangleFree A) :
    E A≤q*(n:ℤ)+(m:ℤ)-1 := by
  classical
  by_contra! hcontra
  have hE : q*(n:ℤ)+(m:ℤ)≤E A := by omega
  have hmn : m<n := by omega
  have hmpos : 0<m := by
    have h := mul_nonneg (show 0≤q by omega) (show 0≤q-3 by omega)
    nlinarith
  obtain ⟨b,hb,hcap⟩ := high_cap_four_parameter hq hn hm
  obtain ⟨H,hH,htop⟩ := top_set (d A) m (by simpa using hmn.le)
  obtain ⟨hTex,hdev⟩ := top_four_exact hq hn hm A hA H hH htop hE
  obtain ⟨hD,hhigh⟩ := top_four_profile hmpos hmn A H hH htop hTex hE (hcap A hA)
  have hAT := transpose_free A hA
  have hET : q*(n:ℤ)+(m:ℤ)≤E A.transpose := by rwa [transpose_E]
  obtain ⟨J,hJ,htopJ⟩ := top_set (d A.transpose) m (by simpa using hmn.le)
  obtain ⟨hTexJ,hdevJ⟩ := top_four_exact hq hn hm A.transpose hAT J hJ htopJ hET
  obtain ⟨hDJ,hhighJ⟩ := top_four_profile hmpos hmn A.transpose J hJ htopJ hTexJ hET
      (hcap A.transpose hAT)
  have hminrow : ∀ i,q-(b:ℤ)≤d A i := by
    intro i
    have hi := deficit_point (d A) q i
    omega
  have hmincol : ∀ j,q-(b:ℤ)≤c A j := by
    intro j
    have hi := deficit_point (d A.transpose) q j
    rw [transpose_d] at hi
    omega
  by_cases hcolmax : ∀ j,c A j≤q+1
  · exact near_four_weighted_contradiction (by omega) hn hm hb A hA H hH
      (le_of_eq hTex.symm) hdev hE hmincol hcolmax
  · push Not at hcolmax
    have he : ∃ i,d A.transpose i>q+1 := by
      obtain ⟨j,hj⟩ := hcolmax
      exact ⟨j,by rwa [transpose_d]⟩
    have hcolmin : ∀ j,q≤c A j := by
      intro j
      have := hhighJ he j
      rwa [transpose_d] at this
    have hrowmax := local_forces_degree_cap (by omega) hn A hA hcolmin
    exact near_four_weighted_contradiction (by omega) hn hm hb A.transpose hAT J hJ
      (le_of_eq hTexJ.symm) hdevJ hET
      (fun i => by rw [transpose_c]; exact hminrow i)
      (fun i => by rw [transpose_c]; exact hrowmax i)

theorem four_deletion_polynomial_ge_seven {n m : ℕ} {q : ℤ}
    (hq : 7≤q)
    (hn : (n:ℤ)=q*q+q-3)
    (hm : (m:ℤ)=q*q-3*q+3)
    (A : Matrix (Fin n) (Fin n) Bool) (hA : rectangleFree A) :
    E A≤q^3+2*q^2-6*q+2 := by
  have h := four_deletion_upper_ge_seven hq hn hm A hA
  rw [hn,hm] at h
  convert h using 1 <;> ring


end RectangleResearch

namespace ProjectiveBoard

abbrev Pt (K : Type*) := Sum (K × K) (Option K)

def x {K : Type*} [Zero K] [One K] : Pt K → K
  | .inl _ => 1
  | .inr _ => 0

def y {K : Type*} [Zero K] [One K] : Pt K → K
  | .inl p => p.1
  | .inr (some _) => 1
  | .inr none => 0

def z {K : Type*} [Zero K] [One K] : Pt K → K
  | .inl p => p.2
  | .inr (some t) => t
  | .inr none => 1

def dot {K : Type*} [Field K] (u v : Pt K) : K :=
  x u * x v + y u * y v + z u * z v

theorem dot_symm {K : Type*} [Field K] (u v : Pt K) : dot u v = dot v u := by
  unfold dot
  ring

theorem eq_of_minors {K : Type*} [Field K] (u v : Pt K)
    (hxy : x u * y v - y u * x v = 0)
    (hxz : x u * z v - z u * x v = 0)
    (hyz : y u * z v - z u * y v = 0) : u = v := by
  rcases u with ⟨a,b⟩ | (_ | a)
  all_goals rcases v with ⟨c,d⟩ | (_ | c)
  all_goals simp [x,y,z] at hxy hxz hyz ⊢
  all_goals try contradiction
  all_goals try constructor
  all_goals try first | exact (sub_eq_zero.mp hxy).symm | exact (sub_eq_zero.mp hxz).symm | exact (sub_eq_zero.mp hyz).symm

private theorem annihilate_minors {K : Type*} [Field K]
    (a b c d e f r s t R S T : K)
    (h1 : a*r+b*s+c*t = 0) (h2 : d*r+e*s+f*t = 0)
    (h3 : a*R+b*S+c*T = 0) (h4 : d*R+e*S+f*T = 0)
    (hD : a*e-b*d ≠ 0) :
    r*S-s*R = 0 ∧ r*T-t*R = 0 ∧ s*T-t*S = 0 := by
  have hRT : (a*e-b*d)*(r*T-t*R) = 0 := by
    linear_combination e*T*h1 - b*T*h2 - e*t*h3 + b*t*h4
  have hST : (a*e-b*d)*(s*T-t*S) = 0 := by
    linear_combination a*T*h2 - d*T*h1 - a*t*h4 + d*t*h3
  have hRS : (a*e-b*d)*(r*S-s*R) = 0 := by
    have H : (a*e-b*d)*(r*S-s*R) = (b*f-c*e)*(t*S-s*T) := by
      linear_combination e*S*h1 - b*S*h2 - e*s*h3 + b*s*h4
    have hs : s*T-t*S = 0 := (mul_eq_zero.mp hST).resolve_left hD
    have hrev : t*S-s*T = 0 := by linear_combination -hs
    rw [H, hrev, mul_zero]
  exact ⟨(mul_eq_zero.mp hRS).resolve_left hD,
    (mul_eq_zero.mp hRT).resolve_left hD, (mul_eq_zero.mp hST).resolve_left hD⟩

theorem unique_common_neighbor {K : Type*} [Field K] (u v w z' : Pt K)
    (huv : u ≠ v) (h1 : dot u w = 0) (h2 : dot v w = 0)
    (h3 : dot u z' = 0) (h4 : dot v z' = 0) : w = z' := by
  unfold dot at h1 h2 h3 h4
  by_cases hxy : x u * y v - y u * x v = 0
  · by_cases hxz : x u * z v - z u * x v = 0
    · have hyz : y u * z v - z u * y v ≠ 0 :=
        fun h => huv (eq_of_minors u v hxy hxz h)
      have h := annihilate_minors (y u) (z u) (x u) (y v) (z v) (x v)
        (y w) (z w) (x w) (y z') (z z') (x z')
        (by linear_combination h1) (by linear_combination h2)
        (by linear_combination h3) (by linear_combination h4) hyz
      exact eq_of_minors w z' (by linear_combination -h.2.1)
        (by linear_combination -h.2.2) h.1
    · have h := annihilate_minors (x u) (z u) (y u) (x v) (z v) (y v)
        (x w) (z w) (y w) (x z') (z z') (y z')
        (by linear_combination h1) (by linear_combination h2)
        (by linear_combination h3) (by linear_combination h4) hxz
      exact eq_of_minors w z' h.2.1 h.1 (by linear_combination -h.2.2)
  · have h := annihilate_minors (x u) (y u) (z u) (x v) (y v) (z v)
      (x w) (y w) (z w) (x z') (y z') (z z') h1 h2 h3 h4 hxy
    exact eq_of_minors w z' h.1 h.2.1 h.2.2


variable {K : Type*} [Field K] [Fintype K]
private theorem card_param {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (p : β → Prop) [DecidablePred p] (f : α → β) (hinj : Function.Injective f)
    (h : ∀ b : β, p b ↔ ∃ a : α, f a = b) :
    (Finset.univ.filter p).card = Fintype.card α := by
  have hh : Finset.univ.filter p = Finset.univ.image f := by
    ext b
    simp [h]
  rw [hh, Finset.card_image_of_injective _ hinj, Finset.card_univ]

private theorem linear_eq_iff {a b c : K} (hc : c ≠ 0) :
    a + c * b = 0 ↔ b = -a / c := by
  rw [eq_div_iff hc, mul_comm b c]
  constructor
  · intro h
    calc
      c * b = (a + c * b) - a := by rw [add_comm a, add_sub_cancel_right]
      _ = -a := by rw [h]; simp
  · intro h
    rw [h, add_neg_cancel]

set_option maxHeartbeats 1000000 in
theorem card_projective_line [DecidableEq K] (A B C : K)
    (h : A ≠ 0 ∨ B ≠ 0 ∨ C ≠ 0) :
    (Finset.univ.filter fun v : Pt K => A * x v + B * y v + C * z v = 0).card =
      Fintype.card K + 1 := by
  classical
  by_cases hC : C = 0
  · by_cases hB : B = 0
    · have hA : A ≠ 0 := by
        rcases h with hA | hB' | hC'
        · exact hA
        · exact False.elim (hB' hB)
        · exact False.elim (hC' hC)
      let f : Option K → Pt K := Sum.inr
      have hi : Function.Injective f := by
        intro a b hab
        exact Sum.inr.inj hab
      rw [← Fintype.card_option]
      apply card_param _ f hi
      intro v
      cases v with
      | inl p => simp [x, y, hA, hB, hC, f]
      | inr o => simp [x, hB, hC, f]
    · let f : Option K → Pt K
        | some t => .inl (-A / B, t)
        | none => .inr none
      have hi : Function.Injective f := by
        intro a b hab
        cases a <;> cases b <;> simpa [f] using hab
      rw [← Fintype.card_option]
      apply card_param _ f hi
      intro v
      cases v with
      | inl p =>
          rcases p with ⟨s, t⟩
          simp only [x, y, z, mul_one, hC, zero_mul, add_zero, linear_eq_iff hB]
          constructor
          · intro hs
            exact ⟨some t, by simp [f, hs]⟩
          · rintro ⟨o, ho⟩
            cases o <;> simp [f] at ho
            exact ho.1.symm
      | inr o =>
          cases o with
          | none =>
              constructor
              · intro _
                exact ⟨none, rfl⟩
              · intro _
                simp [x, y, z, hC]
          | some t =>
              simp [x, y, z, hB, hC]
              intro o
              cases o <;> simp [f]
  · let f : Option K → Pt K
      | some t => .inl (t, -(A + B * t) / C)
      | none => .inr (some (-B / C))
    have hi : Function.Injective f := by
      intro a b hab
      cases a <;> cases b <;> simp [f] at hab ⊢
      first | exact hab.1 | exact hab
    rw [← Fintype.card_option]
    apply card_param _ f hi
    intro v
    cases v with
    | inl p =>
        rcases p with ⟨s, t⟩
        simp only [x, y, z, mul_one, linear_eq_iff hC]
        constructor
        · intro ht
          exact ⟨some s, by simp [f, ht]⟩
        · rintro ⟨o, ho⟩
          cases o <;> simp [f] at ho
          rcases ho with ⟨rfl, ht⟩
          simpa using ht.symm
    | inr o =>
        cases o with
        | none =>
            simp [x, y, z, hC]
            intro o
            cases o <;> simp [f]
        | some t =>
            simp only [x, y, z, mul_zero, mul_one, zero_add, linear_eq_iff hC]
            constructor
            · intro ht
              exact ⟨none, by simp [f, ht]⟩
            · rintro ⟨o, ho⟩
              cases o <;> simp [f] at ho
              exact ho.symm

theorem card_neighbors [DecidableEq K] (u : Pt K) :
    (Finset.univ.filter fun v : Pt K => dot u v = 0).card = Fintype.card K + 1 := by
  apply card_projective_line
  cases u with
  | inl p => simp [x]
  | inr o => cases o <;> simp [x, y, z]


end ProjectiveBoard


namespace ProjectiveBoard
open RectFreeCounting

def dotNeg {K : Type*} [Field K] (u v : Pt K) : K :=
  x u * x v - y u * y v + z u * z v

def flipY {K : Type*} [Field K] : Pt K → Pt K
  | .inl (a,b) => .inl (-a,b)
  | .inr (some t) => .inr (some (-t))
  | .inr none => .inr none

theorem flipY_inj {K : Type*} [Field K] : Function.Injective (flipY (K := K)) := by
  have hinv (u : Pt K) : flipY (flipY u) = u := by
    rcases u with ⟨a,b⟩ | (_ | a) <;> simp [flipY]
  intro a b h
  rw [← hinv a, ← hinv b, h]

theorem signed_zero {K : Type*} [Field K] (u v : Pt K) :
    dotNeg u v = 0 ↔ dot (flipY u) v = 0 := by
  rcases u with ⟨a,b⟩ | (_ | a)
  · simp [dotNeg, dot, flipY, x,y,z, neg_mul, sub_eq_add_neg]
  · simp [dotNeg, dot, flipY, x,y,z]
  · simp only [dotNeg,dot,flipY,x,y,z,zero_mul,one_mul,zero_add,zero_sub,neg_mul]
    constructor <;> intro h <;> linear_combination -h

theorem signed_symm {K : Type*} [Field K] (u v : Pt K) : dotNeg u v = dotNeg v u := by
  unfold dotNeg
  ring


end ProjectiveBoard

namespace ProjectiveBoard
open RectFreeCounting RectangleResearch Finset

noncomputable def si {K : Type*} [Field K] (u v : Pt K) : ℤ := by
  classical
  exact if dotNeg u v=0 then 1 else 0

theorem si_symm {K : Type*} [Field K] (u v : Pt K) : si u v = si v u := by
  unfold si
  rw [signed_symm u v]

theorem si_row_sum {K : Type*} [Field K] [Fintype K] (u : Pt K) :
    (∑ v,si u v) = (Fintype.card K:ℤ)+1 := by
  classical
  have h : (univ.filter fun v : Pt K => dotNeg u v = 0) =
      univ.filter (fun v : Pt K => dot (flipY u) v = 0) := by
    ext v
    simp [signed_zero]
  have hcount : (univ.filter fun v : Pt K => dotNeg u v = 0).card = Fintype.card K+1 := by
    rw [h]
    exact card_neighbors (flipY u)
  have hc := congrArg (fun x : ℕ => (x:ℤ)) hcount
  rw [card_eq_sum_ones,Nat.cast_sum,Nat.cast_add,Nat.cast_one,sum_filter] at hc
  convert hc using 1
  apply sum_congr rfl
  intro v _
  by_cases ht : dotNeg u v=0 <;> simp [si,ht]

theorem principal_count {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → α → ℤ) (h : ∀ i j,f i j=f j i) (r : ℤ)
    (hreg : ∀ i,∑ j,f i j=r)
    (D : Finset α) :
    (∑ i ∈ univ \ D,∑ j ∈ univ \ D,f i j) =
      (Fintype.card α:ℤ)*r-2*(D.card:ℤ)*r+(∑ i ∈ D,∑ j ∈ D,f i j) := by
  let S := (univ : Finset α) \ D
  have h1 : (∑ i ∈ S,∑ j ∈ S,f i j)+(∑ i ∈ S,∑ j ∈ D,f i j) =
      (∑ i ∈ S,∑ j,f i j) := by
    rw [←sum_add_distrib]
    apply sum_congr rfl
    intro i _
    exact sum_sdiff (subset_univ _) (f := f i)
  have h2 : (∑ i ∈ D,∑ j ∈ S,f i j)+(∑ i ∈ D,∑ j ∈ D,f i j) =
      (∑ i ∈ D,∑ j,f i j) := by
    rw [←sum_add_distrib]
    apply sum_congr rfl
    intro i _
    exact sum_sdiff (subset_univ _) (f := f i)
  have hs : (∑ i ∈ S,∑ j ∈ D,f i j)=(∑ i ∈ D,∑ j ∈ S,f i j) := by
    rw [sum_comm]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    exact h j i
  simp_rw [hreg,sum_const,nsmul_eq_mul] at h1 h2
  have hc : (S.card:ℤ) = (Fintype.card α:ℤ)-(D.card:ℤ) := compl_card D
  change (∑ i ∈ S,∑ j ∈ S,f i j)=_
  rw [hc] at h1
  linarith

theorem principal_projective {K : Type*} [Field K] [Fintype K]
    (D : Finset (Pt K)) (n : ℕ)
    (hn : n=Fintype.card K*Fintype.card K+Fintype.card K+1-D.card) :
    ∃ B : Matrix (Fin n) (Fin n) Bool, B.IsSymm ∧ rectangleFree B ∧
      E B =
      ((Fintype.card K:ℤ)*(Fintype.card K:ℤ)+(Fintype.card K:ℤ)+1)*
        ((Fintype.card K:ℤ)+1) -
        2*(D.card:ℤ)*((Fintype.card K:ℤ)+1) + ∑ i ∈ D,∑ j ∈ D,si i j := by
  classical
  let S := (univ : Finset (Pt K)) \ D
  have hP : Fintype.card (Pt K) = Fintype.card K*Fintype.card K+Fintype.card K+1 := by
    simp [Pt,add_assoc]
  have hc : Fintype.card ↥S = n := by
    rw [Fintype.card_coe]
    unfold S
    rw [card_sdiff_of_subset (subset_univ _),card_univ,hP,hn]
  let e : Fin n ≃ ↥S := (Fintype.equivFinOfCardEq hc).symm
  let B : Matrix (Fin n) (Fin n) Bool := fun i j => decide (dotNeg (e i).val (e j).val=0)
  refine ⟨B,?_,?_,?_⟩
  · apply Matrix.IsSymm.ext
    intro i j
    change decide (dotNeg (e j).val (e i).val=0)=decide (dotNeg (e i).val (e j).val=0)
    rw [signed_symm (e j).val (e i).val]
  · intro i i' j j' hii hjj hr
    have heinj : Function.Injective (fun i => (e i).val) :=
      fun _ _ he => e.injective (Subtype.ext he)
    have hp : flipY (e i).val ≠ flipY (e i').val :=
      fun h => hii (heinj (flipY_inj h))
    have hw := unique_common_neighbor (flipY (e i).val) (flipY (e i').val)
        (e j).val (e j').val hp
        ((signed_zero _ _).mp (of_decide_eq_true hr.1))
        ((signed_zero _ _).mp (of_decide_eq_true hr.2.2.1))
        ((signed_zero _ _).mp (of_decide_eq_true hr.2.1))
        ((signed_zero _ _).mp (of_decide_eq_true hr.2.2.2))
    exact hjj (heinj hw)
  · rw [←E_rows B]
    simp_rw [d_sum]
    have heq (i j : Fin n) : w B i j = si (e i).val (e j).val := by
      unfold w si
      change (if decide (dotNeg (e i).val (e j).val=0)=true then (1:ℤ) else 0) = _
      simp
    simp_rw [heq]
    have hi (u : ↥S) : (∑ j : Fin n,si u.val (e j).val)=∑ j ∈ S,si u.val j := by
      rw [Equiv.sum_comp e (fun v : ↥S => si u.val v.val),sum_coe_sort]
    simp_rw [hi]
    rw [Equiv.sum_comp e (fun u : ↥S => ∑ j ∈ S,si u.val j),sum_coe_sort S (fun i => ∑ j ∈ S,si i j)]
    have hcount := principal_count (fun u v : Pt K => si u v)
      si_symm ((Fintype.card K:ℤ)+1) si_row_sum D
    rw [hP] at hcount
    push_cast at hcount
    exact hcount

theorem four_deleted_points {K : Type*} [Field K] [Fintype K] :
    ∃ D : Finset (Pt K), D.card=4 ∧ (∑ i ∈ D,∑ j ∈ D,si i j)=9 := by
  classical
  let p1 : Pt K := .inl (0,0)
  let p2 : Pt K := .inr (.some 0)
  let p3 : Pt K := .inr none
  let p4 : Pt K := .inl (1,0)
  let D : Finset (Pt K) := {p1,p2,p3,p4}
  have h34 : p3 ∉ ({p4} : Finset (Pt K)) := by simp [p3,p4]
  have h234 : p2 ∉ ({p3,p4} : Finset (Pt K)) := by simp [p2,p3,p4]
  have h1234 : p1 ∉ ({p2,p3,p4} : Finset (Pt K)) := by simp [p1,p2,p3,p4]
  refine ⟨D,?_,?_⟩
  · simp [D,card_insert_of_notMem h1234,card_insert_of_notMem h234,card_insert_of_notMem h34]
  · simp [D,sum_insert h1234,sum_insert h234,sum_insert h34,si,dotNeg,x,y,z,p1,p2,p3,p4]

/-- The symmetric lower bound at four below a projective-plane order. -/
theorem four_deletion_lower (K : Type*) [Field K] [Fintype K] :
    let q := Fintype.card K
    let n := q*q+q-3
    ∃ B : Matrix (Fin n) (Fin n) Bool, B.IsSymm ∧ rectangleFree B ∧
       E B=(q:ℤ)^3+2*(q:ℤ)^2-6*(q:ℤ)+2 := by
  let q := Fintype.card K
  let n := q*q+q-3
  have hq : 2≤q := Fintype.one_lt_card
  obtain ⟨D,hD,h9⟩ := four_deleted_points (K := K)
  have hn : n=q*q+q+1-D.card := by rw [hD]; dsimp [n]; omega
  obtain ⟨B,hs,hf,hE⟩ := principal_projective D n hn
  refine ⟨B,hs,hf,?_⟩
  rw [hE,hD,h9]
  simp only [Nat.cast_ofNat]
  ring

theorem four_deletion_finite_field_ge_seven (K : Type*) [Field K] [Fintype K]
    (hq : 7≤Fintype.card K) :
    let q := Fintype.card K
    let n := q*q+q-3
    ∃ B : Matrix (Fin n) (Fin n) Bool, B.IsSymm ∧ rectangleFree B ∧
      ∀ A : Matrix (Fin n) (Fin n) Bool, rectangleFree A → numberOfOnes A ≤ numberOfOnes B := by
  let q := Fintype.card K
  let n := q*q+q-3
  let m := q*q+3-3*q
  have hqn : 7≤q := hq
  have hqi : 7≤(q:ℤ) := by exact_mod_cast hqn
  have hqn' : 3≤q*q+q := by nlinarith
  have hqm : 3*q≤q*q+3 := by
    nlinarith [Nat.zero_le (q*q), show q*q≥7*q by nlinarith]
  have hn : (n:ℤ)=(q:ℤ)*(q:ℤ)+(q:ℤ)-3 := by
    dsimp [n]
    rw [Nat.cast_sub hqn',Nat.cast_add,Nat.cast_mul]
    norm_num
  have hm : (m:ℤ)=(q:ℤ)*(q:ℤ)-3*(q:ℤ)+3 := by
    dsimp [m]
    rw [Nat.cast_sub hqm,Nat.cast_add,Nat.cast_mul,Nat.cast_mul]
    norm_num
    ring
  obtain ⟨B,hs,hf,hE⟩ := four_deletion_lower K
  refine ⟨B,hs,hf,?_⟩
  intro A hA
  have hub := four_deletion_polynomial_ge_seven hqi hn hm A hA
  rw [← hE] at hub
  exact Int.ofNat_le.mp hub


end ProjectiveBoard

namespace RectangleResearch
open RectFreeCounting Finset

/-- For a top set near its lower target, all selected rows have degree at least q,
and the total deficit below q comes from unselected rows. -/
theorem relaxed_profile {n m b : ℕ} {q u : ℤ}
    (hu : 0≤u) (hmu : u<(m:ℤ)) (hlu : u<(n:ℤ)-(m:ℤ))
    (A : Matrix (Fin n) (Fin n) Bool)
    (H : Finset (Fin n)) (hc : H.card=m)
    (htop : ∀ i ∈ H, ∀ j ∉ H, d A j≤d A i)
    (hT : (∑ i ∈ H,d A i)≤(q+1)*(m:ℤ)+u)
    (hE : q*(n:ℤ)+(m:ℤ)≤E A)
    (hcap : (univ.filter fun i => q<d A i).card≤m+b) :
    let R := (univ : Finset (Fin n)) \ H
    let k := (R.filter fun i => q<d A i).card
    (∀ i∈H,q≤d A i) ∧ (∀ j∈R,d A j≤q+1) ∧
    k≤b ∧ (0<k → ∀ i∈H,q+1≤d A i) ∧
    deficit (d A) q≤(∑ i∈H,d A i)-(q+1)*(m:ℤ)+(k:ℤ) := by
  classical
  let R := (univ : Finset (Fin n)) \ H
  let K := R.filter fun i => q<d A i
  let k := K.card
  change (∀ i∈H,q≤d A i) ∧ (∀ j∈R,d A j≤q+1) ∧
    k≤b ∧ (0<k → ∀ i∈H,q+1≤d A i) ∧
    deficit (d A) q≤(∑ i∈H,d A i)-(q+1)*(m:ℤ)+(k:ℤ)
  have hcardR : (R.card:ℤ)=(n:ℤ)-(m:ℤ) := by rw [compl_card_fin H,hc]
  have hsplit : (∑ j∈R,d A j)+(∑ i∈H,d A i)=E A := by
    rw [←E_rows]
    exact sum_sdiff (subset_univ H)
  have hRestLow : q*((n:ℤ)-(m:ℤ))-u≤∑ j∈R,d A j := by linarith
  have htopmin : ∀ i∈H,q≤d A i := by
    intro i hi
    by_contra! hbad
    have hrest : ∀ j∈R,d A j≤q-1 := by
      intro j hj
      have h := htop i hi j (mem_sdiff.mp hj).2
      omega
    have hup : (∑ j∈R,d A j)≤(q-1)*((n:ℤ)-(m:ℤ)) := by
      calc
        _≤∑ _j∈R,(q-1) := sum_le_sum hrest
        _=_ := by rw [sum_const,nsmul_eq_mul,hcardR]; ring
    linarith
  have hRestMax : ∀ j∈R,d A j≤q+1 := by
    intro j hj
    by_contra! hbad
    have hlead : ∀ i∈H,q+2≤d A i := by
      intro i hi
      have h:=htop i hi j (mem_sdiff.mp hj).2
      omega
    have hlo : (q+2)*(m:ℤ)≤∑ i∈H,d A i := by
      calc
        _=∑ _i∈H,(q+2) := by rw [sum_const,nsmul_eq_mul,hc]; ring
        _≤_ := sum_le_sum hlead
    linarith
  have hK : 0<k → ∀ i∈H,q+1≤d A i := by
    intro hk i hi
    obtain ⟨j,hj⟩ := card_pos.mp hk
    have ⟨hjR,hjhigh⟩ := mem_filter.mp hj
    have h := htop i hi j (mem_sdiff.mp hjR).2
    omega
  have hkcap : k≤b := by
    by_cases hz : k=0
    · omega
    · have hhigh : H∪K⊆univ.filter (fun i => q<d A i) := by
        intro i hi
        rcases mem_union.mp hi with hi | hi
        · exact mem_filter.mpr ⟨mem_univ _,by have := hK (by omega) i hi; omega⟩
        · exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hi).2⟩
      have hdis : Disjoint H K := by
        rw [disjoint_left]
        intro i hi hiK
        exact (mem_sdiff.mp (mem_filter.mp hiK).1).2 hi
      have hh := card_le_card hhigh
      rw [card_union_of_disjoint hdis,hc] at hh
      change m+k≤_ at hh
      omega
  have hsumD : deficit (d A) q=∑ j∈R,max (q-d A j) 0 := by
    unfold deficit
    have hd := sum_sdiff (subset_univ H) (f := fun j=>max (q-d A j) 0)
    have hz : (∑ j∈H,max (q-d A j) 0)=0 := by
      apply sum_eq_zero
      intro j hj
      exact max_eq_right (by have := htopmin j hj; omega)
    rw [hz,add_zero] at hd
    exact hd.symm
  have hk_eq : (k:ℤ)=∑ j∈R,(if q<d A j then (1:ℤ) else 0) := by
    unfold k K
    rw [card_eq_sum_ones,Nat.cast_sum,sum_filter]
    simp
  have hRestId : (∑ j∈R,d A j)=q*((n:ℤ)-(m:ℤ))+(k:ℤ)-deficit (d A) q := by
    calc
      (∑ j∈R,d A j)=∑ j∈R,(q+(if q<d A j then (1:ℤ) else 0)-max (q-d A j) 0) := by
        apply sum_congr rfl
        intro j hj
        by_cases h : q<d A j
        · rw [if_pos h,max_eq_right (by omega)]
          have := hRestMax j hj
          omega
        · rw [if_neg h,max_eq_left (by omega)]
          ring
      _=_ := by
        rw [sum_sub_distrib,sum_add_distrib,sum_const,nsmul_eq_mul,hcardR,←hk_eq,←hsumD]
        ring
  exact ⟨htopmin,hRestMax,hkcap,hK,by linarith⟩

theorem local_deficit_neighbor {n : ℕ} (A : Matrix (Fin n) (Fin n) Bool)
    (hA : rectangleFree A) (q : ℤ) (i : Fin n) :
    d A i*(q-1)-(∑ j,w A i j*max (q-c A j) 0)≤(n:ℤ)-1 := by
  have hpoint (j : Fin n) :
      w A i j*(q-1)-w A i j*max (q-c A j) 0≤w A i j*(c A j-1) := by
    have hm := le_max_left (q-c A j) 0
    by_cases hj : A i j=true
    · simp [w,hj]
      linarith
    · simp [w,hj]
  have h := sum_le_sum (fun j (_ : j∈(univ : Finset (Fin n))) => hpoint j)
  rw [sum_sub_distrib,←sum_mul,←d_sum] at h
  exact h.trans (local_int A hA i)

theorem local_deficit_total {n : ℕ} (A : Matrix (Fin n) (Fin n) Bool)
    (hA : rectangleFree A) (q : ℤ) (i : Fin n) :
    d A i*(q-1)-deficit (c A) q≤(n:ℤ)-1 := by
  have hp : (∑ j,w A i j*max (q-c A j) 0)≤deficit (c A) q := by
    unfold deficit
    apply sum_le_sum
    intro j _
    by_cases hj : A i j=true <;> simp [w,hj]
  linarith [local_deficit_neighbor A hA q i]

theorem large_count_deficit {n : ℕ} {q : ℤ} (hq : 1≤q)
    (hn : (n:ℤ)=q*q+q-3)
    (A : Matrix (Fin n) (Fin n) Bool) (hA : rectangleFree A) :
    2*((univ.filter fun i => q+1<d A i).card:ℤ)≤(q-1)*deficit (c A) q := by
  classical
  let L := (univ : Finset (Fin n)).filter fun i => q+1<d A i
  let δ (j : Fin n) := max (q-c A j) 0
  have hδ (j : Fin n) : 0≤δ j := le_max_right _ _
  have hlocal (i : Fin n) (hi : i∈L) : 2≤∑ j,w A i j*δ j := by
    have hd : q+2≤d A i := by have := (mem_filter.mp hi).2; omega
    have hp := mul_le_mul_of_nonneg_right hd (show 0≤q-1 by omega)
    have h := local_deficit_neighbor A hA q i
    change d A i*(q-1)-(∑ j,w A i j*δ j)≤(n:ℤ)-1 at h
    rw [hn] at h
    have heq : (q+2)*(q-1)=q*q+q-2 := by ring
    linarith
  have hlo : 2*(L.card:ℤ)≤∑ i∈L,∑ j,w A i j*δ j := by
    calc
      _=∑ _i∈L,(2:ℤ) := by rw [sum_const,nsmul_eq_mul]; ring
      _≤_ := sum_le_sum hlocal
  rw [sum_comm (s:=L)] at hlo
  simp_rw [←sum_mul,←a_sum] at hlo
  have hsub (j : Fin n) : a A L j≤c A j := by
    rw [a_sum,c_sum]
    apply sum_le_sum_of_subset_of_nonneg (subset_univ _)
    intro i _ _
    by_cases h : A i j=true <;> simp [w,h]
  have hup : (∑ j,a A L j*δ j)≤(q-1)*deficit (c A) q := by
    unfold deficit
    rw [mul_sum]
    apply sum_le_sum
    intro j _
    by_cases hz : q≤c A j
    · have he : δ j=0 := max_eq_right (by omega)
      change a A L j*δ j≤(q-1)*δ j
      rw [he]
      simp
    · have hmin : c A j≤q-1 := by omega
      exact mul_le_mul_of_nonneg_right ((hsub j).trans hmin) (hδ j)
  exact hlo.trans hup

theorem large_degree_cap {n : ℕ} {q : ℤ}
    (hq : 4≤q) (hn : (n:ℤ)=q*q+q-3)
    (A : Matrix (Fin n) (Fin n) Bool) (hA : rectangleFree A)
    (hD : deficit (c A) q≤3) :
    ∀ i,d A i≤q+2 := by
  intro i
  by_contra! hbad
  have hb := local_deficit_total A hA q i
  have hp := mul_le_mul_of_nonneg_right (show q+3≤d A i by omega) (show 0≤q-1 by omega)
  rw [hn] at hb
  have he : (q+3)*(q-1)=q*q+2*q-3 := by ring
  linarith

theorem deficit_forced {n : ℕ} {q : ℤ}
    (hq : 1≤q) (hn : (n:ℤ)=q*q+q-3)
    (A : Matrix (Fin n) (Fin n) Bool) (hA : rectangleFree A)
    (hex : ∃ i,q+1<d A i) :
    2≤deficit (c A) q := by
  obtain ⟨i,hi⟩:=hex
  have hp := mul_le_mul_of_nonneg_right (show q+2≤d A i by omega) (show 0≤q-1 by omega)
  have hb := local_deficit_total A hA q i
  rw [hn] at hb
  have he : (q+2)*(q-1)=q*q+q-2 := by ring
  linarith

theorem deficit_transpose {n : ℕ} (A : Matrix (Fin n) (Fin n) Bool) (q : ℤ) :
    deficit (d A.transpose) q=deficit (c A) q := by
  unfold deficit
  simp_rw [transpose_d]

theorem deficit_transpose_col {n : ℕ} (A : Matrix (Fin n) (Fin n) Bool) (q : ℤ) :
    deficit (c A.transpose) q=deficit (d A) q := by
  unfold deficit
  simp_rw [transpose_c]

/-- If every selected row is already high and their total excess over q+1
is at most 1, there can be at most one row of degree above q+1. -/
theorem large_count_one {n m : ℕ} {q : ℤ}
    (A : Matrix (Fin n) (Fin n) Bool) (H : Finset (Fin n)) (hc : H.card=m)
    (hHI : ∀ i∈H,q+1≤d A i)
    (hOut : ∀ j∈((univ : Finset (Fin n)) \ H),d A j≤q+1)
    (hT : (∑ i∈H,d A i)≤(q+1)*(m:ℤ)+1) :
    (univ.filter fun i=>q+1<d A i).card≤1 := by
  classical
  let L := (univ : Finset (Fin n)).filter fun i=>q+1<d A i
  have hLH : L⊆H := by
    intro i hi
    by_contra hbad
    have h := hOut i (mem_sdiff.mpr ⟨mem_univ _,hbad⟩)
    have := (mem_filter.mp hi).2
    omega
  have hsub : (L.card:ℤ)≤∑ i∈L,(d A i-(q+1)) := by
    rw [card_eq_sum_ones,Nat.cast_sum]
    apply sum_le_sum
    intro i hi
    have := (mem_filter.mp hi).2
    simp
    omega
  have hup : (∑ i∈L,(d A i-(q+1)))≤∑ i∈H,(d A i-(q+1)) :=
    sum_le_sum_of_subset_of_nonneg hLH (fun i hi _ => by have := hHI i hi; omega)
  have heq : (∑ i∈H,(d A i-(q+1))) = (∑ i∈H,d A i)-(m:ℤ)*(q+1) := by
    rw [sum_sub_distrib,sum_const,nsmul_eq_mul,hc]
  rw [heq] at hup
  have hn : (L.card:ℤ)≤1 := by linarith
  exact_mod_cast hn


end RectangleResearch

namespace RectangleResearch
open RectFreeCounting Finset

theorem signed_weight_upper {n m : ℕ} {q D K U : ℤ}
    (hq : 2≤q) (hDnon : 0≤D)
    (A : Matrix (Fin n) (Fin n) Bool)
    (H : Finset (Fin n))
    (hE : q*(n:ℤ)+(m:ℤ)≤E A)
    (hmax : ∀ j,c A j≤q+2)
    (hD : deficit (c A) q≤D)
    (hK : ((univ.filter fun j=>q+1<c A j).card:ℤ)≤K)
    (hU : ∑ j,max (a A H j-(q-3)-1) 0≤U) :
    (∑ j,a A H j*(q+1-c A j))≤(q-2)*((n:ℤ)-(m:ℤ)+K)+(D+1)*U := by
  classical
  let W (j : Fin n) := q+1-c A j
  let P (j : Fin n) := max (W j) 0
  let δ (j : Fin n) := max (a A H j-(q-3)-1) 0
  have hP (j : Fin n) : P j = W j+(if q+1<c A j then 1 else 0) := by
    unfold P W
    by_cases h : q+1<c A j
    · rw [if_pos h,max_eq_right (by omega)]
      have := hmax j
      omega
    · rw [if_neg h,max_eq_left (by omega)]
      ring
  have hcard : (∑ j:Fin n,(if q+1<c A j then (1:ℤ) else 0)) =
      ((univ.filter fun j=>q+1<c A j).card:ℤ) := by
    rw [←sum_filter,card_eq_sum_ones,Nat.cast_sum]
    simp
  have hPsum : (∑ j,P j)≤(n:ℤ)-(m:ℤ)+K := by
    simp_rw [hP]
    rw [sum_add_distrib,hcard]
    unfold W
    rw [sum_sub_distrib,sum_const,nsmul_eq_mul,card_univ,Fintype.card_fin,E_cols]
    linarith
  have hPmax (j : Fin n) : P j≤D+1 := by
    have hh:=deficit_point (c A) q j
    unfold P W
    apply max_le <;> omega
  have hpoint (j : Fin n) :
      a A H j*W j≤(q-2)*P j+(D+1)*δ j := by
    have h1 := mul_le_mul_of_nonneg_left (le_max_left (W j) 0) (a_nonneg A H j)
    have ha : a A H j≤q-2+δ j := by
      have h := le_max_left (a A H j-(q-3)-1) 0
      unfold δ
      omega
    have h2 := mul_le_mul_of_nonneg_right ha (le_max_right (W j) 0)
    have h3 := mul_le_mul_of_nonneg_left (hPmax j) (le_max_right (a A H j-(q-3)-1) 0)
    change a A H j*W j≤a A H j*P j at h1
    change a A H j*P j≤(q-2+δ j)*P j at h2
    change δ j*P j≤δ j*(D+1) at h3
    linarith [show (q-2+δ j)*P j=(q-2)*P j+δ j*P j by ring,
      mul_comm (δ j) (D+1)]
  have hs := sum_le_sum (fun j (_ : j∈(univ : Finset (Fin n)))=>hpoint j)
  rw [sum_add_distrib,←mul_sum,←mul_sum] at hs
  have h1:=mul_le_mul_of_nonneg_left hPsum (show 0≤q-2 by omega)
  have h2:=mul_le_mul_of_nonneg_left hU (show 0≤D+1 by omega)
  change (∑ j,δ j)≤U at hU
  change (D+1)*(∑ j,δ j)≤(D+1)*U at h2
  exact hs.trans (add_le_add h1 h2)

theorem small_cap_parameters {n m : ℕ} {q : ℤ}
    (hq : 4≤q) (hq6 : q≤6)
    (hn : (n:ℤ)=q*q+q-3) (hm : (m:ℤ)=q*q-3*q+3) :
    ∃ (b : ℕ) (u : ℤ),
      (q=4∧b=0∧u=3 ∨ (q=5∨q=6)∧b=1∧u=1) ∧
      (∀ A : Matrix (Fin n) (Fin n) Bool, rectangleFree A →
        (univ.filter fun i=>q<d A i).card≤m+b) := by
  have hcases : q=4∨q=5∨q=6 := by omega
  rcases hcases with he | he | he
  · subst q
    refine ⟨0,3,Or.inl ⟨rfl,rfl,rfl⟩,?_⟩
    intro A hA
    apply high_cap (k:=2) (by norm_num) A hA
    push_cast
    rw [hn,hm]
    norm_num
  · subst q
    refine ⟨1,1,Or.inr ⟨Or.inl rfl,rfl,rfl⟩,?_⟩
    intro A hA
    apply high_cap (k:=3) (by norm_num) A hA
    push_cast
    rw [hn,hm]
    norm_num
  · subst q
    refine ⟨1,1,Or.inr ⟨Or.inr rfl,rfl,rfl⟩,?_⟩
    intro A hA
    apply high_cap (k:=4) (by norm_num) A hA
    push_cast
    rw [hn,hm]
    norm_num

theorem top_four_bounded {n m : ℕ} {q u : ℤ}
    (hq : 4≤q) (hu : 0≤u)
    (hu' : 6<2*(q-3)*(u+1))
    (hn : (n:ℤ)=q*q+q-3) (hm : (m:ℤ)=q*q-3*q+3)
    (A : Matrix (Fin n) (Fin n) Bool) (hA : rectangleFree A)
    (H : Finset (Fin n)) (hc : H.card=m)
    (htop : ∀ i∈H,∀ j∉H,d A j≤d A i)
    (hE : q*(n:ℤ)+(m:ℤ)≤E A) :
    (q+1)*(m:ℤ)≤(∑ i∈H,d A i) ∧
    (∑ i∈H,d A i)≤(q+1)*(m:ℤ)+u ∧
    (∑ j,(a A H j-(q-3))*(a A H j-(q-3)-1))≤6 := by
  have hlo := top_weight_lower A H hc htop hE
  have hb := top_slack_four hn hm A hA H hc
  have hnon : 0≤∑ j,(a A H j-(q-3))*(a A H j-(q-3)-1) :=
    sum_nonneg fun j _=>int_mul_pred_nonneg _
  have hprod := mul_nonneg (show 0≤2*(q-3) by omega)
      (show 0≤(∑ i∈H,d A i)-(q+1)*(m:ℤ) by linarith)
  have hup : (∑ i∈H,d A i)≤(q+1)*(m:ℤ)+u := by
    by_contra! hh
    have hgap : u+1≤(∑ i∈H,d A i)-(q+1)*(m:ℤ) := by omega
    have hp:=mul_le_mul_of_nonneg_left hgap (show 0≤2*(q-3) by omega)
    linarith
  exact ⟨hlo,hup,by linarith⟩

theorem four_deletion_small_upper {n m : ℕ} {q : ℤ}
    (hq : 4≤q) (hq6 : q≤6)
    (hn : (n:ℤ)=q*q+q-3) (hm : (m:ℤ)=q*q-3*q+3)
    (A : Matrix (Fin n) (Fin n) Bool) (hA : rectangleFree A) :
    E A≤q*(n:ℤ)+(m:ℤ)-1 := by
  classical
  by_contra! hcontra
  have hE : q*(n:ℤ)+(m:ℤ)≤E A := by omega
  obtain ⟨b,u,hpar,hcap⟩:=small_cap_parameters hq hq6 hn hm
  have hcase : (q=4∧b=0∧u=3) ∨ (q=5∧b=1∧u=1) ∨ (q=6∧b=1∧u=1) := by
    rcases hpar with h | ⟨h,hb,hu⟩
    · exact Or.inl h
    · rcases h with h | h
      · exact Or.inr (Or.inl ⟨h,hb,hu⟩)
      · exact Or.inr (Or.inr ⟨h,hb,hu⟩)
  have hu : 0≤u := by omega
  have hu' : 6<2*(q-3)*(u+1) := by
    rcases hcase with ⟨rfl,_,rfl⟩ | ⟨rfl,_,rfl⟩ | ⟨rfl,_,rfl⟩ <;> norm_num
  have hmul : u<(m:ℤ) := by
    rw [hm]
    rcases hcase with ⟨rfl,_,rfl⟩ | ⟨rfl,_,rfl⟩ | ⟨rfl,_,rfl⟩ <;> norm_num
  have hl : u<(n:ℤ)-(m:ℤ) := by
    rw [hn,hm]
    rcases hcase with ⟨rfl,_,rfl⟩ | ⟨rfl,_,rfl⟩ | ⟨rfl,_,rfl⟩ <;> norm_num
  have hmn : m<n := by omega
  have hb : 3*((b:ℤ)+1)<2*q := by omega
  have hub : u+(b:ℤ)≤3 := by omega
  have hAT:=transpose_free A hA
  have hET : q*(n:ℤ)+(m:ℤ)≤E A.transpose := by rwa [transpose_E]
  obtain ⟨H,hH,htop⟩:=top_set (d A) m (by simpa using hmn.le)
  obtain ⟨J,hJ,htopJ⟩:=top_set (d A.transpose) m (by simpa using hmn.le)
  obtain ⟨hTlo,hThi,hdev⟩:=top_four_bounded hq hu hu' hn hm A hA H hH htop hE
  obtain ⟨hTloJ,hThiJ,hdevJ⟩:=top_four_bounded hq hu hu' hn hm A.transpose hAT J hJ htopJ hET
  have hNoLarge (X : Matrix (Fin n) (Fin n) Bool) (hX : rectangleFree X)
      (hEX : q*(n:ℤ)+(m:ℤ)≤E X)
      (L : Finset (Fin n)) (hL : L.card=m)
      (hTL : (q+1)*(m:ℤ)≤∑ i∈L,d X i)
      (hdevL : ∑ j,(a X L j-(q-3))*(a X L j-(q-3)-1)≤6)
      (hmax : ∀ j,c X j≤q+1) : False := by
    have hmaxT : ∀ j,d X.transpose j≤q+1 := by simpa only [transpose_d] using hmax
    have hcapT := hcap X.transpose (transpose_free X hX)
    have hdi := deficit_identity (d X.transpose) q hmaxT
    rw [E_rows,transpose_E,deficit_transpose] at hdi
    have hcapI : ((univ.filter fun j=>q<d X.transpose j).card:ℤ)≤(m:ℤ)+(b:ℤ) := by exact_mod_cast hcapT
    have hD : deficit (c X) q≤b := by linarith
    have hmin (j : Fin n) : q-(b:ℤ)≤c X j := by
      have := deficit_point (c X) q j
      omega
    exact near_four_weighted_contradiction (by omega) hn hm hb X hX L hL hTL hdevL hEX hmin hmax
  by_cases hcolmax : ∀ j,c A j≤q+1
  · exact hNoLarge A hA hE H hH hTlo hdev hcolmax
  by_cases hrowmax : ∀ i,d A i≤q+1
  · exact hNoLarge A.transpose hAT hET J hJ hTloJ hdevJ
      (fun i=>by rw [transpose_c]; exact hrowmax i)
  push Not at hrowmax hcolmax
  have hcolmaxT : ∃ j,q+1<d A.transpose j := by simpa only [transpose_d] using hcolmax
  have hDcolLo := deficit_forced (by omega) hn A hA hrowmax
  have hDrowLo := deficit_forced (by omega) hn A.transpose hAT hcolmaxT
  rw [deficit_transpose_col] at hDrowLo
  let R := (univ : Finset (Fin n)) \ H
  let S := (univ : Finset (Fin n)) \ J
  let k := (R.filter fun i=>q<d A i).card
  let kJ := (S.filter fun i=>q<d A.transpose i).card
  obtain ⟨hminH,hmaxR,hk,hallH,hDrow⟩:=relaxed_profile hu hmul hl A H hH htop hThi hE (hcap A hA)
  obtain ⟨hminJ,hmaxS,hkJ,hallJ,hDcol⟩:=relaxed_profile hu hmul hl A.transpose J hJ htopJ hThiJ hET
      (hcap A.transpose hAT)
  change k≤b at hk
  change kJ≤b at hkJ
  change 0<kJ→∀ i∈J,q+1≤d A.transpose i at hallJ
  change deficit (d A) q≤(∑ i∈H,d A i)-(q+1)*(m:ℤ)+(k:ℤ) at hDrow
  change deficit (d A.transpose) q≤(∑ i∈J,d A.transpose i)-(q+1)*(m:ℤ)+(kJ:ℤ) at hDcol
  rw [deficit_transpose] at hDcol
  have hkI : (k:ℤ)≤b := by exact_mod_cast hk
  have hkJI : (kJ:ℤ)≤b := by exact_mod_cast hkJ
  have hDrowUp : deficit (d A) q≤u+b := by linarith
  have hDcolUp : deficit (c A) q≤u+b := by linarith
  have hmaxC : ∀ j,c A j≤q+2 := by
    have h := large_degree_cap hq hn A.transpose hAT (by rw [deficit_transpose_col]; linarith)
    simpa only [transpose_d] using h
  let t := (∑ i∈H,d A i)-(q+1)*(m:ℤ)
  have htlo : 2-(b:ℤ)≤t := by dsimp [t]; linarith
  have htup : t≤u := by dsimp [t]; linarith
  have hslack := top_slack_four hn hm A hA H hH
  change 2*(q-3)*t+(∑ j,(a A H j-(q-3))*(a A H j-(q-3)-1))≤6 at hslack
  have hdelta : (∑ j,max (a A H j-(q-3)-1) 0)≤1 := by
    have hcoef : 4≤2*(q-3)*t := by
      rcases hcase with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ <;>
        norm_num at htlo ⊢ <;> omega
    have hsum : (∑ j,(a A H j-(q-3))*(a A H j-(q-3)-1))≤2 := by linarith
    have h := sum_max_excess (fun j=>a A H j-(q-3)) 2 hsum
    omega
  have hweighted := weighted_bound A hA H q
  rw [hH] at hweighted
  have hloEq : q*(∑ i∈H,d A i)-(m:ℤ)*((n:ℤ)-1)=4*(m:ℤ)+q*t := by
    unfold t
    rw [hn]
    ring
  rw [hloEq] at hweighted
  by_cases he : q=4
  · have hb0 : b=0 := by omega
    have hu3 : u=3 := by omega
    have hN : (n:ℤ)=17 := by rw [hn,he]; norm_num
    have hM : (m:ℤ)=7 := by rw [hm,he]; norm_num
    have hcnt := large_count_deficit (by omega) hn A.transpose hAT
    rw [deficit_transpose_col] at hcnt
    simp_rw [transpose_d] at hcnt
    have hK : ((univ.filter fun j=>q+1<c A j).card:ℤ)≤4 := by
      rw [he] at hcnt
      norm_num at hcnt
      have hh : deficit (d A) q≤3 := hDrowUp.trans hub
      rw [he] at hh ⊢
      norm_num at hh ⊢
      omega
    have hup := signed_weight_upper (by omega) (by norm_num : (0:ℤ)≤3) A H hE
        hmaxC (hDcolUp.trans hub) hK hdelta
    rw [he,hN,hM] at hup
    rw [he,hM] at hweighted
    norm_num at hup hweighted
    have ht : 2≤t := by rw [hb0] at htlo; simpa using htlo
    omega
  · have hb1 : b=1 := by omega
    have hu1 : u=1 := by omega
    have hDcol2 : deficit (c A) q≤2 := by rw [hb1,hu1] at hDcolUp; simpa using hDcolUp
    have hkjpos : 0<kJ := by
      by_contra! hh
      have hkj0 : kJ=0 := by omega
      rw [hkj0] at hDcol
      rw [hu1] at hThiJ
      norm_num at hDcol
      linarith
    have hKnat := large_count_one A.transpose J hJ (hallJ hkjpos) hmaxS (by simpa [hu1] using hThiJ)
    simp_rw [transpose_d] at hKnat
    have hK : ((univ.filter fun j=>q+1<c A j).card:ℤ)≤1 := by exact_mod_cast hKnat
    have hup := signed_weight_upper (by omega) (by norm_num : (0:ℤ)≤2) A H hE hmaxC hDcol2 hK hdelta
    have ht : 1≤t := by rw [hb1] at htlo; simpa using htlo
    have h56 : q=5∨q=6 := by omega
    rcases h56 with he5 | he6
    · have hN : (n:ℤ)=27 := by rw [hn,he5]; norm_num
      have hM : (m:ℤ)=13 := by rw [hm,he5]; norm_num
      rw [he5,hN,hM] at hup
      rw [he5,hM] at hweighted
      norm_num at hup hweighted
      omega
    · have hN : (n:ℤ)=39 := by rw [hn,he6]; norm_num
      have hM : (m:ℤ)=21 := by rw [hm,he6]; norm_num
      rw [he6,hN,hM] at hup
      rw [he6,hM] at hweighted
      norm_num at hup hweighted
      omega


end RectangleResearch

namespace RectangleResearch
open RectFreeCounting Finset

theorem nine_profiles (A : Matrix (Fin 9) (Fin 9) Bool) (hA : rectangleFree A)
    (hE : 30≤E A) : (∀ j,c A j=3∨c A j=4) ∧ E A=30 := by
  have h := deviation_bound A hA univ 3
  change 2*3*(∑ i,d A i)-(9:ℤ)*3*(3+1)+
      (∑ j,(c A j-3)*(c A j-3-1))≤
      ((univ : Finset (Fin 9)).card:ℤ)*(((univ : Finset (Fin 9)).card:ℤ)-1) at h
  rw [E_rows,card_univ,Fintype.card_fin] at h
  norm_num at h
  have hnon (j : Fin 9) : 0≤(c A j-3)*(c A j-3-1) := int_mul_pred_nonneg _
  have hsum : 0≤∑ j,(c A j-3)*(c A j-3-1) := sum_nonneg fun j _=>hnon j
  have hzero : (∑ j,(c A j-3)*(c A j-3-1))=0 := by linarith
  have hs := (sum_eq_zero_iff_of_nonneg (fun j _=>hnon j)).mp hzero
  refine ⟨?_,by linarith⟩
  intro j
  have he := hs j (mem_univ j)
  rcases mul_eq_zero.mp he with hh | hh <;> omega

theorem nine_upper (A : Matrix (Fin 9) (Fin 9) Bool) (hA : rectangleFree A) :
    E A≤29 := by
  classical
  by_contra! hh
  have hE : 30≤E A := by omega
  obtain ⟨hc,hEeq⟩ := nine_profiles A hA hE
  have hAT := transpose_free A hA
  have hET : 30≤E A.transpose := by rwa [transpose_E]
  obtain ⟨hrow,_⟩ := nine_profiles A.transpose hAT hET
  have hr (i : Fin 9) : d A i=3∨d A i=4 := by
    have h := hrow i
    rwa [transpose_c] at h
  let H : Finset (Fin 9) := univ.filter fun i=>3<d A i
  have hmax (i : Fin 9) : d A i≤3+1 := by have := hr i; omega
  have hD : deficit (d A) 3=0 := by
    unfold deficit
    apply sum_eq_zero
    intro i _
    apply max_eq_right
    have := hr i
    omega
  have hid := deficit_identity (d A) 3 hmax
  rw [E_rows,hEeq,hD] at hid
  change (30:ℤ)=3*(9:ℤ)+(H.card:ℤ)-0 at hid
  have hH : H.card=3 := by omega
  have hT : (∑ i∈H,d A i)=12 := by
    calc
      _=∑ _i∈H,(4:ℤ) := by
        apply sum_congr rfl
        intro i hi
        have h := (mem_filter.mp hi).2
        have := hr i
        omega
      _=_ := by rw [sum_const,nsmul_eq_mul,hH]; norm_num
  have hdev := top_slack_four (q:=3) (by norm_num : (9:ℤ)=3*3+3-3)
      (by norm_num : (3:ℤ)=3*3-3*3+3) A hA H hH
  norm_num at hdev
  exact near_four_weighted_contradiction (q:=3) (b:=0) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) A hA H hH
    (by rw [hT]; norm_num) hdev (by norm_num; exact hE)
    (fun j=>by have := hc j; omega) (fun j=>by have := hc j; omega)

theorem three_upper (A : Matrix (Fin 3) (Fin 3) Bool) (hA : rectangleFree A) :
    E A≤6 := by
  have h := RectFreeCounting.tangent_bound (k:=2) (by decide : 1≤3) A hA
  change 4*numberOfOnes A≤24 at h
  unfold E
  omega

theorem four_deletion_upper_all {n m : ℕ} {q : ℤ}
    (hq : 2≤q) (hn : (n:ℤ)=q*q+q-3) (hm : (m:ℤ)=q*q-3*q+3)
    (A : Matrix (Fin n) (Fin n) Bool) (hA : rectangleFree A) :
    E A≤q^3+2*q^2-6*q+2 := by
  by_cases h7 : 7≤q
  · exact four_deletion_polynomial_ge_seven h7 hn hm A hA
  by_cases h4 : 4≤q
  · have hb := four_deletion_small_upper h4 (by omega) hn hm A hA
    rw [hn,hm] at hb
    convert hb using 1 <;> ring
  have hcases : q=2∨q=3 := by omega
  rcases hcases with hq2 | hq3
  · subst q
    have hN : n=3 := by norm_num at hn; omega
    subst n
    norm_num
    exact three_upper A hA
  · subst q
    have hN : n=9 := by norm_num at hn; omega
    subst n
    norm_num
    exact nine_upper A hA

end RectangleResearch

namespace ProjectiveBoard
open RectFreeCounting RectangleResearch

/-- The exact Zarankiewicz value and the symmetric extremizer at n=q²+q−3. -/
theorem four_deletion_exact_finite_field (K : Type*) [Field K] [Fintype K] :
    let q := Fintype.card K
    let n := q*q+q-3
    ∃ B : Matrix (Fin n) (Fin n) Bool, B.IsSymm ∧ rectangleFree B ∧
      E B=(q:ℤ)^3+2*(q:ℤ)^2-6*(q:ℤ)+2 ∧
      ∀ A : Matrix (Fin n) (Fin n) Bool, rectangleFree A → numberOfOnes A ≤ numberOfOnes B := by
  let q := Fintype.card K
  let n := q*q+q-3
  let m := q*q+3-3*q
  have hqn : 2≤q := Fintype.one_lt_card
  have hqi : 2≤(q:ℤ) := by exact_mod_cast hqn
  have hqn' : 3≤q*q+q := by nlinarith
  have hqm : 3*q≤q*q+3 := by
    have h := Nat.mul_le_mul_left q hqn
    by_cases h2 : q=2
    · simp [h2]
    · have h3 : 3≤q := by omega
      nlinarith [Nat.mul_le_mul_left q h3]
  have hn : (n:ℤ)=(q:ℤ)*(q:ℤ)+(q:ℤ)-3 := by
    dsimp [n]
    rw [Nat.cast_sub hqn',Nat.cast_add,Nat.cast_mul]
    norm_num
  have hm : (m:ℤ)=(q:ℤ)*(q:ℤ)-3*(q:ℤ)+3 := by
    dsimp [m]
    rw [Nat.cast_sub hqm,Nat.cast_add,Nat.cast_mul,Nat.cast_mul]
    norm_num
    ring
  obtain ⟨B,hs,hf,hE⟩ := four_deletion_lower K
  refine ⟨B,hs,hf,hE,?_⟩
  intro A hA
  have hub := four_deletion_upper_all hqi hn hm A hA
  rw [← hE] at hub
  exact Int.ofNat_le.mp hub

/-- Full 2013 Dybizbański–Dzido–Radziszowski conjecture 5, with symmetry. -/
theorem four_deletion_exact_prime_power (p k : ℕ) (hp : p.Prime) (hk : k≠0) :
    let q := p^k
    let n := q*q+q-3
    ∃ B : Matrix (Fin n) (Fin n) Bool, B.IsSymm ∧ rectangleFree B ∧
      E B=(q:ℤ)^3+2*(q:ℤ)^2-6*(q:ℤ)+2 ∧
      ∀ A : Matrix (Fin n) (Fin n) Bool, rectangleFree A → numberOfOnes A ≤ numberOfOnes B := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fintype (GaloisField p k) := Fintype.ofFinite _
  have hc : Fintype.card (GaloisField p k)=p^k := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card p k hk
  let C : ℕ → Prop := fun q =>
    let n:=q*q+q-3
    ∃ B : Matrix (Fin n) (Fin n) Bool, B.IsSymm ∧ rectangleFree B ∧
      E B=(q:ℤ)^3+2*(q:ℤ)^2-6*(q:ℤ)+2 ∧
      ∀ A : Matrix (Fin n) (Fin n) Bool, rectangleFree A → numberOfOnes A ≤ numberOfOnes B
  have h : C (Fintype.card (GaloisField p k)) := four_deletion_exact_finite_field (GaloisField p k)
  rw [hc] at h
  exact h


end ProjectiveBoard

namespace RectangleResearch
open RectFreeCounting Finset

theorem peel_from_gap {n m : ℕ} {q k : ℤ} (hk : 0≤k)
    (hmn : m≤n)
    (gap : (m:ℤ)*((m:ℤ)-1)+(n:ℤ)*k*(k+1)<2*k*(q+1)*(m:ℤ))
    (A : Matrix (Fin n) (Fin n) Bool) (hA : rectangleFree A) :
    E A≤q*(n:ℤ)+(m:ℤ)-1 := by
  by_contra! hh
  have hE : q*(n:ℤ)+(m:ℤ)≤E A := by omega
  obtain ⟨H,hH,htop⟩:=top_set (d A) m (by simpa using hmn)
  have hlo:=top_weight_lower A H hH htop hE
  have hdev:=deviation_bound A hA H k
  rw [hH] at hdev
  have hp:=mul_le_mul_of_nonneg_left hlo (show 0≤2*k by omega)
  have hnon : 0≤∑ j,(a A H j-k)*(a A H j-k-1) :=
    sum_nonneg fun j _=>int_mul_pred_nonneg _
  linarith

theorem two_deletion_upper {n m : ℕ} {q : ℤ} (hq : 2≤q)
    (hn : (n:ℤ)=q*q+q-1) (hm : (m:ℤ)=q*q-q+1)
    (A : Matrix (Fin n) (Fin n) Bool) (hA : rectangleFree A) :
    E A≤q^3+2*q^2-2*q := by
  have hgap : (m:ℤ)*((m:ℤ)-1)+(n:ℤ)*(q-1)*(q-1+1)<2*(q-1)*(q+1)*(m:ℤ) := by
    rw [hn,hm]
    have heq : 2*(q-1)*(q+1)*(q*q-q+1) -
        ((q*q-q+1)*(q*q-q+1-1)+(q*q+q-1)*(q-1)*(q-1+1))=2*(q-1) := by ring
    linarith
  have hb := peel_from_gap (k:=q-1) (by omega) (by omega) hgap A hA
  rw [hn,hm] at hb
  convert hb using 1 <;> ring

theorem ten_profiles (A : Matrix (Fin 10) (Fin 10) Bool) (hA : rectangleFree A)
    (hE : 35≤E A) : (∀ j,c A j=3∨c A j=4) ∧ E A=35 := by
  have h:=deviation_bound A hA univ 3
  change 2*3*(∑ i,d A i)-(10:ℤ)*3*(3+1)+
      (∑ j,(c A j-3)*(c A j-3-1))≤
      ((univ : Finset (Fin 10)).card:ℤ)*(((univ : Finset (Fin 10)).card:ℤ)-1) at h
  rw [E_rows,card_univ,Fintype.card_fin] at h
  norm_num at h
  have hnon (j : Fin 10) : 0≤(c A j-3)*(c A j-3-1) := int_mul_pred_nonneg _
  have hsum : 0≤∑ j,(c A j-3)*(c A j-3-1) := sum_nonneg fun j _=>hnon j
  have hzero : (∑ j,(c A j-3)*(c A j-3-1))=0 := by linarith
  have hs := (sum_eq_zero_iff_of_nonneg (fun j _=>hnon j)).mp hzero
  refine ⟨?_,by linarith⟩
  intro j
  have he:=hs j (mem_univ j)
  rcases mul_eq_zero.mp he with hh | hh <;> omega

theorem ten_upper (A : Matrix (Fin 10) (Fin 10) Bool) (hA : rectangleFree A) :
    E A≤34 := by
  classical
  by_contra! hh
  have hE : 35≤E A := by omega
  obtain ⟨hc,hEeq⟩:=ten_profiles A hA hE
  have hAT:=transpose_free A hA
  have hET : 35≤E A.transpose := by rwa [transpose_E]
  obtain ⟨hrow,_⟩:=ten_profiles A.transpose hAT hET
  have hr (i : Fin 10) : d A i=3∨d A i=4 := by
    have h:=hrow i
    rwa [transpose_c] at h
  let H : Finset (Fin 10) := univ.filter fun i=>3<d A i
  have hmax (i : Fin 10) : d A i≤3+1 := by have := hr i; omega
  have hD : deficit (d A) 3=0 := by
    unfold deficit
    apply sum_eq_zero
    intro i _
    apply max_eq_right
    have := hr i
    omega
  have hid:=deficit_identity (d A) 3 hmax
  rw [E_rows,hEeq,hD] at hid
  change (35:ℤ)=3*(10:ℤ)+(H.card:ℤ)-0 at hid
  have hH : H.card=5 := by omega
  have hT : (∑ i∈H,d A i)=20 := by
    calc
      _=∑ _i∈H,(4:ℤ) := by
        apply sum_congr rfl
        intro i hi
        have h:=(mem_filter.mp hi).2
        have:=hr i
        omega
      _=_ := by rw [sum_const,nsmul_eq_mul,hH]; norm_num
  let W (j : Fin 10) := 4-c A j
  have hW (j : Fin 10) : W j=0∨W j=1 := by unfold W; have:=hc j; omega
  have hsumW : (∑ j,W j)=5 := by
    unfold W
    rw [sum_sub_distrib,sum_const,nsmul_eq_mul,card_univ,Fintype.card_fin,E_cols,hEeq]
    norm_num
  have hWeighted := weighted_bound A hA H 3
  change 3*(∑ i∈H,d A i)-(H.card:ℤ)*(10-1)≤∑ j,a A H j*W j at hWeighted
  rw [hT,hH] at hWeighted
  norm_num at hWeighted
  have hpoint (j : Fin 10) : 4*(a A H j*W j)-6*W j≤a A H j*(a A H j-1) := by
    rcases hW j with he | he
    · rw [he]
      simpa using int_mul_pred_nonneg (a A H j)
    · rw [he]
      have h:=int_mul_pred_nonneg (a A H j-2)
      linarith [show (a A H j-2)*(a A H j-2-1)=a A H j*(a A H j-1)-4*a A H j+6 by ring]
  have hsum:=sum_le_sum (fun j (_ : j∈(univ : Finset (Fin 10)))=>hpoint j)
  rw [sum_sub_distrib,←mul_sum,←mul_sum,hsumW] at hsum
  have hPair:=int_pair_bound A hA H
  rw [hH] at hPair
  norm_num at hPair
  linarith

theorem four_upper (A : Matrix (Fin 4) (Fin 4) Bool) (hA : rectangleFree A) :
    E A≤9 := by
  have h:=RectFreeCounting.tangent_bound (k:=2) (by decide : 1≤4) A hA
  change 4*numberOfOnes A≤36 at h
  unfold E
  omega

theorem three_deletion_upper {n m : ℕ} {q : ℤ} (hq : 2≤q)
    (hn : (n:ℤ)=q*q+q-2) (hm : (m:ℤ)=q*q-2*q+2)
    (A : Matrix (Fin n) (Fin n) Bool) (hA : rectangleFree A) :
    E A≤q^3+2*q^2-4*q+1 := by
  by_cases hlarge : 4≤q
  · have hgap : (m:ℤ)*((m:ℤ)-1)+(n:ℤ)*(q-2)*(q-2+1)<2*(q-2)*(q+1)*(m:ℤ) := by
      rw [hn,hm]
      have heq : 2*(q-2)*(q+1)*(q*q-2*q+2)-
          ((q*q-2*q+2)*(q*q-2*q+2-1)+(q*q+q-2)*(q-2)*(q-2+1))=2*(q-3) := by ring
      linarith
    have hb:=peel_from_gap (k:=q-2) (by omega) (by omega) hgap A hA
    rw [hn,hm] at hb
    convert hb using 1 <;> ring
  have hcases : q=2∨q=3 := by omega
  rcases hcases with he | he
  · subst q
    have hN : n=4 := by norm_num at hn; omega
    subst n
    norm_num
    exact four_upper A hA
  · subst q
    have hN : n=10 := by norm_num at hn; omega
    subst n
    norm_num
    exact ten_upper A hA

end RectangleResearch

namespace ProjectiveBoard
open RectFreeCounting RectangleResearch Finset

theorem two_deleted_points {K : Type*} [Field K] [Fintype K] :
    ∃ D : Finset (Pt K), D.card=2 ∧ (∑ i∈D,∑ j∈D,si i j)=3 := by
  classical
  let p3 : Pt K := .inr none
  let p4 : Pt K := .inl (1,0)
  let D : Finset (Pt K) := {p3,p4}
  have h34 : p3 ∉ ({p4} : Finset (Pt K)) := by simp [p3,p4]
  refine ⟨D,?_,?_⟩
  · simp [D,card_insert_of_notMem h34]
  · simp [D,sum_insert h34,si,dotNeg,x,y,z,p3,p4]

theorem three_deleted_points {K : Type*} [Field K] [Fintype K] :
    ∃ D : Finset (Pt K), D.card=3 ∧ (∑ i∈D,∑ j∈D,si i j)=6 := by
  classical
  let p1 : Pt K := .inl (0,0)
  let p2 : Pt K := .inr (.some 0)
  let p3 : Pt K := .inr none
  let D : Finset (Pt K) := {p1,p2,p3}
  have h23 : p2 ∉ ({p3} : Finset (Pt K)) := by simp [p2,p3]
  have h123 : p1 ∉ ({p2,p3} : Finset (Pt K)) := by simp [p1,p2,p3]
  refine ⟨D,?_,?_⟩
  · simp [D,card_insert_of_notMem h123,card_insert_of_notMem h23]
  · simp [D,sum_insert h123,sum_insert h23,si,dotNeg,x,y,z,p1,p2,p3]

theorem two_deletion_exact_finite_field (K : Type*) [Field K] [Fintype K] :
    let q:=Fintype.card K
    let n:=q*q+q-1
    ∃ B : Matrix (Fin n) (Fin n) Bool, B.IsSymm ∧ rectangleFree B ∧
      E B=(q:ℤ)^3+2*(q:ℤ)^2-2*(q:ℤ) ∧
      ∀ A : Matrix (Fin n) (Fin n) Bool, rectangleFree A→numberOfOnes A≤numberOfOnes B := by
  let q:=Fintype.card K
  let n:=q*q+q-1
  let m:=q*q+1-q
  have hq : 2≤q := Fintype.one_lt_card
  have hqi : 2≤(q:ℤ) := by exact_mod_cast hq
  obtain ⟨D,hD,h3⟩:=two_deleted_points (K:=K)
  have hn' : n=q*q+q+1-D.card := by rw [hD]; dsimp [n]; omega
  obtain ⟨B,hs,hf,hE⟩:=principal_projective D n hn'
  have hE' : E B=(q:ℤ)^3+2*(q:ℤ)^2-2*(q:ℤ) := by
    rw [hE,hD,h3]
    push_cast
    ring
  refine ⟨B,hs,hf,hE',?_⟩
  intro A hA
  have hn : (n:ℤ)=(q:ℤ)*(q:ℤ)+(q:ℤ)-1 := by
    dsimp [n]
    rw [Nat.cast_sub (by omega : 1≤q*q+q),Nat.cast_add,Nat.cast_mul]
    norm_num
  have hm : (m:ℤ)=(q:ℤ)*(q:ℤ)-(q:ℤ)+1 := by
    dsimp [m]
    rw [Nat.cast_sub (by nlinarith [Nat.mul_le_mul_left q hq] : q≤q*q+1),Nat.cast_add,Nat.cast_mul]
    norm_num
    ring
  have hb:=two_deletion_upper hqi hn hm A hA
  rw [←hE'] at hb
  exact Int.ofNat_le.mp hb

theorem three_deletion_exact_finite_field (K : Type*) [Field K] [Fintype K] :
    let q:=Fintype.card K
    let n:=q*q+q-2
    ∃ B : Matrix (Fin n) (Fin n) Bool, B.IsSymm ∧ rectangleFree B ∧
      E B=(q:ℤ)^3+2*(q:ℤ)^2-4*(q:ℤ)+1 ∧
      ∀ A : Matrix (Fin n) (Fin n) Bool, rectangleFree A→numberOfOnes A≤numberOfOnes B := by
  let q:=Fintype.card K
  let n:=q*q+q-2
  let m:=q*q+2-2*q
  have hq : 2≤q := Fintype.one_lt_card
  have hqi : 2≤(q:ℤ) := by exact_mod_cast hq
  obtain ⟨D,hD,h6⟩:=three_deleted_points (K:=K)
  have hn' : n=q*q+q+1-D.card := by rw [hD]; dsimp [n]; omega
  obtain ⟨B,hs,hf,hE⟩:=principal_projective D n hn'
  have hE' : E B=(q:ℤ)^3+2*(q:ℤ)^2-4*(q:ℤ)+1 := by
    rw [hE,hD,h6]
    push_cast
    ring
  refine ⟨B,hs,hf,hE',?_⟩
  intro A hA
  have hn : (n:ℤ)=(q:ℤ)*(q:ℤ)+(q:ℤ)-2 := by
    dsimp [n]
    rw [Nat.cast_sub (by omega : 2≤q*q+q),Nat.cast_add,Nat.cast_mul]
    norm_num
  have hm : (m:ℤ)=(q:ℤ)*(q:ℤ)-2*(q:ℤ)+2 := by
    dsimp [m]
    rw [Nat.cast_sub (by nlinarith [Nat.mul_le_mul_left q hq] : 2*q≤q*q+2),Nat.cast_add,Nat.cast_mul,Nat.cast_mul]
    norm_num
    ring
  have hb:=three_deletion_upper hqi hn hm A hA
  rw [←hE'] at hb
  exact Int.ofNat_le.mp hb


end ProjectiveBoard

namespace ProjectiveBoard
open RectFreeCounting RectangleResearch Finset

def optimalAt (n : ℕ) : Prop :=
  ∃ B : Matrix (Fin n) (Fin n) Bool, B.IsSymm ∧ rectangleFree B ∧
    ∀ A : Matrix (Fin n) (Fin n) Bool, rectangleFree A → numberOfOnes A≤numberOfOnes B

theorem zero_deletion_optimal (K : Type*) [Field K] [Fintype K] :
    optimalAt (Fintype.card K*Fintype.card K+Fintype.card K+1) := by
  let q:=Fintype.card K
  let n:=q*q+q+1
  obtain ⟨B,hs,hf,hE⟩:=principal_projective (∅ : Finset (Pt K)) n (by simp [n,q])
  have hW : E B=(n:ℤ)*((q:ℤ)+1) := by
    rw [hE]
    simp [n,q]
  refine ⟨B,hs,hf,?_⟩
  intro A hA
  have hb := projective_order_bound (q:=q) (rfl : n=q*q+q+1) A hA
  have hb' : E A≤(n:ℤ)*((q:ℤ)+1) := by unfold E; exact_mod_cast hb
  rw [←hW] at hb'
  exact Int.ofNat_le.mp hb'

theorem one_deleted_point {K : Type*} [Field K] [Fintype K] :
    ∃ D : Finset (Pt K), D.card=1 ∧ (∑ i∈D,∑ j∈D,si i j)=1 := by
  classical
  let v : Pt K := .inl (1,0)
  refine ⟨{v},by simp,?_⟩
  rw [sum_singleton,sum_singleton]
  simp [v,si,dotNeg,x,y,z]

theorem one_deletion_optimal (K : Type*) [Field K] [Fintype K] :
    optimalAt (Fintype.card K*Fintype.card K+Fintype.card K) := by
  let q:=Fintype.card K
  let n:=q*q+q
  obtain ⟨D,hD,h1⟩:=one_deleted_point (K:=K)
  have hn : n=q*q+q+1-D.card := by rw [hD]; rfl
  obtain ⟨B,hs,hf,hE⟩:=principal_projective D n hn
  have hW : E B=(q:ℤ)*(q:ℤ)*(q:ℤ)+2*(q:ℤ)*(q:ℤ) := by
    rw [hE,hD,h1]
    push_cast
    ring
  refine ⟨B,hs,hf,?_⟩
  intro A hA
  have hq : 0<q := Fintype.card_pos
  have hb:=projective_minus_one_bound hq (rfl : n=q*q+q) A hA
  have hb' : E A≤(q:ℤ)*(q:ℤ)*(q:ℤ)+2*(q:ℤ)*(q:ℤ) := by unfold E; exact_mod_cast hb
  rw [←hW] at hb'
  exact Int.ofNat_le.mp hb'

theorem two_deletion_optimal (K : Type*) [Field K] [Fintype K] :
    optimalAt (Fintype.card K*Fintype.card K+Fintype.card K-1) := by
  obtain ⟨B,hs,hf,_,hm⟩:=two_deletion_exact_finite_field K
  exact ⟨B,hs,hf,hm⟩

theorem three_deletion_optimal (K : Type*) [Field K] [Fintype K] :
    optimalAt (Fintype.card K*Fintype.card K+Fintype.card K-2) := by
  obtain ⟨B,hs,hf,_,hm⟩:=three_deletion_exact_finite_field K
  exact ⟨B,hs,hf,hm⟩

theorem four_deletion_optimal (K : Type*) [Field K] [Fintype K] :
    optimalAt (Fintype.card K*Fintype.card K+Fintype.card K-3) := by
  obtain ⟨B,hs,hf,_,hm⟩:=four_deletion_exact_finite_field K
  exact ⟨B,hs,hf,hm⟩

theorem five_families_finite_field (K : Type*) [Field K] [Fintype K]
    (h : ℕ) (hh : h≤4) :
    optimalAt (Fintype.card K*Fintype.card K+Fintype.card K+1-h) := by
  let q:=Fintype.card K
  change optimalAt (q*q+q+1-h)
  have hcase : h=0∨h=1∨h=2∨h=3∨h=4 := by omega
  rcases hcase with rfl | rfl | rfl | rfl | rfl
  · rw [show q*q+q+1-0=q*q+q+1 by omega]
    exact zero_deletion_optimal K
  · rw [show q*q+q+1-1=q*q+q by omega]
    exact one_deletion_optimal K
  · rw [show q*q+q+1-2=q*q+q-1 by omega]
    exact two_deletion_optimal K
  · rw [show q*q+q+1-3=q*q+q-2 by omega]
    exact three_deletion_optimal K
  · rw [show q*q+q+1-4=q*q+q-3 by omega]
    exact four_deletion_optimal K

theorem five_families_prime_power (p k h : ℕ) (hp : p.Prime) (hk : 0<k) (hh : h≤4) :
    optimalAt (p^k*p^k+p^k+1-h) := by
  classical
  letI : Fact p.Prime:=⟨hp⟩
  letI : Fintype (GaloisField p k):=Fintype.ofFinite _
  have hc : Fintype.card (GaloisField p k)=p^k := by
    rw [←Nat.card_eq_fintype_card]
    exact GaloisField.card p k (by omega)
  have ht := five_families_finite_field (GaloisField p k) h hh
  rw [hc] at ht
  exact ht


end ProjectiveBoard

/-- Proof of the entire first reduction step. -/
theorem OMA.solution : OMA.R_oeis_a072567_R1.H1 := by
  intro p k h hp hk hh
  exact ProjectiveBoard.five_families_prime_power p k h hp hk hh
