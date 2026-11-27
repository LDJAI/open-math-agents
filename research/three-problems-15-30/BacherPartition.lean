import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Powerset
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.CharP.Two
import Mathlib.Logic.Relation
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Finset.Preimage

/-!
# Computing the product of all spanning-tree bipartitions

Roland Bacher, MathOverflow question 38547 (September 2010).
Formal development for the LDJAI research repository.
Use Lean 4.33.1 with the Mathlib dependency pinned by formal-conjectures
at commit 9097e2f90e66. Run `lake env lean BacherPartition.lean`.

The main executable result is `Bacher.partitionAlgorithm_spec`. Its input
is a finite edge list with one distinguished vertex as root.
`Bacher.product_as_tree_distance` relates the result to the sum of distances
over the actual spanning subtrees of the input simple graph.
-/


namespace TreePartition
noncomputable section
open Finset Matrix

variable {n : ℕ} {E R : Type*} [Fintype E] [LinearOrder E] [CommRing R]

private def expansionTerm (A : Matrix (Fin n) E R) (B : Matrix E (Fin n) R)
    (f : Fin n → E) : R :=
  (∏ i, A i (f i)) * (B.submatrix f id).det

private theorem expandDet (A : Matrix (Fin n) E R) (B : Matrix E (Fin n) R) :
    (A * B).det = ∑ f, expansionTerm A B f := by
  classical
  let D := (Matrix.detRowAlternating : (Fin n → R) [⋀^Fin n]→ₗ[R] R).toMultilinearMap
  let g (i : Fin n) (e : E) : Fin n → R := A i e • B e
  have hM : (A * B) = fun i => ∑ e, g i e := by
    ext i j
    simp [Matrix.mul_apply, g, Finset.sum_apply]
  change D (A * B) = _
  rw [hM, D.map_sum g]
  apply Finset.sum_congr rfl
  intro f _
  exact Matrix.det_mul_column (fun i => A i (f i)) (B.submatrix f id)

private def mask (A : Matrix (Fin n) E R) (s : Finset E) : Matrix (Fin n) E R :=
  fun i e => if e ∈ s then A i e else 0

private theorem maskTerm (A : Matrix (Fin n) E R) (B : Matrix E (Fin n) R)
    (s : Finset E) (f : Fin n → E) :
    expansionTerm (mask A s) B f = if ∀ i, f i ∈ s then expansionTerm A B f else 0 := by
  classical
  by_cases h : ∀ i, f i ∈ s
  · simp [expansionTerm, mask, h]
  · obtain ⟨i, hi⟩ := not_forall.mp h
    rw [if_neg h]
    unfold expansionTerm
    have hz : (∏ j, mask A s j (f j)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by simp [mask, hi])
    simp [hz]

private theorem maskMul (A : Matrix (Fin n) E R) (B : Matrix E (Fin n) R)
    (s : Finset E) (hs : s.card = n) :
    mask A s * B = A.submatrix id (s.orderEmbOfFin hs) * B.submatrix (s.orderEmbOfFin hs) id := by
  classical
  ext i j
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, id_eq, mask, ite_mul, zero_mul]
  let g (e : E) := A i e * B e j
  change (∑ e : E, if e ∈ s then g e else 0) = ∑ k : Fin n, g (s.orderEmbOfFin hs k)
  rw [← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
  calc ∑ e ∈ s, g e = ∑ e : s, g e := (s.sum_attach g).symm
       _ = _ := ((s.orderIsoOfFin hs).toEquiv.sum_comp fun e : s => g e).symm

/-- Cauchy–Binet, with minors indexed by increasing enumerations of edge subsets. -/
theorem cauchyBinet (A : Matrix (Fin n) E R) (B : Matrix E (Fin n) R) :
    (A*B).det = ∑ s : {s : Finset E // s.card = n},
      (A.submatrix id (s.1.orderEmbOfFin s.2)).det *
      (B.submatrix (s.1.orderEmbOfFin s.2) id).det := by
  classical
  let SS := {s : Finset E // s.card = n}
  calc
    (A * B).det = ∑ f, expansionTerm A B f := expandDet _ _
    _ = ∑ s : SS, ∑ f, expansionTerm (mask A s.1) B f := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro f _
      simp_rw [maskTerm]
      by_cases hin : Function.Injective f
      · let s : {s : Finset E // s.card = n} :=
          ⟨Finset.univ.image f, by simp [Finset.card_image_of_injective _ hin]⟩
        symm
        rw [Finset.sum_eq_single s]
        · rw [if_pos (fun i => Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)]
        · intro t _ hts
          apply if_neg
          intro h
          apply hts
          apply Subtype.ext
          symm
          apply Finset.eq_of_subset_of_card_le
          · intro e he
            obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp he
            exact h i
          · exact t.2.trans s.2.symm |>.le
        · simp
      · have h : ∃ i j, f i = f j ∧ i ≠ j := by
          by_contra! ha
          exact hin fun i j hij => ha i j hij
        obtain ⟨i,j,hij,hne⟩ := h
        have hz : (B.submatrix f id).det = 0 :=
          Matrix.det_zero_of_row_eq hne (by funext k; simp [Matrix.submatrix_apply, hij])
        simp [expansionTerm, hz]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s _
      rw [← expandDet (mask A s.1) B, maskMul _ _ _ s.2, Matrix.det_mul]

end
end TreePartition


namespace Bacher

open Matrix
open scoped Matrix

variable {n m : ℕ}

/-- Ground the vertex `none` and use the remaining vertex coordinates as labels. -/
def grounded (x : Fin n → ZMod 2) : Option (Fin n) → ZMod 2
  | none => 0
  | some i => x i

/-- The reduced incidence matrix counts the two endpoints modulo two. -/
def incidence (u v : Fin m → Option (Fin n)) : Matrix (Fin n) (Fin m) (ZMod 2) :=
  fun i j => (if u j = some i then 1 else 0) + (if v j = some i then 1 else 0)

lemma sum_endpoint (x : Fin n → ZMod 2) (p : Option (Fin n)) :
    (∑ i, x i * (if p = some i then (1 : ZMod 2) else 0)) = grounded x p := by
  cases p with
  | none => simp [grounded]
  | some j => simp [grounded, mul_ite]

theorem vecMul_incidence (u v : Fin m → Option (Fin n)) (x : Fin n → ZMod 2) (j : Fin m) :
    (x ᵥ* incidence u v) j = grounded x (u j) + grounded x (v j) := by
  simp only [Matrix.vecMul, dotProduct, incidence, mul_add, Finset.sum_add_distrib, sum_endpoint]

def Adjacent (u v : Fin m → Option (Fin n)) (p q : Option (Fin n)) : Prop :=
  ∃ j, u j = p ∧ v j = q

/-- Reachability along edges in either direction. -/
def Connected (u v : Fin m → Option (Fin n)) : Prop :=
  ∀ p, Relation.EqvGen (Adjacent u v) none p

lemma grounded_eq_of_reach {u v : Fin m → Option (Fin n)} {x : Fin n → ZMod 2}
    (h : ∀ j, grounded x (u j) = grounded x (v j)) {p q : Option (Fin n)}
    (hpq : Relation.EqvGen (Adjacent u v) p q) : grounded x p = grounded x q := by
  induction hpq with
  | rel _ _ hh => obtain ⟨j,rfl,rfl⟩ := hh; exact h j
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ hp hq => exact hp.trans hq

theorem det_ne_zero_iff_connected (u v : Fin n → Option (Fin n)) :
    (incidence u v).det ≠ 0 ↔ Connected u v := by
  classical
  constructor
  · intro hdet
    let R := Relation.EqvGen (Adjacent u v)
    let x : Fin n → ZMod 2 := fun i => if R none (some i) then 0 else 1
    have hroot : R none none := Relation.EqvGen.refl _
    have hval (p : Option (Fin n)) : grounded x p = if R none p then 0 else 1 := by
      cases p <;> simp [grounded, x, hroot]
    have hz : x ᵥ* incidence u v = 0 := by
      funext j
      have he : R (u j) (v j) := Relation.EqvGen.rel _ _ ⟨j, rfl, rfl⟩
      have same : R none (u j) ↔ R none (v j) :=
        ⟨fun h => Relation.EqvGen.trans _ _ _ h he,
         fun h => Relation.EqvGen.trans _ _ _ h (Relation.EqvGen.symm _ _ he)⟩
      rw [vecMul_incidence, hval, hval, if_congr same rfl rfl]
      exact CharTwo.add_self_eq_zero _
    have hzero : x = 0 := by
      by_contra hnon
      exact hdet (Matrix.exists_vecMul_eq_zero_iff.mp ⟨x,hnon,hz⟩)
    intro p
    cases p with
    | none => exact hroot
    | some i =>
      by_contra hbad
      have hxi := congrFun hzero i
      have hi : ¬R none (some i) := hbad
      simp [x, hi] at hxi
  · intro hc hdet
    obtain ⟨x,hx,hzero⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet
    have he (j : Fin n) : grounded x (u j) = grounded x (v j) := by
      have h := congrFun hzero j
      rw [vecMul_incidence] at h
      exact (eq_neg_of_add_eq_zero_left h).trans (ZMod.neg_eq_self_mod_two _)
    apply hx
    funext i
    exact (grounded_eq_of_reach he (hc (some i))).symm

end Bacher


namespace Bacher
open Matrix
open scoped Matrix
variable {n m : ℕ}

/-- Labels on the two ends of every edge sum to one. Zero is the root label. -/
def ProperColor (u v : Fin m → Option (Fin n)) (x : Fin n → ZMod 2) : Prop :=
  ∀ j, grounded x (u j) + grounded x (v j) = 1

/-- Select an actual proper coloring when one exists. -/
noncomputable def color (u v : Fin m → Option (Fin n)) : Fin n → ZMod 2 := by
  classical
  exact if h : ∃ x, ProperColor u v x then Classical.choose h else 0

theorem matrix_color (u v : Fin m → Option (Fin n)) (x : Fin n → ZMod 2) :
    ProperColor u v x ↔ (incidence u v).transpose *ᵥ x = fun _ => 1 := by
  rw [Matrix.mulVec_transpose]
  constructor
  · intro h; funext e; exact (vecMul_incidence u v x e).trans (h e)
  · intro h e; exact (vecMul_incidence u v x e).symm.trans (congrFun h e)

theorem one_of_nz {z : ZMod 2} (h : z ≠ 0) : z = 1 := by
  exact (show ∀ a : ZMod 2, a ≠ 0 → a = 1 by decide) z h

theorem color_eq_cramer (u v : Fin n → Option (Fin n)) (hc : Connected u v) :
    ProperColor u v (color u v) ∧
      color u v = (incidence u v).transpose.cramer (fun _ => 1) := by
  classical
  let A := (incidence u v).transpose
  have hd : A.det = 1 := by
    dsimp [A]; rw [Matrix.det_transpose]
    exact one_of_nz ((det_ne_zero_iff_connected u v).mpr hc)
  have hcand : ProperColor u v (A.cramer fun _ => 1) := by
    apply (matrix_color u v _).mpr
    change A *ᵥ A.cramer _ = _
    rw [Matrix.mulVec_cramer, hd, one_smul]
  have hex : ∃ x, ProperColor u v x := ⟨_, hcand⟩
  have hcol : ProperColor u v (color u v) := by
    simp only [color, dif_pos hex]
    exact Classical.choose_spec hex
  refine ⟨hcol, ?_⟩
  have hu : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).mpr (hd ▸ isUnit_one)
  apply (Matrix.mulVec_injective_iff_isUnit.mpr hu)
  exact ((matrix_color u v _).mp hcol).trans ((matrix_color u v _).mp hcand).symm

abbrev Selection (n m : ℕ) := {s : Finset (Fin m) // s.card = n}

def edgeAt (s : Selection n m) (i : Fin n) : Fin m := s.1.orderEmbOfFin s.2 i

/-- Sum the binary colors of all connected n-edge subsets on n+1 vertices.
These are exactly the spanning trees. The zero coordinate at the root fixes the
global sign of each factor. -/
noncomputable def productBit (u v : Fin m → Option (Fin n)) (j : Fin n) : ZMod 2 := by
  classical
  exact ∑ s : Selection n m, if Connected (u ∘ edgeAt s) (v ∘ edgeAt s)
    then color (u ∘ edgeAt s) (v ∘ edgeAt s) j else 0

def testMatrix (u v : Fin m → Option (Fin n)) (j : Fin n) :
    Matrix (Fin m) (Fin n) (ZMod 2) :=
  (incidence u v).transpose.updateCol j (fun _ => 1)

lemma summand (u v : Fin m → Option (Fin n)) (s : Selection n m) (j : Fin n)
    [Decidable (Connected (u ∘ edgeAt s) (v ∘ edgeAt s))] :
    ((incidence u v).submatrix id (edgeAt s)).det *
      ((testMatrix u v j).submatrix (edgeAt s) id).det =
    if Connected (u ∘ edgeAt s) (v ∘ edgeAt s) then color (u ∘ edgeAt s) (v ∘ edgeAt s) j else 0 := by
  let a := u ∘ edgeAt s
  let b := v ∘ edgeAt s
  have hmin : (incidence u v).submatrix id (edgeAt s) = incidence a b := rfl
  have htest : (testMatrix u v j).submatrix (edgeAt s) id =
      (incidence a b).transpose.updateCol j (fun _ => 1) := by
    ext e i
    by_cases he : i=j <;> simp [testMatrix, Matrix.updateCol_apply, Matrix.submatrix, he, incidence, a, b]
  rw [hmin, htest]
  by_cases h : Connected a b
  · rw [if_pos h, one_of_nz ((det_ne_zero_iff_connected _ _).mpr h), one_mul, (color_eq_cramer _ _ h).2]
    rfl
  · have hz : (incidence a b).det = 0 := by
      by_contra hh
      exact h ((det_ne_zero_iff_connected _ _).mp hh)
    rw [hz, zero_mul, if_neg h]

end Bacher


namespace Bacher
open Matrix
open scoped Matrix
variable {n m : ℕ}

/-- One determinant of order n per requested color bit, on n+1 vertices. -/
theorem partition_formula (u v : Fin m → Option (Fin n)) (j : Fin n) :
    ((incidence u v) * (testMatrix u v j)).det = productBit u v j := by
  classical
  rw [TreePartition.cauchyBinet, productBit]
  apply Finset.sum_congr rfl
  intro s _
  exact summand u v s j

/-- Writing the same algorithm directly on the grounded Laplacian. -/
theorem laplacian_formula (u v : Fin m → Option (Fin n)) (j : Fin n) :
    (((incidence u v) * (incidence u v).transpose).updateCol j
      ((incidence u v) *ᵥ fun _ => 1)).det = productBit u v j := by
  rw [← partition_formula]
  congr 1
  ext i k
  by_cases hk : k = j
  · subst k
    simp [testMatrix, Matrix.mul_apply, Matrix.updateCol_apply, Matrix.mulVec, dotProduct]
  · simp [testMatrix, Matrix.mul_apply, Matrix.updateCol_apply, hk, Ne.symm hk]

end Bacher


namespace TreeParity
open Matrix
open scoped Matrix
variable {n m : Type} [Fintype n] [Fintype m] [DecidableEq n]

lemma bit_sq (z : ZMod 2) : z * z = z := by
  fin_cases z <;> rfl

lemma gram_diag (B : Matrix n m (ZMod 2)) : (B * Bᵀ).diag = B *ᵥ (fun _ => 1) := by
  funext i
  simp only [diag_apply, mul_apply, transpose_apply, bit_sq, mulVec, dotProduct, mul_one]

/-- The vector of Cramer determinants used by the spanning-tree algorithm collapses
to zero when the number of spanning trees is even. -/
theorem cramer_gram (B : Matrix n m (ZMod 2)) :
    cramer (B * Bᵀ) (B *ᵥ fun _ => 1) = (B * Bᵀ).det • (B * Bᵀ).adjugate.diag := by
  let L := B * Bᵀ
  let A := L.adjugate
  have hL : Lᵀ = L := by simp [L,transpose_mul]
  have hA : Aᵀ = A := by simp [A,adjugate_transpose,hL]
  change cramer L (B *ᵥ fun _ => 1) = L.det • A.diag
  rw [cramer_eq_adjugate_mulVec, mulVec_mulVec]
  change (A * B) *ᵥ (fun _ => 1) = L.det • A.diag
  rw [← gram_diag, transpose_mul, hA, Matrix.mul_assoc, ← Matrix.mul_assoc B,
    ← Matrix.mul_assoc A]
  change ((L.adjugate * L) * A).diag = _
  rw [adjugate_mul, Matrix.smul_mul, Matrix.one_mul, diag_smul]

theorem cramer_singular (B : Matrix n m (ZMod 2)) (h : (B * Bᵀ).det = 0) :
    cramer (B * Bᵀ) (B *ᵥ fun _ => 1) = 0 := by rw [cramer_gram,h,zero_smul]

theorem solve_nonsingular (B : Matrix n m (ZMod 2)) (h : (B * Bᵀ).det ≠ 0) :
    (B * Bᵀ) *ᵥ cramer (B * Bᵀ) (B *ᵥ fun _ => 1) = B *ᵥ fun _ => 1 := by
  have hOne : (B * Bᵀ).det = 1 := by
    generalize hz : (B * Bᵀ).det = z at h ⊢
    fin_cases z <;> first | rfl | exact (h rfl).elim
  rw [Matrix.mulVec_cramer, hOne, one_smul]

end TreeParity


namespace Bacher
open Matrix
open scoped Matrix
variable {n m : ℕ}

abbrev groundedLap (u v : Fin m → Option (Fin n)) :=
  (incidence u v) * (incidence u v)ᵀ

/-- Every spanning-tree aggregate is determined by the grounded Laplacian.
In particular the singular case is identically zero. -/
theorem fast_partition (u v : Fin m → Option (Fin n)) :
    productBit u v = (groundedLap u v).det • (groundedLap u v).adjugate.diag := by
  rw [← TreeParity.cramer_gram]
  funext j
  exact (laplacian_formula u v j).symm

theorem singular_trivial (u v : Fin m → Option (Fin n)) (h : (groundedLap u v).det = 0) :
    productBit u v = 0 := by rw [fast_partition, h, zero_smul]

/-- One binary linear system determines all k output coordinates at once. -/
theorem nonsingular_eq_solve (u v : Fin m → Option (Fin n))
    (h : (groundedLap u v).det ≠ 0) (x : Fin n → ZMod 2) :
    x = productBit u v ↔ (groundedLap u v) *ᵥ x = (incidence u v) *ᵥ (fun _ => 1) := by
  have hp : productBit u v = (groundedLap u v).cramer ((incidence u v) *ᵥ fun _ => 1) := by
    funext j; exact (laplacian_formula u v j).symm
  have he := TreeParity.solve_nonsingular (incidence u v) h
  change (groundedLap u v) *ᵥ (groundedLap u v).cramer _ = _ at he
  rw [hp]
  constructor
  · intro hx; rw [hx]; exact he
  · intro hx
    apply (Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr h)))
    exact hx.trans he.symm

/-- Number of labeled spanning trees, enumerated as connected n-edge selections. -/
noncomputable def treeCount (u v : Fin m → Option (Fin n)) : ℕ := by
  classical
  exact (Finset.univ.filter fun s : Selection n m =>
    Connected (u ∘ edgeAt s) (v ∘ edgeAt s)).card

theorem parity_tree_count (u v : Fin m → Option (Fin n)) :
    (groundedLap u v).det = ((treeCount u v : ℕ) : ZMod 2) := by
  classical
  rw [groundedLap, TreePartition.cauchyBinet, treeCount, ← Finset.sum_boole]
  apply Finset.sum_congr rfl
  intro s _
  let a := u ∘ edgeAt s
  let b := v ∘ edgeAt s
  let W := incidence a b
  change W.det * W.transpose.det = if Connected a b then 1 else 0
  rw [Matrix.det_transpose, TreeParity.bit_sq]
  by_cases h : Connected a b
  · rw [if_pos h]; exact one_of_nz ((det_ne_zero_iff_connected _ _).mpr h)
  · rw [if_neg h]
    by_contra hh
    exact h ((det_ne_zero_iff_connected _ _).mp hh)

theorem even_tree_count_trivial (u v : Fin m → Option (Fin n)) (h : Even (treeCount u v)) :
    productBit u v = 0 := by
  apply singular_trivial
  rw [parity_tree_count]
  obtain ⟨k, hk⟩ := h
  rw [hk, Nat.cast_add]
  exact CharTwo.add_self_eq_zero _

end Bacher


namespace Bacher.Elimination
open Matrix

abbrev Bit := ZMod 2
abbrev Square (n : ℕ) := Matrix (Fin n) (Fin n) Bit

/-- Evaluate all entries once and store the result in vectors before the next pivot step. -/
def tabulate {n : ℕ} (f : Square n) : Square n :=
  let rows := Vector.ofFn (fun i : Fin n => Vector.ofFn (f i))
  fun i j => rows[i.val][j.val]

@[simp] theorem tabulate_eq {n : ℕ} (f : Square n) : tabulate f = f := by
  ext i j
  simp [tabulate]

def firstPivot {n : ℕ} (A : Square n) (j : Fin n) : Option (Fin n) :=
  (List.finRange n).find? (fun i => decide (A i j = 1))

def residual {n : ℕ} (A : Square (n+1)) (p : Fin (n+1)) : Square n :=
  fun i j => A (p.succAbove i) j.succ + A (p.succAbove i) 0 * A p j.succ

/-- The second component charges one bit comparison per possible pivot, one AND and
one XOR per entry of the smaller table. It bounds arithmetic work including a full scan. -/
def solve : (n : ℕ) → Square n → Bit × ℕ
  | 0, _ => (1, 0)
  | n+1, A =>
    match firstPivot A 0 with
    | none => (0, n+1)
    | some p =>
      let r := solve n (tabulate (residual A p))
      (r.1, r.2 + (n+1) + 2*n*n)

theorem det_residual {n : ℕ} (A : Square (n+1)) (p : Fin (n+1))
    (hp : A p 0 = 1) : A.det = (residual A p).det := by
  let c (i : Fin (n+1)) : Bit := if i = p then 0 else A i 0
  let T : Square (n+1) := fun i j => A i j + c i * A p j
  have hd : T.det = A.det :=
    Matrix.det_eq_of_forall_row_eq_smul_add_const c p (by simp [c]) (fun _ _ => rfl)
  have h0 : T p 0 = 1 := by simp [T, c, hp]
  have hz (i) (hi : i ≠ p) : T i 0 = 0 := by
    simp [T, c, hi, hp, CharTwo.add_self_eq_zero]
  have hR : T.submatrix p.succAbove Fin.succ = residual A p := by
    ext i j
    change A (p.succAbove i) j.succ + c (p.succAbove i) * A p j.succ = _
    simp [c, residual, Fin.succAbove_ne]
  rw [← hd, Matrix.det_succ_column_zero, Finset.sum_eq_single p]
  · rw [h0, hR, ZMod.neg_eq_self_mod_two]
    simp
  · intro i _ hi
    simp [hz i hi]
  · simp

theorem all_zero {n : ℕ} (A : Square (n+1)) (h : firstPivot A 0 = none) :
    A.det = 0 := by
  apply Matrix.det_eq_zero_of_column_eq_zero 0
  intro i
  have hn : A i 0 ≠ 1 := by
    have ha := List.find?_eq_none.mp h i (by simp)
    simpa using ha
  generalize he : A i 0 = b at hn ⊢
  fin_cases b <;> first | rfl | exact (hn rfl).elim

/-- Correctness and worst-case bit-arithmetic bound for a deterministic tabulated solver. -/
theorem solve_spec (n : ℕ) (A : Square n) :
    (solve n A).1 = A.det ∧ (solve n A).2 ≤ 3*n^3 := by
  induction n with
  | zero => simp [solve]
  | succ n ih =>
    cases he : firstPivot A 0 with
    | none =>
      simp only [solve, he]
      refine ⟨(all_zero A he).symm, ?_⟩
      nlinarith only [Nat.zero_le n, Nat.zero_le (n*n), Nat.zero_le (n*n*n)]
    | some p =>
      have hp : A p 0 = 1 := by
        simpa using (List.find?_some he)
      obtain ⟨hval, hcost⟩ := ih (tabulate (residual A p))
      simp only [solve, he]
      refine ⟨hval.trans ?_, ?_⟩
      · rw [tabulate_eq, ← det_residual A p hp]
      · nlinarith only [hcost, Nat.zero_le n, Nat.zero_le (n*n)]

end Bacher.Elimination


namespace Bacher.Elimination
open Matrix
open scoped Matrix

abbrev Column (n : ℕ) := Fin n → Bit

def cacheVec {n} (v : Column n) : Column n :=
  let a := Vector.ofFn v
  fun i => a[i.val]

@[simp] theorem cacheVec_eq {n} (v : Column n) : cacheVec v = v := by
  funext i
  simp [cacheVec]

def reduceVec {n} (A : Square (n+1)) (b : Column (n+1)) (p : Fin (n+1)) : Column n :=
  fun i => b (p.succAbove i) + A (p.succAbove i) 0 * b p

def tailSum {n} (A : Square (n+1)) (i : Fin (n+1)) (y : Column n) : Bit :=
  ∑ j, A i j.succ * y j

def recover {n} (A : Square (n+1)) (b : Column (n+1)) (p : Fin (n+1)) (y : Column n) :
    Column (n+1) :=
  Fin.cons (b p + tailSum A p y) y

/-- The charge counts pivot comparisons, field additions and multiplications with
one slot per operation. A stage may charge unused slots if it terminates early. -/
def linearSolve : (n : ℕ) → Square n → Column n → Option (Column n) × ℕ
  | 0, _, _ => (some (fun _ => 0), 0)
  | n+1, A, b =>
    match firstPivot A 0 with
    | none => (none, n+1)
    | some p =>
      let r := linearSolve n (tabulate (residual A p)) (cacheVec (reduceVec A b p))
      (r.1.map (fun y => cacheVec (recover A b p y)), r.2 + 2*n*n + 5*n + 2)

private theorem recover_correct {n} (A : Square (n+1)) (b : Column (n+1)) (p : Fin (n+1))
    (y : Column n) (hp : A p 0 = 1) (hy : residual A p *ᵥ y = reduceVec A b p) :
    A *ᵥ recover A b p y = b := by
  funext i
  change (∑ j, A i j * recover A b p y j) = b i
  rw [Fin.sum_univ_succ]
  change A i 0 * (b p + tailSum A p y) + tailSum A i y = b i
  by_cases h : i = p
  · subst i
    rw [hp, one_mul, add_assoc, CharTwo.add_self_eq_zero, add_zero]
  · obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq h
    have he := congrFun hy j
    change (∑ k, (A (p.succAbove j) k.succ + A (p.succAbove j) 0 * A p k.succ) * y k) =
      b (p.succAbove j) + A (p.succAbove j) 0 * b p at he
    rw [hj] at he
    simp only [add_mul, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum] at he
    change tailSum A i y + A i 0 * tailSum A p y = b i + A i 0 * b p at he
    calc A i 0 * (b p + tailSum A p y) + tailSum A i y
          = A i 0 * b p + (tailSum A i y + A i 0 * tailSum A p y) := by ring
         _ = A i 0 * b p + (b i + A i 0 * b p) := by rw [he]
         _ = b i := by rw [add_left_comm, CharTwo.add_self_eq_zero, add_zero]

theorem linearSolve_spec (n : ℕ) (A : Square n) (b : Column n) :
    (match (linearSolve n A b).1 with
     | none => A.det = 0
     | some x => A.det ≠ 0 ∧ A *ᵥ x = b) ∧
    (linearSolve n A b).2 ≤ 7*n^3 := by
  induction n with
  | zero =>
    simp only [linearSolve, Matrix.det_fin_zero, ne_eq, one_ne_zero, not_false_eq_true, true_and]
    exact ⟨Subsingleton.elim _ _, by decide⟩
  | succ n ih =>
    cases he : firstPivot A 0 with
    | none =>
      simp only [linearSolve, he]
      refine ⟨all_zero A he, ?_⟩
      nlinarith only [Nat.zero_le n, Nat.zero_le (n*n), Nat.zero_le (n*n*n)]
    | some p =>
      have hp : A p 0 = 1 := by simpa using (List.find?_some he)
      have hd := det_residual A p hp
      have ⟨hval,hcost⟩ := ih (tabulate (residual A p)) (cacheVec (reduceVec A b p))
      simp only [linearSolve, he]
      constructor
      · cases hr : (linearSolve n (tabulate (residual A p)) (cacheVec (reduceVec A b p))).1 with
        | none =>
          rw [hr] at hval
          simpa only [Option.map_none, hd, tabulate_eq] using hval
        | some y =>
          rw [hr] at hval
          simp only [tabulate_eq, cacheVec_eq] at hval
          simpa only [Option.map_some, cacheVec_eq] using
            And.intro (hd.trans_ne hval.1) (recover_correct A b p y hp hval.2)
      · nlinarith only [hcost, Nat.zero_le n, Nat.zero_le (n*n)]

/-- One execution returns every color simultaneously, returning zero on breakdown. -/
def colors {n m} (u v : Fin m → Option (Fin n)) : Column n :=
  let A := incidence u v
  let L := tabulate (A * A.transpose)
  let b := cacheVec (A *ᵥ (fun _ => 1))
  (linearSolve n L b).1.getD (fun _ => 0)

theorem colors_correct {n m} (u v : Fin m → Option (Fin n)) : colors u v = productBit u v := by
  let L := groundedLap u v
  let b := incidence u v *ᵥ fun _ => 1
  have h := (linearSolve_spec n L b).1
  simp only [colors, tabulate_eq, cacheVec_eq]
  change (linearSolve n L b).1.getD _ = _
  cases hr : (linearSolve n L b).1 with
  | none =>
    rw [hr] at h
    exact (singular_trivial _ _ h).symm
  | some x =>
    rw [hr] at h
    exact (nonsingular_eq_solve u v h.1 x).mpr h.2

end Bacher.Elimination


namespace Bacher.Input
open Matrix
open scoped Matrix
abbrev Bit := ZMod 2

/-- Dot product by an explicit bounded loop, returning its bit-operation charge. -/
def inner : (m : ℕ) → (Fin m → Bit) → (Fin m → Bit) → Bit × ℕ
  | 0, _, _ => (0, 0)
  | m+1, a, b =>
    let z := inner m (fun i => a i.castSucc) (fun i => b i.castSucc)
    (z.1 + a (Fin.last m) * b (Fin.last m), z.2+2)

theorem inner_spec {m : ℕ} (a b : Fin m → Bit) :
    inner m a b = (∑ i, a i * b i, 2*m) := by
  induction m with
  | zero => simp [inner]
  | succ m ih => simp [inner, ih, Fin.sum_univ_castSucc, Nat.mul_succ]

/-- Materialize each incidence entry once, including endpoint and root comparisons. -/
def columns {n m : ℕ} (u v : Fin m → Option (Fin n)) : Matrix (Fin n) (Fin m) Bit :=
  let rows := Vector.ofFn fun i : Fin n => Vector.ofFn (incidence u v i)
  fun i e => rows[i.val][e.val]

theorem columns_eq {n m : ℕ} (u v : Fin m → Option (Fin n)) : columns u v = incidence u v := by
  ext; simp [columns]

structure Data (n : ℕ) where
  matrix : Elimination.Square n
  rhs : Fin n → Bit
  cost : ℕ

/-- Assemble the matrix and right-hand side using only endpoint tests and bit arithmetic.
The cost charges three operations per incidence entry, two per dot-product term. -/
def prepare {n m : ℕ} (u v : Fin m → Option (Fin n)) : Data n :=
  let B := columns u v
  let entries := Vector.ofFn fun i : Fin n =>
    Vector.ofFn fun j : Fin n => inner m (B i) (B j)
  let right := Vector.ofFn fun i : Fin n => inner m (B i) (fun _ => 1)
  ⟨fun i j => (entries[i.val][j.val]).1, fun i => (right[i.val]).1,
    3*n*m + (∑ i : Fin n, ∑ j : Fin n, (entries[i.val][j.val]).2) +
      ∑ i : Fin n, (right[i.val]).2⟩

theorem prepare_spec {n m : ℕ} (u v : Fin m → Option (Fin n)) :
    (prepare u v).matrix = (incidence u v)*(incidence u v).transpose ∧
    (prepare u v).rhs = (incidence u v) *ᵥ (fun _ => 1) ∧
    (prepare u v).cost = 3*n*m + n*(n*(2*m)) + n*(2*m) := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j; simp [prepare, columns_eq, inner_spec, Matrix.mul_apply]
  · funext i; simp [prepare, columns_eq, inner_spec, Matrix.mulVec, dotProduct]
  · simp [prepare, inner_spec, Finset.sum_const, Nat.smul_one_eq_cast]

end Bacher.Input


namespace Bacher
open Matrix
open scoped Matrix

/-- Uniform endpoint-list algorithm. The first component is the color of every
nonroot vertex. The second accounts for the loop work specified by Input.prepare
and Elimination.linearSolve. The distinguished root has color zero. -/
def partitionAlgorithm {n m : ℕ} (u v : Fin m → Option (Fin n)) :
    (Fin n → ZMod 2) × ℕ :=
  let data := Input.prepare u v
  let solve := Elimination.linearSolve n data.matrix data.rhs
  (solve.1.getD (fun _ => 0), data.cost + solve.2)

theorem partitionAlgorithm_spec {n m : ℕ} (u v : Fin m → Option (Fin n)) :
    (partitionAlgorithm u v).1 = productBit u v ∧
    (partitionAlgorithm u v).2 ≤ 3*n*m + n*(n*(2*m)) + n*(2*m) + 7*n^3 := by
  obtain ⟨hmat,hrhs,hc⟩ := Input.prepare_spec u v
  dsimp only [partitionAlgorithm]
  rw [hmat, hrhs, hc]
  constructor
  · simpa only [Elimination.colors, Elimination.tabulate_eq, Elimination.cacheVec_eq] using
      Elimination.colors_correct u v
  · exact Nat.add_le_add_left (Elimination.linearSolve_spec n _ _).2 _

end Bacher


namespace Bacher
variable {n m : ℕ}

/-- The ordinary simple graph obtained from indexed endpoints, ignoring orientation. -/
def endpointGraph (u v : Fin m → Option (Fin n)) := SimpleGraph.fromRel (Adjacent u v)

theorem reachable_iff_generated (u v : Fin m → Option (Fin n)) (p q : Option (Fin n)) :
    (endpointGraph u v).Reachable p q ↔ Relation.EqvGen (Adjacent u v) p q := by
  constructor
  · rintro ⟨walk⟩
    induction walk with
    | nil => exact .refl _
    | cons edge _ ih =>
      rcases edge.2 with h | h
      · exact .trans _ _ _ (.rel _ _ h) ih
      · exact .trans _ _ _ (.symm _ _ (.rel _ _ h)) ih
  · intro h
    induction h with
    | rel p q h =>
      by_cases he : p=q
      · subst q; exact .refl _
      · exact SimpleGraph.Adj.reachable (G := endpointGraph u v) ⟨he, Or.inl h⟩
    | refl p => exact .refl _
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ hp hq => exact hp.trans hq

theorem graph_connected (u v : Fin m → Option (Fin n)) :
    (endpointGraph u v).Connected ↔ Connected u v := by
  refine ⟨fun h p => (reachable_iff_generated u v none p).mp (h none p), ?_⟩
  intro h
  have hr (p) := (reachable_iff_generated u v none p).mpr (h p)
  exact ⟨fun p q => (hr p).symm.trans (hr q)⟩

theorem graph_isTree_of_card (u v : Fin n → Option (Fin n))
    (hcard : Nat.card (endpointGraph u v).edgeSet = n) :
    (endpointGraph u v).IsTree ↔ Connected u v := by
  rw [SimpleGraph.isTree_iff_connected_and_card, graph_connected, hcard]
  simp [Nat.card_eq_fintype_card]

lemma Walk_length_parity {α : Type} {G : SimpleGraph α} (c : α → ZMod 2)
    (hc : ∀ {a b}, G.Adj a b → c a + c b = 1) {p q : α} (w : G.Walk p q) :
    c p + c q = (w.length : ZMod 2) := by
  induction w with
  | nil => simp [CharTwo.add_self_eq_zero]
  | @cons a b z edge tail ih =>
    calc
      c a + c z = (c a + c b) + (c b + c z) := by
        rw [add_assoc (c a), ← add_assoc (c b), CharTwo.add_self_eq_zero, zero_add]
      _ = _ := by rw [hc edge, ih]; simp [add_comm]

theorem color_eq_distance (u v : Fin n → Option (Fin n)) (hc : Connected u v)
    (i : Fin n) : color u v i = ((endpointGraph u v).dist none (some i) : ZMod 2) := by
  let c := grounded (color u v)
  have prop := (color_eq_cramer _ _ hc).1
  have he {a b} (hab : (endpointGraph u v).Adj a b) : c a + c b = 1 := by
    rcases hab.2 with ⟨j,rfl,rfl⟩ | ⟨j,rfl,rfl⟩
    · exact prop j
    · rw [add_comm]; exact prop j
  obtain ⟨w,hw⟩ := ((graph_connected _ _).mpr hc).exists_walk_length_eq_dist none (some i)
  simpa [c, grounded, hw] using Walk_length_parity c he w

open scoped Sym2

def edgeOf (u v : Fin m → Option (Fin n)) (i : Fin m) := s(u i, v i)

lemma graph_edge_set (u v : Fin m → Option (Fin n)) (hn : ∀ j, u j ≠ v j) :
    (endpointGraph u v).edgeSet = Set.range (edgeOf u v) := by
  ext e
  induction e using Sym2.ind with | h p q =>
    rw [SimpleGraph.mem_edgeSet]
    constructor
    · intro hpq
      rcases hpq.2 with ⟨i,rfl,rfl⟩ | ⟨i,rfl,rfl⟩
      · exact ⟨i, rfl⟩
      · exact ⟨i, Sym2.eq_swap⟩
    · rintro ⟨i, hi⟩
      have hh : (u i, v i) = (p,q) ∨ (u i, v i) = (p,q).swap :=
        Sym2.mk_eq_mk_iff.mp hi
      rcases hh with hh | hh
      · obtain ⟨hp,hq⟩ := Prod.mk.inj hh
        exact ⟨hp ▸ hq ▸ hn i, Or.inl ⟨i,hp,hq⟩⟩
      · obtain ⟨hp,hq⟩ := Prod.mk.inj hh
        exact ⟨fun h => hn i (hp.trans (h.symm.trans hq.symm)), Or.inr ⟨i,hp,hq⟩⟩

theorem graph_edge_card (u v : Fin m → Option (Fin n)) (hn : ∀ j, u j ≠ v j)
    (hi : Function.Injective (edgeOf u v)) : Nat.card (endpointGraph u v).edgeSet = m := by
  rw [graph_edge_set _ _ hn, ← Nat.card_congr (Equiv.ofInjective _ hi), Nat.card_fin]

theorem simple_spanning_tree_iff (u v : Fin n → Option (Fin n)) (hn : ∀ j, u j ≠ v j)
    (hi : Function.Injective (edgeOf u v)) : (endpointGraph u v).IsTree ↔ Connected u v :=
  graph_isTree_of_card _ _ (graph_edge_card _ _ hn hi)

end Bacher


namespace Bacher
variable {n m : ℕ}
open scoped BigOperators Sym2 Classical

def selectedGraph (u v : Fin m → Option (Fin n)) (s : Selection n m) :=
  endpointGraph (u ∘ edgeAt s) (v ∘ edgeAt s)

lemma selected_edges (u v : Fin m → Option (Fin n)) (hn : ∀ j, u j ≠ v j) (s : Selection n m) :
    (selectedGraph u v s).edgeSet = edgeOf u v '' (s.1 : Set (Fin m)) := by
  rw [selectedGraph, graph_edge_set (u ∘ edgeAt s) (v ∘ edgeAt s) (fun j => hn (edgeAt s j))]
  change Set.range (edgeOf u v ∘ edgeAt s) = _
  rw [Set.range_comp]
  change (edgeOf u v) '' (Set.range (s.1.orderEmbOfFin s.2)) = _
  rw [Finset.range_orderEmbOfFin]

lemma selected_injective (u v : Fin m → Option (Fin n)) (hn : ∀ j, u j ≠ v j)
    (hi : Function.Injective (edgeOf u v)) : Function.Injective (selectedGraph u v) := by
  intro s t h
  have hh := congrArg SimpleGraph.edgeSet h
  rw [selected_edges _ _ hn, selected_edges _ _ hn] at hh
  exact Subtype.ext (Finset.coe_injective (Set.image_injective.mpr hi hh))

lemma selected_tree (u v : Fin m → Option (Fin n)) (hn : ∀ j, u j ≠ v j)
    (hi : Function.Injective (edgeOf u v)) (s : Selection n m) :
    (selectedGraph u v s).IsTree ↔ Connected (u ∘ edgeAt s) (v ∘ edgeAt s) := by
  apply simple_spanning_tree_iff _ _ (fun _ => hn _)
  exact hi.comp (s.1.orderEmbOfFin s.2).injective

lemma selected_le (u v : Fin m → Option (Fin n)) (hn : ∀ j, u j ≠ v j) (s : Selection n m) :
    selectedGraph u v s ≤ endpointGraph u v := by
  rw [← SimpleGraph.edgeSet_subset_edgeSet,selected_edges _ _ hn,graph_edge_set _ _ hn]
  exact Set.image_subset_range _ _

lemma select_tree (u v : Fin m → Option (Fin n)) (hn : ∀ j, u j ≠ v j)
    (hi : Function.Injective (edgeOf u v)) (H : SimpleGraph (Option (Fin n)))
    (hle : H ≤ endpointGraph u v) (ht : H.IsTree) :
    ∃ s : Selection n m, selectedGraph u v s = H := by
  classical
  let f := edgeOf u v
  have hsub : (H.edgeFinset : Set _) ⊆ Set.range f := by
    rw [SimpleGraph.coe_edgeFinset, ← graph_edge_set u v hn]
    exact SimpleGraph.edgeSet_subset_edgeSet.mpr hle
  have him : (H.edgeFinset.preimage f hi.injOn).image f = H.edgeFinset := by
    rw [Finset.image_preimage]
    exact Finset.filter_eq_self.mpr hsub
  let S := H.edgeFinset.preimage f hi.injOn
  have hcard : S.card = n := by
    rw [← Finset.card_image_of_injective _ hi]
    change ((H.edgeFinset.preimage f hi.injOn).image f).card = _
    rw [him]
    have := ht.card_edgeFinset
    simpa using this
  refine ⟨⟨S,hcard⟩, ?_⟩
  apply SimpleGraph.edgeSet_injective
  rw [selected_edges _ _ hn, ← SimpleGraph.coe_edgeFinset, ← him, Finset.coe_image]

/-- The sum in the determinant theorem counts each actual spanning subgraph tree exactly once. -/
theorem product_as_tree_distance (u v : Fin m → Option (Fin n)) (hn : ∀ j, u j ≠ v j)
    (hi : Function.Injective (edgeOf u v)) (i : Fin n) :
    productBit u v i = ∑ H : SimpleGraph (Option (Fin n)),
      if H ≤ endpointGraph u v ∧ H.IsTree then (H.dist none (some i) : ZMod 2) else 0 := by
  classical
  rw [productBit]
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  apply Finset.sum_bij (fun s _ => selectedGraph u v s)
  · intro s hs
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hs ⊢
    exact ⟨selected_le _ _ hn s, (selected_tree _ _ hn hi s).mpr hs⟩
  · intro s _ t _ h
    exact selected_injective _ _ hn hi h
  · intro H hH
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hH
    obtain ⟨s,rfl⟩ := select_tree _ _ hn hi H hH.1 hH.2
    exact ⟨s, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (selected_tree _ _ hn hi s).mp hH.2⟩, rfl⟩
  · intro s hs
    exact color_eq_distance _ _ (Finset.mem_filter.mp hs).2 i

/-- Every ordinary finite simple graph admits an indexed, unduplicated edge presentation. -/
theorem exists_presentation (G : SimpleGraph (Option (Fin n))) :
    ∃ (m : ℕ) (u v : Fin m → Option (Fin n)), (∀ j, u j ≠ v j) ∧
      Function.Injective (edgeOf u v) ∧ endpointGraph u v = G := by
  classical
  let e := (Fintype.equivFin G.edgeSet).symm
  let f := fun i => (e i).val
  let u := fun i => (f i).out.1
  let v := fun i => (f i).out.2
  have hf (i) : edgeOf u v i = f i := by
    change Quot.mk _ (f i).out = f i
    exact Quot.out_eq _
  have hn (i) : u i ≠ v i := by
    intro he
    have hd : (edgeOf u v i).IsDiag := Sym2.mk_isDiag_iff.mpr he
    rw [hf] at hd
    exact G.not_isDiag_of_mem_edgeSet (e i).property hd
  have hi : Function.Injective (edgeOf u v) := by
    intro i j h
    apply e.injective
    exact Subtype.ext ((hf i).symm.trans (h.trans (hf j)))
  refine ⟨_,u,v,hn,hi,SimpleGraph.edgeSet_injective ?_⟩
  rw [graph_edge_set _ _ hn]
  ext z
  constructor
  · rintro ⟨j,rfl⟩
    rw [hf]; exact (e j).property
  · intro hz
    obtain ⟨i,hi⟩ := e.surjective ⟨z,hz⟩
    exact ⟨i,(hf i).trans (congrArg Subtype.val hi)⟩

end Bacher


namespace Bacher
open scoped Classical
variable {n m : ℕ}

/-- Correct on every simple, loopless graph presented by its indexed edge list.
No assumption on the parity of its spanning-tree count is needed. -/
theorem algorithm_on_graph (u v : Fin m → Option (Fin n))
    (hn : ∀ j, u j ≠ v j) (hi : Function.Injective (edgeOf u v)) (i : Fin n) :
    (partitionAlgorithm u v).1 i = ∑ H : SimpleGraph (Option (Fin n)),
      if H ≤ endpointGraph u v ∧ H.IsTree then (H.dist none (some i) : ZMod 2) else 0 := by
  rw [(partitionAlgorithm_spec u v).1]
  exact product_as_tree_distance u v hn hi i

end Bacher


namespace Bacher
open scoped BigOperators Classical

/-- The bounded algorithm returns the original vertex partition, expressed using
Mathlib's ordinary spanning subgraphs, tree predicate, and graph distance. -/
theorem endpoint_algorithm {n m : ℕ} (u v : Fin m → Option (Fin n))
    (noLoops : ∀ i, u i ≠ v i) (distinct : Function.Injective (edgeOf u v)) :
    (∀ i, (partitionAlgorithm u v).1 i =
      ∑ H : SimpleGraph (Option (Fin n)), if H ≤ endpointGraph u v ∧ H.IsTree
        then (H.dist none (some i) : ZMod 2) else 0) ∧
    (partitionAlgorithm u v).2 ≤ 3*n*m + n*(n*(2*m)) + n*(2*m) + 7*n^3 := by
  obtain ⟨correct,bound⟩ := partitionAlgorithm_spec u v
  exact ⟨fun i => (congrFun correct i).trans (product_as_tree_distance u v noLoops distinct i), bound⟩

/-- The graph representation in `endpoint_algorithm` covers every ordinary graph. -/
theorem every_graph_algorithm {n : ℕ} (G : SimpleGraph (Option (Fin n))) :
    ∃ (m : ℕ) (u v : Fin m → Option (Fin n)), endpointGraph u v = G ∧
      (∀ i, (partitionAlgorithm u v).1 i =
        ∑ H : SimpleGraph (Option (Fin n)), if H ≤ G ∧ H.IsTree
          then (H.dist none (some i) : ZMod 2) else 0) ∧
      (partitionAlgorithm u v).2 ≤ 3*n*m + n*(n*(2*m)) + n*(2*m) + 7*n^3 := by
  obtain ⟨m,u,v,hn,hi,rfl⟩ := exists_presentation G
  exact ⟨m,u,v,rfl,endpoint_algorithm u v hn hi⟩

#print axioms endpoint_algorithm
#print axioms every_graph_algorithm
end Bacher


namespace Bacher.Example
/-- Edges of the triangle on the root, 0 and 1, and a leaf 2 at the root. -/
def leftEnd (e : Fin 4) : Option (Fin 3) :=
  if e = 1 then some 0 else if e = 2 then some 1 else none
def rightEnd (e : Fin 4) : Option (Fin 3) :=
  if e = 0 then some 0 else if e = 1 then some 1 else if e = 3 then some 2 else none

theorem triangle_with_leaf : productBit leftEnd rightEnd = fun i => if i = 2 then 1 else 0 := by
  rw [← (partitionAlgorithm_spec leftEnd rightEnd).1]
  funext i
  fin_cases i <;> decide +kernel

end Bacher.Example

#print axioms Bacher.partitionAlgorithm_spec
#print axioms Bacher.algorithm_on_graph
#print axioms Bacher.every_graph_algorithm
#print axioms Bacher.even_tree_count_trivial
#print axioms Bacher.Example.triangle_with_leaf
