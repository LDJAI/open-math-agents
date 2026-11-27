import TreeResult
import TreeParity

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
