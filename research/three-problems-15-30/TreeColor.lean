import TreeIncidence
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Finset.Sort

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
