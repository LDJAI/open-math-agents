import OMAStatements.S_mo_386884
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

-- Credit: @LDJAI
-- Euclidean two-distance representation, with coordinates indexed by ordered vertex pairs.
theorem OMA.solution : type_of% @OMA.S_mo_386884.main := by
  classical
  intro V _ G
  let : Fintype V := Fintype.ofFinite V
  let delta (u i : V) : ℝ := if i = u then 1 else 0
  let sign (i j : V) : ℝ := if G.Adj i j then -1 else 1
  let point (u : V) : EuclideanSpace ℝ (V × V) :=
    WithLp.toLp 2 (fun t => delta u t.1 + sign t.1 t.2 * delta u t.2)
  let n : ℝ := Fintype.card V
  have n_nonneg : 0 ≤ n := Nat.cast_nonneg _
  have select (u v : V) (f : V → ℝ) :
      ∑ i, (delta u i - delta v i) * f i = f u - f v := by
    simp [delta, sub_mul, ite_mul, Finset.sum_sub_distrib]
  have distanceFormula (u v : V) (huv : u ≠ v) :
      dist (point u) (point v) ^ 2 = 4*n + 4 - 4*sign u v := by
    let D (i : V) := delta u i - delta v i
    have squared : ∑ i, D i ^ 2 = 2 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num]
      simpa [D, pow_two, delta, huv, Ne.symm huv] using select u v D
    have symmetricSign (i j : V) : sign i j = sign j i := by
      simp only [sign, G.adj_comm]
    have cross : ∑ i, ∑ j, D i * (D j * sign i j) = 2 - 2*sign u v := by
      simp_rw [← Finset.mul_sum]
      calc
        ∑ i, D i * ∑ j, D j * sign i j =
            ∑ i, D i * (sign i u - sign i v) := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [show ∑ j, D j * sign i j = sign i u - sign i v from select u v _]
        _ = (sign u u - sign u v) - (sign v u - sign v v) := select u v _
        _ = _ := by
          rw [symmetricSign v u]
          by_cases h : G.Adj u v <;> norm_num [sign, h]
    have expansion (i j : V) :
        (point u (i,j) - point v (i,j))^2 =
          (D i)^2 + (D j)^2 + 2*(D i*(D j * sign i j)) := by
      change (delta u i + sign i j * delta u j -
        (delta v i + sign i j * delta v j))^2 = _
      dsimp [D, sign]
      split <;> ring
    rw [EuclideanSpace.dist_sq_eq, Fintype.sum_prod_type]
    simp_rw [Real.dist_eq, sq_abs, expansion, Finset.sum_add_distrib]
    have diagOne : (∑ i : V, ∑ _j : V, D i ^ 2) = n*2 := by
      simp [n, nsmul_eq_mul, ← Finset.mul_sum, squared]
    have diagTwo : (∑ _i : V, ∑ j : V, D j ^ 2) = n*2 := by
      simp [squared, n, nsmul_eq_mul]
    have crossTwo : (∑ i, ∑ j, 2*(D i*(D j*sign i j))) = 2*(2-2*sign u v) := by
      simp_rw [← Finset.mul_sum]
      rw [← cross]
      simp_rw [← Finset.mul_sum]
    linarith
  let r := Real.sqrt (4*n + 8)
  have hr : 0 < r := Real.sqrt_pos.2 (by linarith)
  have hr2 : r^2 = 4*n+8 := Real.sq_sqrt (by linarith)
  let scaled (u : V) := r⁻¹ • point u
  have scaledDist (u v : V) : dist (scaled u) (scaled v) = (dist (point u) (point v)) / r := by
    simp only [scaled, dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hr), div_eq_inv_mul]
  let reindex := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Fintype.equivFin (V × V))
  refine ⟨_, fun u => reindex (scaled u), ?_, ?_⟩
  · intro u v h
    by_contra huv
    have hz : dist (scaled u) (scaled v) = 0 := dist_eq_zero.mpr (reindex.injective h)
    rw [scaledDist, div_eq_zero_iff] at hz
    have hz' := hz.resolve_right (ne_of_gt hr)
    have h := distanceFormula u v huv
    rw [hz'] at h
    have hn : 0 < n := by
      let : Nonempty V := ⟨u⟩
      dsimp [n]
      exact_mod_cast (Fintype.card_pos : 0 < Fintype.card V)
    dsimp [sign] at h
    split at h <;> linarith
  · intro u v huv
    rw [reindex.dist_map, scaledDist, div_eq_iff (ne_of_gt hr), one_mul]
    have h := distanceFormula u v huv
    by_cases he : G.Adj u v
    · simp [sign, he] at h
      exact iff_of_true he (by nlinarith [dist_nonneg (x := point u) (y := point v)])
    · simp [sign, he] at h
      exact iff_of_false he (by intro hdist; rw [hdist, hr2] at h; linarith)
