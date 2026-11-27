import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace CloneSize

theorem log_factorial_le (N : ℕ) :
    Real.log (N.factorial : ℝ) ≤ (N : ℝ) * Real.log N := by
  have h : (N.factorial : ℝ) ≤ (N : ℝ)^N := by exact_mod_cast N.factorial_le_pow
  have hpos : 0 < (N.factorial : ℝ) := by exact_mod_cast N.factorial_pos
  simpa [Real.log_pow] using Real.log_le_log hpos h

/-- With L=256 n² and odds base 4/3, the representative regret cutoff
log((nL)!)/(L² log(4/3)) is strictly below 1/8. -/
theorem cutoff (n : ℕ) (hn : 2 ≤ n) :
    let L : ℕ := 256*n^2
    Real.log ((n*L).factorial : ℝ) < (L : ℝ)^2 * Real.log (4/3) / 8 := by
  dsimp only
  let L : ℕ := 256*n^2
  change Real.log ((n*L).factorial : ℝ) < (L : ℝ)^2 * Real.log (4/3) / 8
  have hnr : (2:ℝ) ≤ n := by exact_mod_cast hn
  have npos : 0 < (n:ℝ) := by linarith
  have hL : (L : ℝ) = 256*(n:ℝ)^2 := by dsimp [L]; push_cast; ring
  have lpos : 0 < (L : ℝ) := by rw [hL]; positivity
  have castN : ((n*L:ℕ):ℝ) = (n:ℝ)*L := by norm_cast
  have Npos : 0 < (n:ℝ)*L := mul_pos npos lpos
  have hlog2 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (x:=2) (by norm_num)]
  have log256 : Real.log 256 = 8 * Real.log 2 := by
    rw [show (256:ℝ) = 2^8 by norm_num, Real.log_pow]
    norm_num
  have Nrepr : (n:ℝ)*L = 256*(n:ℝ)^3 := by rw [hL]; ring
  have hln : Real.log ((n:ℝ)*L) ≤ 5+3*n := by
    rw [Nrepr, Real.log_mul (by norm_num) (pow_ne_zero _ npos.ne'), log256, Real.log_pow]
    push_cast
    linarith [Real.log_le_sub_one_of_pos npos]
  have lower : (1:ℝ)/4 ≤ Real.log (4/3) := by
    have h := Real.one_sub_inv_le_log_of_pos (x:=(4:ℝ)/3) (by norm_num)
    norm_num at h ⊢
    linarith
  calc
    _ ≤ ((n:ℝ)*L) * Real.log ((n:ℝ)*L) := by simpa [castN] using log_factorial_le (n*L)
    _ ≤ ((n:ℝ)*L) * (5+3*n) := mul_le_mul_of_nonneg_left hln Npos.le
    _ < ((n:ℝ)*L) * (8*n) := mul_lt_mul_of_pos_left (by linarith) Npos
    _ = (L : ℝ)^2 * (1/4) / 8 := by rw [hL]; ring
    _ ≤ (L : ℝ)^2 * Real.log (4/3) / 8 := by nlinarith [mul_nonneg (sq_nonneg (L:ℝ)) (sub_nonneg.mpr lower)]

end CloneSize

#print axioms CloneSize.cutoff
