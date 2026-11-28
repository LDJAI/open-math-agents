import OMAStatements.S_oeis_a067016
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases
import Mathlib.Algebra.Ring.Parity

namespace OMA
open OMA.S_oeis_a067016

def staircase (n : ℕ) : ℕ :=
  if n = 0 then 1 else if n = 1 then 4 else if n = 2 then 3 else
  if n = 3 then 2 else 2*n - 1 - n%2

lemma staircase_tail (n : ℕ) (h : 4 ≤ n) :
    staircase n = 2*n - 1 - n%2 := by
  unfold staircase
  repeat first | omega | split

lemma staircase_upper (i j : ℕ) (h : 3 ≤ i+j) :
    staircase i + staircase j ≤ staircase (i+j+1) := by
  rw [staircase_tail (i+j+1) (by omega)]
  unfold staircase
  repeat first | omega | split

lemma staircase_attain (n : ℕ) (h : 4 ≤ n) :
    staircase 1 + staircase n = staircase (n+2) := by
  rw [staircase_tail n h, staircase_tail (n+2) (by omega)]
  change 4 + (2*n-1-n%2) = 2*(n+2)-1-(n+2)%2
  omega

lemma staircase_witness (n : ℕ) (h : 3 ≤ n) :
    ∃ i j : ℕ, i+j=n ∧ staircase i + staircase j = staircase (n+1) := by
  by_cases h3 : n = 3
  · subst n
    exact ⟨1,2,rfl,rfl⟩
  by_cases h4 : n = 4
  · subst n
    exact ⟨0,4,rfl,rfl⟩
  have h5 : 4 ≤ n-1 := by omega
  refine ⟨1,n-1,by omega,?_⟩
  have ha := staircase_attain (n-1) h5
  have he : n-1+2 = n+1 := by omega
  rw [he] at ha
  exact ha

lemma max_plus_eq (n : ℕ) : a n = staircase n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < 4
    · have hc : n=0 ∨ n=1 ∨ n=2 ∨ n=3 := by omega
      rcases hc with hc|hc|hc|hc <;> subst n <;> simp [a,staircase]
    · obtain ⟨k,hk⟩ : ∃ k : ℕ, n = k+4 := ⟨n-4, by omega⟩
      subst n
      rw [a]
      apply le_antisymm
      · apply Finset.sup_le
        intro i _
        have hi := i.isLt
        rw [ih i (by omega), ih (k+3-i) (by omega)]
        have hsum : (i : ℕ) + (k+3-i) = k+3 := by omega
        have hu := staircase_upper (i : ℕ) (k+3-i) (by omega)
        rw [hsum] at hu
        exact hu
      · obtain ⟨i,j,hij,hb⟩ := staircase_witness (k+3) (by omega)
        let ii : Fin (k+4) := ⟨i, by omega⟩
        apply Finset.le_sup_of_le (b := ii) (Finset.mem_univ ii)
        change staircase (k+4) ≤ a i + a (k+3-i)
        rw [ih i (by omega), ih (k+3-i) (by omega)]
        have h : k+3-i=j := by omega
        rw [h,hb]

lemma staircase_formula (n : ℕ) (hn : 4 ≤ n) :
    2 * (a n : ℤ) = -3 + (-1 : ℤ)^n + 4*(n : ℤ) := by
  rw [max_plus_eq, staircase, neg_one_pow_eq_pow_mod_two]
  split_ifs <;> try omega
  have hm : n%2 = 0 ∨ n%2 = 1 := by omega
  rcases hm with hm|hm <;> rw [hm] <;> norm_num <;> omega

open PowerSeries in
lemma staircase_gf :
    (1-X)^2 * (1+X) * mk (fun n => (a n : ℤ)) =
      1 + 3*X - 2*X^2 - 4*X^3 + 6*X^4 + 2*X^5 - 2*X^6 := by
  let p : PowerSeries ℤ := mk (fun n => (a n : ℤ))
  change (1-X)^2*(1+X)*p = _
  have hp : (1-X)^2*(1+X)*p = p-X^1*p-X^2*p+X^3*p := by ring
  have hR : (1 + 3*X - 2*X^2 - 4*X^3 + 6*X^4 + 2*X^5 - 2*X^6 : PowerSeries ℤ) =
    C 1 + C 3*X^1 - C 2*X^2 - C 4*X^3 + C 6*X^4 + C 2*X^5 - C 2*X^6 := by simp
  rw [hp,hR]
  apply PowerSeries.ext
  intro n
  simp only [map_add,map_sub,coeff_X_pow_mul',coeff_C_mul_X_pow,coeff_C,p,coeff_mk]
  by_cases hn : n < 7
  · interval_cases n <;> norm_num [max_plus_eq,staircase]
  · have h1 : 1 ≤ n := by omega
    have h2 : 2 ≤ n := by omega
    have h3 : 3 ≤ n := by omega
    have hn0 : n ≠ 0 := by omega
    have hn1 : n ≠ 1 := by omega
    have hn2 : n ≠ 2 := by omega
    have hn3 : n ≠ 3 := by omega
    have hn4 : n ≠ 4 := by omega
    have hn5 : n ≠ 5 := by omega
    have hn6 : n ≠ 6 := by omega
    simp only [if_pos h1,if_pos h2,if_pos h3,max_plus_eq,hn0,hn1,hn2,hn3,hn4,hn5,hn6,if_false]
    rw [staircase_tail n (by omega), staircase_tail (n-1) (by omega),
        staircase_tail (n-2) (by omega), staircase_tail (n-3) (by omega)]
    omega

theorem solution : type_of% @OMA.S_oeis_a067016.main := by
  exact ⟨staircase_formula, staircase_gf⟩

end OMA
