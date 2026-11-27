import Mathlib.Algebra.Star.StarRingHom
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.NoncommRing

/- The averaging identity at the algebraic core of Henriques's question.
   The hypotheses say that ρ is an irreducible unital star-endomorphism
   implemented at its square by the displayed Cuntz family. -/
open Finset
open scoped BigOperators

namespace SectorTransfer
variable {R I : Type*} [Ring R] [StarRing R] [Fintype I]

/-- Changing Cuntz families preserves the sum of diagonal compressions when
    the transition coefficients are central. Only completeness is needed. -/
theorem transfer_basis {J K : Type*} [Fintype J] [Fintype K]
    (a : J → R) (b : K → R) (z : R)
    (ha : ∑ j, a j * star (a j) = 1) (hb : ∑ k, b k * star (b k) = 1)
    (hc : ∀ j k y, (star (a j) * b k) * y = y * (star (a j) * b k)) :
    ∑ j, star (a j) * z * a j = ∑ k, star (b k) * z * b k := by
  calc
    _ = ∑ j, ∑ k, (star (a j) * b k) * (star (b k) * z * a j) := by
      apply sum_congr rfl
      intro j _
      simp_rw [show ∀ k, (star (a j) * b k) * (star (b k) * z * a j) =
        star (a j) * (b k * star (b k)) * z * a j by intro k; noncomm_ring]
      rw [← sum_mul, ← sum_mul, ← mul_sum, hb, mul_one]
    _ = ∑ k, ∑ j, (star (b k) * z * a j) * (star (a j) * b k) := by
      simp_rw [hc]
      rw [sum_comm]
    _ = _ := by
      apply sum_congr rfl
      intro k _
      simp_rw [show ∀ j, (star (b k) * z * a j) * (star (a j) * b k) =
        (star (b k) * z) * (a j * star (a j)) * b k by intro j; noncomm_ring]
      rw [← sum_mul, ← mul_sum, ha, mul_one]

/-- The unnormalized average satisfies T² = |I| T at arbitrary multiplicity. -/
theorem transfer_square (rho : R →+* R) (hstar : ∀ y, rho (star y) = star (rho y)) (w : I → R) (x : R)
    (hunit : ∑ i, w i * star (w i) = 1)
    (hisom : ∀ i, star (w i) * w i = 1)
    (hinter : ∀ i t, rho (rho t) * w i = w i * rho t)
    (hirred : ∀ y, (∀ t, y * rho t = rho t * y) → ∀ v, y * v = v * y) :
    let T := fun v : R => ∑ i, star (w i) * rho v * w i
    T (T x) = Fintype.card I • T x := by
  classical
  let a : I × I → R := fun ij => rho (w ij.1) * w ij.2
  let b : I × I → R := fun ij => w ij.1 * w ij.2
  have hab (f : R →+* R) (hf : ∀ y, f (star y) = star (f y)) :
      ∑ ij : I × I, (f (w ij.1) * w ij.2) * star (f (w ij.1) * w ij.2) = 1 := by
    rw [Fintype.sum_prod_type]
    simp only [star_mul]
    simp_rw [show ∀ i j, (f (w i) * w j) * (star (w j) * star (f (w i))) =
      f (w i) * (w j * star (w j)) * star (f (w i)) by intros; noncomm_ring]
    simp_rw [← sum_mul, ← mul_sum, hunit, mul_one]
    simp only [← hf, ← map_mul, ← map_sum, hunit, map_one]
  have ha (ij : I × I) (t : R) :
      rho (rho (rho t)) * a ij = a ij * rho t := by
    dsimp [a]
    rw [← mul_assoc, ← map_mul, hinter, map_mul, mul_assoc, hinter, mul_assoc]
  have hb (ij : I × I) (t : R) :
      rho (rho (rho t)) * b ij = b ij * rho t := by
    dsimp [b]
    rw [← mul_assoc, hinter, mul_assoc, hinter, mul_assoc]
  have hadj (ij : I × I) (t : R) :
      star (a ij) * rho (rho (rho t)) = rho t * star (a ij) := by
    simpa only [star_mul, ← hstar, star_star] using congrArg star (ha ij (star t))
  have hc (ij kl : I × I) : ∀ y, (star (a ij) * b kl) * y = y * (star (a ij) * b kl) := by
    apply hirred
    intro t
    rw [mul_assoc, ← hb, ← mul_assoc, hadj, mul_assoc]
  have hchange := transfer_basis a b (rho (rho x)) (hab rho hstar)
    (by simpa [b] using hab (RingHom.id R) (fun _ => rfl)) hc
  simp only [Fintype.sum_prod_type, a, b, star_mul] at hchange
  change (∑ j, star (w j) * rho (∑ i, star (w i) * rho x * w i) * w j) = _
  simp only [map_sum, map_mul, hstar, mul_sum, sum_mul]
  calc
    _ = ∑ i, ∑ j, (star (w j) * star (rho (w i))) * rho (rho x) * (rho (w i) * w j) := by
      rw [sum_comm]
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro j _
      noncomm_ring
    _ = _ := hchange
    _ = _ := by
      simp_rw [show ∀ i j, (star (w j) * star (w i)) * rho (rho x) * (w i * w j) =
          star (w j) * rho x * w j by
        intro i j
        calc
          _ = star (w j) * (star (w i) * (rho (rho x) * w i)) * w j := by noncomm_ring
          _ = _ := by rw [hinter, ← mul_assoc (star (w i)) (w i) (rho x), hisom, one_mul]]
      simp

end SectorTransfer

#print axioms SectorTransfer.transfer_basis
#print axioms SectorTransfer.transfer_square
