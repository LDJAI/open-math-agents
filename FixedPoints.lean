import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Tactic.NoncommRing

/- The range of the idempotent transfer consists precisely of elements on which
the endomorphism and the Cuntz doubling coincide. We avoid division by using
the unnormalized transfer, whose square is twice itself. -/
namespace SectorFixedPoints

variable {R : Type*} [CStarAlgebra R] [PartialOrder R] [StarOrderedRing R]
  [IsOrderedAddMonoid R]

def transfer (r : R →+* R) (s t x : R) : R :=
  star s * r x * s + star t * r x * t

private theorem four_squares (a b c d : R)
    (h : (star a * a + star b * b) + (star c * c + star d * d) = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  have split {u v : R} (hu : 0 ≤ u) (hv : 0 ≤ v) (h0 : u + v = 0) :
      u = 0 ∧ v = 0 := by
    constructor
    · exact le_antisymm (h0 ▸ le_add_of_nonneg_right hv) hu
    · exact le_antisymm (h0 ▸ le_add_of_nonneg_left hu) hv
  have habcd := split (add_nonneg (star_mul_self_nonneg a) (star_mul_self_nonneg b))
    (add_nonneg (star_mul_self_nonneg c) (star_mul_self_nonneg d)) h
  have hab := split (star_mul_self_nonneg a) (star_mul_self_nonneg b) habcd.1
  have hcd := split (star_mul_self_nonneg c) (star_mul_self_nonneg d) habcd.2
  exact ⟨(CStarRing.star_mul_self_eq_zero_iff _).mp hab.1,
    (CStarRing.star_mul_self_eq_zero_iff _).mp hab.2,
    (CStarRing.star_mul_self_eq_zero_iff _).mp hcd.1,
    (CStarRing.star_mul_self_eq_zero_iff _).mp hcd.2⟩

theorem fixed_iff (r : R →+* R) (s t x : R)
    (hstar : ∀ y, r (star y) = star (r y)) (hr : Function.Injective r) (hs : star s * s = 1) (ht : star t * t = 1)
    (hfull : s * star s + t * star t = 1)
    (hproj : ∀ y, transfer r s t (transfer r s t y) =
      transfer r s t y + transfer r s t y) :
    transfer r s t x = x + x ↔ r x = s * x * star s + t * x * star t := by
  constructor
  · intro hx
    let a := r x * s - s * x
    let b := r x * t - t * x
    have hx' : transfer r s t (star x) = star x + star x := by
      simpa only [transfer, star_add, star_mul, star_star, hstar, mul_assoc] using congrArg star hx
    have hv : star a * a + star b * b = transfer r s t (star x * x) -
        (star x * x + star x * x) := by
      calc
        _ = transfer r s t (star x * x) - transfer r s t (star x) * x -
            star x * transfer r s t x + star x * (star s * s + star t * t) * x := by
              simp only [a, b, transfer, hstar, map_mul, star_sub, star_mul]
              noncomm_ring
        _ = _ := by rw [hx', hx, hs, ht]; noncomm_ring
    have hz : transfer r s t (star a * a + star b * b) = 0 := by
      rw [hv]
      have hlin (p q u : R) : transfer r s t (p - (q + u)) =
          transfer r s t p - (transfer r s t q + transfer r s t u) := by
        simp only [transfer, map_sub, map_add]
        noncomm_ring
      rw [hlin, hproj, sub_self]
    have hsq : (star (r a * s) * (r a * s) + star (r b * s) * (r b * s)) +
        (star (r a * t) * (r a * t) + star (r b * t) * (r b * t)) = 0 := by
      convert hz using 1
      simp only [transfer, map_add, hstar, map_mul, star_mul]
      noncomm_ring
    obtain ⟨has, hbs, hat, hbt⟩ := four_squares _ _ _ _ hsq
    have hkill (z : R) (hzs : r z * s = 0) (hzt : r z * t = 0) : z = 0 := by
      apply hr
      calc
        r z = r z * (s * star s + t * star t) := by rw [hfull, mul_one]
        _ = 0 := by rw [mul_add, ← mul_assoc, hzs, zero_mul, ← mul_assoc, hzt, zero_mul, add_zero]
        _ = r 0 := (map_zero r).symm
    have ha : r x * s = s * x := sub_eq_zero.mp (hkill a has hat)
    have hb : r x * t = t * x := sub_eq_zero.mp (hkill b hbs hbt)
    calc
      r x = r x * (s * star s + t * star t) := by rw [hfull, mul_one]
      _ = _ := by rw [mul_add, ← mul_assoc, ha, ← mul_assoc, hb]
  · intro heq
    have hst0 : star s * t = 0 := by
      have h : (star s * s) * (star s * t) + (star s * t) * (star t * t) = star s * t := by
        calc
          _ = star s * (s * star s + t * star t) * t := by noncomm_ring
          _ = _ := by rw [hfull, mul_one]
      rw [hs, ht, one_mul, mul_one] at h
      exact add_left_cancel (h.trans (add_zero _).symm)
    have hts0 : star t * s = 0 := by simpa only [star_mul, star_star, star_zero] using congrArg star hst0
    have hsx : r x * s = s * x := by
      rw [heq, add_mul, mul_assoc, hs, mul_one, mul_assoc, hts0, mul_zero, add_zero]
    have htx : r x * t = t * x := by
      rw [heq, add_mul, mul_assoc, hst0, mul_zero, mul_assoc, ht, mul_one, zero_add]
    unfold transfer
    rw [mul_assoc (star s), hsx, ← mul_assoc, hs, one_mul,
      mul_assoc (star t), htx, ← mul_assoc, ht, one_mul]

/-- The Pimsner–Popa bound on the original algebra, with the transfer left
unnormalized. For E=T/2 the conclusion reads x ≤ 4E(x). -/
theorem transfer_bound (r : R →+* R) (s t x : R)
    (hstar : ∀ u, r (star u) = star (r u))
    (hr : Function.Injective r) (hs : star s * s = 1) (ht : star t * t = 1)
    (hfull : s * star s + t * star t = 1)
    (hproj : ∀ u, transfer r s t (transfer r s t u) =
      transfer r s t u + transfer r s t u)
    (horder : ∀ u v, r u ≤ r v ↔ u ≤ v) (hx : 0 ≤ x) :
    x ≤ transfer r s t x + transfer r s t x := by
  let Z := s * star s - t * star t
  let X := s * star t + t * star s
  let Y := s * star t - t * star s
  have hfixed := (fixed_iff r s t (transfer r s t x) hstar hr hs ht hfull hproj).mp (hproj x)
  have hrest : r x = (s * star s + t * star t) * r x * (s * star s + t * star t) := by
    rw [hfull, one_mul, mul_one]
  have hsum : r (transfer r s t x + transfer r s t x) - r x =
      star Z * r x * Z + star X * r x * X + star Y * r x * Y := by
    rw [map_add, hfixed]
    rw [sub_eq_add_neg]
    rw [show -r x = -((s * star s + t * star t) * r x * (s * star s + t * star t)) from congrArg Neg.neg hrest]
    simp only [transfer, Z, X, Y, star_add, star_sub, star_mul, star_star]
    noncomm_ring
  have hpos : 0 ≤ r x := by simpa only [map_zero] using (horder 0 x).mpr hx
  exact (horder _ _).mp <| sub_nonneg.mp <| hsum ▸
    add_nonneg (add_nonneg (star_left_conjugate_nonneg hpos Z) (star_left_conjugate_nonneg hpos X))
      (star_left_conjugate_nonneg hpos Y)

end SectorFixedPoints

#print axioms SectorFixedPoints.fixed_iff
#print axioms SectorFixedPoints.transfer_bound
