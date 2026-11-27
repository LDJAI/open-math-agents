import Std

/-! A limitation of finite-horizon ranking functions for the ordinary Collatz map.
This file is self-contained and uses the standard odd/even Collatz step. -/

namespace CollatzDescent

def collatzStep (n : Nat) : Nat :=
  if n % 2 = 0 then n / 2 else 3*n + 1

def orbit (n : Nat) : Nat → Nat
  | 0 => n
  | j+1 => orbit (collatzStep n) j

/-- Beyond `cutoff`, the rank never decreases within a residue class modulo `m`. -/
def ResidueMonotone (rank : Nat → Nat) (m cutoff : Nat) : Prop :=
  ∀ n d, cutoff ≤ n → rank n ≤ rank (n + d * m)

private def oddTerm (s : Nat) : Nat := 2 * s - 1
private def evenTerm (s : Nat) : Nat := 6 * s - 2

private theorem oneStep {s : Nat} (hs : 0 < s) :
    collatzStep (oddTerm s) = evenTerm s := by
  unfold oddTerm evenTerm collatzStep
  split <;> omega

private theorem nextOdd {s : Nat} (hs : 0 < s) :
    collatzStep (evenTerm (2*s)) = oddTerm (3*s) := by
  unfold evenTerm oddTerm collatzStep
  split <;> omega

/-- Long odd-even segments, with each of their two subsequences nondecreasing in rank. -/
private theorem segment {rank : Nat → Nat} {m cutoff : Nat}
    (hr : ResidueMonotone rank m cutoff) (hm : 0 < m) (k b : Nat)
    (hb : cutoff < b) :
    let s := 2^k * b * m
    ∀ j ≤ 2*k + 1,
      min (rank (oddTerm s)) (rank (evenTerm s)) ≤
        rank (orbit (oddTerm s) j) := by
  induction k generalizing b with
  | zero =>
    intro s j hj
    have hs : 0 < s := by dsimp [s]; exact Nat.mul_pos (Nat.mul_pos (by decide) (by omega)) hm
    have hj' : j = 0 ∨ j = 1 := by omega
    rcases hj' with rfl | rfl
    · exact Nat.min_le_left _ _
    · simpa only [orbit, oneStep hs] using Nat.min_le_right (rank (oddTerm s)) (rank (evenTerm s))
  | succ k ih =>
    let y := 2^k * b * m
    have hbpos : 0 < b := by omega
    have hby : b ≤ y := by
      dsimp [y]
      calc
        b ≤ 2^k*b := Nat.le_mul_of_pos_left b (Nat.pow_pos (by decide))
        _ ≤ 2^k*b*m := Nat.le_mul_of_pos_right _ hm
    have hy : 0 < y := by omega
    have hs : 2^(k+1)*b*m = 2*y := by dsimp [y]; rw [Nat.pow_succ]; ac_rfl
    have hs' : 2^k*(3*b)*m = 3*y := by dsimp [y]; ac_rfl
    have hrO := hr (oddTerm (2*y)) (2*(2^k*b)) (by dsimp [oddTerm]; omega)
    have hrE := hr (evenTerm (2*y)) (6*(2^k*b)) (by dsimp [evenTerm]; omega)
    have eqO : oddTerm (2*y) + (2*(2^k*b))*m = oddTerm (3*y) := by
      rw [Nat.mul_assoc 2]; change oddTerm (2*y) + 2*y = oddTerm (3*y)
      dsimp [oddTerm]; omega
    have eqE : evenTerm (2*y) + (6*(2^k*b))*m = evenTerm (3*y) := by
      rw [Nat.mul_assoc 6]; change evenTerm (2*y) + 6*y = evenTerm (3*y)
      dsimp [evenTerm]; omega
    rw [eqO] at hrO
    rw [eqE] at hrE
    have hrmin : min (rank (oddTerm (2*y))) (rank (evenTerm (2*y))) ≤ min (rank (oddTerm (3*y))) (rank (evenTerm (3*y))) :=
      Nat.le_min.mpr ⟨Nat.le_trans (Nat.min_le_left _ _) hrO, Nat.le_trans (Nat.min_le_right _ _) hrE⟩
    have hchild := ih (3*b) (by omega)
    dsimp only at hchild ⊢
    rw [hs'] at hchild
    rw [hs]
    intro j hj
    rcases j with _ | j
    · exact Nat.min_le_left _ _
    rcases j with _ | j
    · simpa only [orbit, oneStep (s := 2*y) (by omega)] using Nat.min_le_right (rank (oddTerm (2*y))) (rank (evenTerm (2*y)))
    · simpa only [orbit, oneStep (s := 2*y) (by omega),
        nextOdd hy] using Nat.le_trans hrmin (hchild j (by omega))

/-- Every finite horizon has arbitrarily large starting values from which none of the
next ranks is smaller, even when the rank can behave differently on every residue
class. The modulus, ranking function, and monotonicity threshold are all arbitrary. -/
theorem noUniformRankDescent (rank : Nat → Nat) (m cutoff : Nat)
    (hm : 0 < m) (hr : ResidueMonotone rank m cutoff) (horizon lower : Nat) :
    ∃ n > lower, ∀ j ≤ horizon, rank n ≤ rank (orbit n j) := by
  let b := cutoff + lower + 1
  let s := 2^horizon * b * m
  have hb : cutoff < b := by dsimp [b]; omega
  have hbs : b ≤ s := by
    calc
      b ≤ 2^horizon*b := Nat.le_mul_of_pos_left b (Nat.pow_pos (by decide))
      _ ≤ s := Nat.le_mul_of_pos_right _ hm
  have hs : 0 < s := by omega
  have hx := segment hr hm horizon b hb
  change ∀ j ≤ 2*horizon+1, min (rank (oddTerm s)) (rank (evenTerm s)) ≤ rank (orbit (oddTerm s) j) at hx
  by_cases ho : rank (oddTerm s) ≤ rank (evenTerm s)
  · refine ⟨oddTerm s, ?_, ?_⟩
    · dsimp [oddTerm, b] at *; omega
    · intro j hj
      simpa only [Nat.min_eq_left ho] using hx j (by omega)
  · have he : rank (evenTerm s) ≤ rank (oddTerm s) := by omega
    refine ⟨evenTerm s, ?_, ?_⟩
    · dsimp [evenTerm, b] at *; omega
    · intro j hj
      simpa only [Nat.min_eq_right he, orbit, oneStep hs]
        using hx (j+1) (by omega)

private theorem orbit_add (n i j : Nat) :
    orbit (orbit n i) j = orbit n (i+j) := by
  induction i generalizing n with
  | zero => simp [orbit]
  | succ i ih =>
    simpa only [Nat.succ_add, orbit] using ih (collatzStep n)

private theorem orbit_pos (n k : Nat) (hn : 0 < n) : 0 < orbit n k := by
  induction k generalizing n with
  | zero => exact hn
  | succ k ih =>
    apply ih
    unfold collatzStep
    split <;> omega

/-- Allowing the descent horizon to depend on the starting number gives an
exact equivalent of the full Collatz conjecture. -/
theorem convergence_iff_descent :
    (∀ n > 0, ∃ k, orbit n k = 1) ↔ (∀ n > 1, ∃ k, orbit n k < n) := by
  constructor
  · intro hc n hn
    obtain ⟨k, hk⟩ := hc n (by omega)
    exact ⟨k, by omega⟩
  · intro hd n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro hn
      by_cases he : n = 1
      · exact ⟨0, he⟩
      · obtain ⟨k, hk⟩ := hd n (by omega)
        obtain ⟨j, hj⟩ := ih (orbit n k) hk (orbit_pos n k hn)
        exact ⟨k+j, (orbit_add n k j).symm.trans hj⟩

#print axioms convergence_iff_descent

#print axioms noUniformRankDescent

end CollatzDescent
