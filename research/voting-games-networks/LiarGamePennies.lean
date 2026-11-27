import LiarGameHomogeneous
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import LiarGameOccupancy

/-! An even homogeneous class of candidates at arbitrary positive lie
allowance can be halved optimally even in the presence of arbitrary
evenly many zero-lie candidates. -/
namespace LiarGamePennies
open LiarGameExtension LiarGameMasks LiarGameOccupancy LiarGameHomogeneous

/-- With k faithful answers in a class of size n, its child contribution is
k copies of the larger volume and n-k copies of the smaller volume. -/
private theorem sum_cutoff (n k a b : ℕ) (hk : k ≤ n) :
    (∑ i : Fin n, if i.val < k then a else b) = k * a + (n - k) * b := by
  induction n generalizing k with
  | zero =>
    have : k = 0 := by omega
    subst k
    simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    by_cases h : k ≤ n
    · rw [ih k h, if_neg (by omega : ¬n < k)]
      have e : n + 1 - k = (n - k) + 1 := by omega
      rw [e, Nat.add_mul, Nat.one_mul]
      omega
    · have e : k = n + 1 := by omega
      subst k
      have bound (i : Fin n) : i.val < n+1 := Nat.lt_succ_of_lt i.isLt
      simp [bound, Nat.add_mul]

def highBudget (r k : ℕ) {n : ℕ} (i : Fin n) : ℕ :=
  if i.val < k then r + 1 else r

private theorem volume_count (h r n k : ℕ) (hk : k ≤ n) :
    (∑ i : Fin n, maskVolume h (highBudget r k i)) =
    k * maskVolume h (r + 1) + (n-k) * maskVolume h r := by
  have e (i : Fin n) : maskVolume h (highBudget r k i) =
      (if i.val < k then maskVolume h (r+1) else maskVolume h r) := by
    unfold highBudget; split <;> rfl
  simpa only [e] using sum_cutoff n k (maskVolume h (r+1))
    (maskVolume h r) hk

private theorem high_mono {h r n a b : ℕ} (hb : a ≤ b)
    (hs : Solvable h (@highBudget r b n)) : Solvable h (@highBudget r a n) := by
  obtain ⟨A,hA⟩ := hs
  refine ⟨A, decodes_lower_budget hA ?_⟩
  intro x; unfold highBudget; split <;> split <;> omega

/-- Initially 2u candidates can sustain r+1 lies and 2v can sustain zero.
An arbitrary first question selects k high-budget and l zero-budget
candidates, so k, l are at most their class sizes. If that question wins
with either answer and h further rounds, the even split wins as well. -/
theorem homogeneous_halving_with_pennies (h r u v k l : ℕ)
    (hk : k ≤ 2*u) (hl : l ≤ 2*v)
    (yes : Solvable h (extendBudget (F := Fin l) (@highBudget r k (2*u))))
    (no : Solvable h (extendBudget (F := Fin (2*v-l)) (@highBudget r (2*u-k) (2*u)))) :
    Solvable h (extendBudget (F := Fin v) (@highBudget r u (2*u))) := by
  obtain ⟨s1,b1⟩ := (with_pennies_iff _ _).mp yes
  obtain ⟨s2,b2⟩ := (with_pennies_iff _ _).mp no
  apply (with_pennies_iff _ _).mpr
  constructor
  · rcases Nat.le_total u k with e | e
    · exact high_mono e s1
    · exact high_mono (by omega : u ≤ 2*u-k) s2
  · rw [volume_count h r _ _ hk] at b1
    rw [volume_count h r _ _ (by omega : 2*u-k ≤ 2*u)] at b2
    rw [volume_count h r _ _ (by omega : u ≤ 2*u)]
    have hk' : 2*u-(2*u-k)=k := by omega
    have hu : 2*u-u=u := by omega
    rw [hk'] at b2; rw [hu]
    have c1 (a : ℕ) : k*a+(2*u-k)*a=2*(u*a) := by
      rw [← Nat.add_mul, Nat.add_sub_of_le hk]; ring
    have c2 := c1 (maskVolume h (r+1))
    have c3 := c1 (maskVolume h r)
    omega


/-- If balancing wins after deleting the original zero-lie candidates, it
still wins after restoring them whenever *any* first question wins. Thus
deleting all original pennies preserves every counterexample to even splitting. -/
theorem restore_initial_pennies {C : Type*} [Fintype C]
    (h v l : ℕ) (r u k : C → ℕ) (hk : ∀ i, k i ≤ 2*u i) (hl : l ≤ 2*v)
    (hard : Solvable h (childBudget (size := fun i => 2*u i) r u))
    (yes : Solvable h (extendBudget (F := Fin l)
       (childBudget (size := fun i => 2*u i) r k)))
    (no : Solvable h (extendBudget (F := Fin (2*v-l))
       (childBudget (size := fun i => 2*u i) r (fun i => 2*u i-k i)))) :
    Solvable h (extendBudget (F := Fin v)
       (childBudget (size := fun i => 2*u i) r u)) := by
  have hy := ((with_pennies_iff _ _).mp yes).2
  have hn := ((with_pennies_iff _ _).mp no).2
  apply (with_pennies_iff _ _).mpr
  refine ⟨hard,?_⟩
  let W (q : C → ℕ) := ∑ x : (i : C) × Fin (2 * u i),
    maskVolume h (childBudget r q x)
  change W k + l ≤ 2^h at hy
  change W (fun i => 2*u i - k i) + (2*v-l) ≤ 2^h at hn
  change W u + v ≤ 2^h
  have double : W k + W (fun i => 2*u i-k i) = 2 * W u := by
    unfold W
    simp only [Fintype.sum_sigma, ← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_add_distrib]
    change (∑ j : Fin (2*u i), maskVolume h (highBudget (r i) (k i) j)) +
      (∑ j : Fin (2*u i), maskVolume h (highBudget (r i) (2*u i-k i) j)) =
      ∑ j : Fin (2*u i), 2 * maskVolume h (highBudget (r i) (u i) j)
    rw [← Finset.mul_sum]
    have hk' := hk i
    rw [volume_count h _ _ _ hk', volume_count h _ _ _ (by omega : 2*u i-k i ≤ 2*u i),
      volume_count h _ _ _ (by omega : u i ≤ 2*u i)]
    have d : 2*u i - (2*u i - k i) = k i := by omega
    have e : 2*u i - u i = u i := by omega
    rw [d,e]
    have expand (a : ℕ) : k i*a+(2*u i-k i)*a=2*(u i*a) := by
      rw [← Nat.add_mul, Nat.add_sub_of_le hk']; ring
    have eq1 := expand (maskVolume h (r i + 1))
    have eq2 := expand (maskVolume h (r i))
    omega
  omega

/-- A question which beats balancing must select above half the class in
at least one positive lie allowance and below half in another. This holds
regardless of how many of the original zero-lie candidates it selects. -/
theorem same_sign_halving_with_pennies {C : Type*} [Fintype C]
    (h v l : ℕ) (r u k : C → ℕ) (hk : ∀ i, k i ≤ 2*u i) (hl : l ≤ 2*v)
    (yes : Solvable h (extendBudget (F := Fin l)
       (childBudget (size := fun i => 2*u i) r k)))
    (no : Solvable h (extendBudget (F := Fin (2*v-l))
       (childBudget (size := fun i => 2*u i) r (fun i => 2*u i-k i))))
    (hSign : (∀ i, u i ≤ k i) ∨ (∀ i, k i ≤ u i)) :
    Solvable h (extendBudget (F := Fin v)
       (childBudget (size := fun i => 2*u i) r u)) := by
  apply restore_initial_pennies h v l r u k hk hl _ yes no
  exact same_sign_halving h r u k ((with_pennies_iff _ _).mp yes).1
    ((with_pennies_iff _ _).mp no).1 hSign

end LiarGamePennies
