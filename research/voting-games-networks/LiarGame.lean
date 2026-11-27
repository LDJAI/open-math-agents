import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Ring

/-! Sphere volume for a binary Rényi–Ulam liar game, and a minimax property
of the even split with respect to that necessary solvability test. -/
namespace LiarGame

/-- Number of response strings of length h allowing at most r wrong answers. -/
def ball (h r : ℕ) : ℕ := ∑ i ∈ Finset.range (r + 1), h.choose i

/-- The volume of continuations after using one available lie. -/
def lieBall (h : ℕ) : ℕ → ℕ
  | 0 => 0
  | r + 1 => ball h r

theorem ball_step (h r : ℕ) : ball (h + 1) r = ball h r + lieBall h r := by
  induction r with
  | zero => simp [ball, lieBall]
  | succ r ih =>
    have hsum (t u : ℕ) : ball t (u + 1) = ball t u + t.choose (u+1) := by
      exact Finset.sum_range_succ _ _
    rw [hsum, ih, hsum, Nat.choose_succ_succ]
    cases r with
    | zero => simp [lieBall, ball]; omega
    | succ r =>
      simp only [lieBall, Nat.succ_eq_add_one]
      have hx := hsum h r
      omega

/-- A histogram indexed by remaining lie budget, from zero through n-1. -/
def volume {n : ℕ} (h : ℕ) (s : Fin n → ℕ) : ℕ :=
  ∑ r, s r * ball h r.val

/-- If a candidate falls on the true side, its budget stays intact. Candidates
on the false side spend one lie. Those at zero remaining lies disappear. -/
def branch {n : ℕ} (h : ℕ) (trueSide falseSide : Fin n → ℕ) : ℕ :=
  ∑ r, (trueSide r * ball h r.val + falseSide r * lieBall h r.val)

theorem conservation {n : ℕ} (h : ℕ) (a b : Fin n → ℕ) :
    branch h a b + branch h b a = volume (h+1) (fun r => a r + b r) := by
  unfold branch volume
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  rw [ball_step]
  ring

/-- For an even histogram, halving every class minimizes the worse of the two
child sphere volumes over *every* legal first question. -/
theorem even_split_minimizes_worst_volume {n : ℕ} (h : ℕ)
    (c a b : Fin n → ℕ) (split : ∀ r, a r + b r = c r + c r) :
    branch h c c ≤ max (branch h a b) (branch h b a) := by
  have h1 := conservation h a b
  have h2 := conservation h c c
  have he : (fun r => a r + b r) = (fun r => c r + c r) := funext split
  rw [he] at h1
  omega

end LiarGame
