import LiarGameExtension
import Mathlib.Data.Nat.Basic

/-! Halving is minimax-optimal when all candidates start with the same
positive lie allowance. We work with actual adaptive question strategies:
a successful strategy distinguishes candidates on all compatible transcripts.
Within each starting class, candidates are interchangeable, so a child state
with k truthful members from a class is numbered with these k members first. -/
namespace LiarGameHomogeneous
open LiarGameExtension

/-- Solving a state is preserved by decreasing arbitrary candidates' budgets. -/
theorem decodes_lower_budget {h : ℕ} {I : Type*} {A : Strategy h I}
    {b c : I → ℕ} (hA : Decodes A b) (hc : ∀ x, c x ≤ b x) :
    Decodes A c := by
  intro w x y hx hy
  exact hA w x y (Nat.le_trans hx (hc x)) (Nat.le_trans hy (hc y))

def Solvable {I : Type*} (h : ℕ) (b : I → ℕ) : Prop :=
  ∃ A : Strategy h I, Decodes A b

/-- The size of class i is arbitrary. Its starting allowance is r i + 1.
After an answer, k i candidates retain that allowance, and the other
members consume one lie. Indexing within each class is local to this child. -/
def childBudget {C : Type*} {size : C → ℕ} (r k : C → ℕ)
    (x : (i : C) × Fin (size i)) : ℕ :=
  if x.2.val < k x.1 then r x.1 + 1 else r x.1

theorem child_monotone {C : Type*} {size : C → ℕ} {h : ℕ}
    (r a b : C → ℕ) (hab : ∀ i, a i ≤ b i)
    (hs : Solvable h (childBudget (size := size) r b)) :
    Solvable h (childBudget (size := size) r a) := by
  obtain ⟨A, hA⟩ := hs
  refine ⟨A, decodes_lower_budget hA ?_⟩
  intro x
  unfold childBudget
  have hk := hab x.1
  split <;> split <;> omega

/-- In a state with even positive-budget classes of size 2u(i),
every winning question whose class imbalances have the same sign can be
replaced by the balanced question, with the same worst-case depth. -/
theorem same_sign_halving {C : Type*} (h : ℕ) (r u k : C → ℕ)
    (hYes : Solvable h (childBudget (size := fun i => 2 * u i) r k))
    (hNo : Solvable h (childBudget (size := fun i => 2 * u i) r
      (fun i => 2 * u i - k i)))
    (hSign : (∀ i, u i ≤ k i) ∨ (∀ i, k i ≤ u i)) :
    Solvable h (childBudget (size := fun i => 2 * u i) r u) := by
  rcases hSign with ge | le
  · exact child_monotone r u k ge hYes
  · apply child_monotone r u _ _ hNo
    intro i
    have hk := le i
    omega

/-- Exact halving theorem for a homogeneous initial population of size 2u,
for any positive allowance r+1 and any number h of subsequent questions.
Both branches of a balanced first question have the displayed budget. -/
theorem homogeneous_halving (h r u k : ℕ)
    (hYes : Solvable h (childBudget (size := fun _ : Unit => 2 * u)
      (fun _ => r) (fun _ => k)))
    (hNo : Solvable h (childBudget (size := fun _ : Unit => 2 * u)
      (fun _ => r) (fun _ => 2 * u - k))) :
    Solvable h (childBudget (size := fun _ : Unit => 2 * u)
      (fun _ => r) (fun _ => u)) := by
  apply same_sign_halving (C := Unit) h (fun _ => r) (fun _ => u) (fun _ => k)
    hYes hNo
  rcases Nat.le_total u k with hk | hk
  · exact Or.inl (fun _ => hk)
  · exact Or.inr (fun _ => hk)

end LiarGameHomogeneous
