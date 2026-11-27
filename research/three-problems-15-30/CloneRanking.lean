import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Data.Fintype.Pi
import Mathlib.Logic.Equiv.Prod

/-! A clone is indexed by a finite set C. A transversal chooses one clone
for each candidate. Costs are rational, so the identities are exact. -/
namespace CloneRanking
open scoped BigOperators
open Finset

private theorem prod_average {X Y : Type*} [Fintype X] [Fintype Y]
    (g : X × Y → ℚ) : (𝔼 z, g z) = 𝔼 x, 𝔼 y, g (x,y) := by
  simpa only [univ_product_univ] using
    (expect_product (univ : Finset X) (univ : Finset Y) g)

private theorem one_coordinate {I C : Type*} [Fintype I] [DecidableEq I]
    [Fintype C] [Nonempty C] (i : I) (g : C → ℚ) :
    (𝔼 s : I → C, g (s i)) = 𝔼 a, g a := by
  classical
  let e := Equiv.funSplitAt i C
  calc
    _ = 𝔼 p : C × ({j : I // j ≠ i} → C), g p.1 :=
      Fintype.expect_equiv e _ _ (fun _ => rfl)
    _ = _ := by rw [prod_average]; simp [Fintype.expect_const]

/-- Uniformly sampling one representative of each candidate samples the
representatives of distinct candidates independently and uniformly. -/
theorem two_coordinates {I C : Type*} [Fintype I] [DecidableEq I]
    [Fintype C] [Nonempty C] (i j : I) (hji : j ≠ i) (g : C → C → ℚ) :
    (𝔼 s : I → C, g (s i) (s j)) = 𝔼 a, 𝔼 b, g a b := by
  classical
  let e := Equiv.funSplitAt i C
  let j' : {j : I // j ≠ i} := ⟨j,hji⟩
  calc
    _ = 𝔼 p : C × ({j : I // j ≠ i} → C), g p.1 (p.2 j') :=
      Fintype.expect_equiv e _ _ (fun _ => rfl)
    _ = _ := by rw [prod_average]; simp only [one_coordinate]

/-- Each directed edge contributes its pair cost. Thus the mean original
score of random transversals is exactly the clone score divided by |C|².
The right hand side takes the per-edge average explicitly. -/
theorem transversal_average {I C E : Type*} [Fintype I] [DecidableEq I]
    [Fintype C] [Nonempty C] (edges : Finset E) (src dst : E → I)
    (hne : ∀ e ∈ edges, dst e ≠ src e) (cost : E → C → C → ℚ) :
    (𝔼 s : I → C, ∑ e ∈ edges, cost e (s (src e)) (s (dst e))) =
    ∑ e ∈ edges, 𝔼 a, 𝔼 b, cost e a b := by
  rw [Finset.expect_sum_comm]
  exact sum_congr rfl (fun e he => two_coordinates _ _ (hne e he) _)

/-- In particular, interleaving clones cannot exceed the best original
ranking when the score is normalized by |C|². -/
theorem interleaving_bound {I C E : Type*} [Fintype I] [DecidableEq I]
    [Fintype C] [Nonempty C] (edges : Finset E) (src dst : E → I)
    (hne : ∀ e ∈ edges, dst e ≠ src e) (cost : E → C → C → ℚ) (best : ℚ)
    (hbest : ∀ s : I → C, (∑ e ∈ edges, cost e (s (src e)) (s (dst e))) ≤ best) :
    (∑ e ∈ edges, 𝔼 a, 𝔼 b, cost e a b) ≤ best := by
  rw [← transversal_average edges src dst hne cost]
  exact expect_le univ_nonempty (fun s _ => hbest s)

/-- When all clones of each candidate form a block, all copies of each
pair contribute the same cost, so the normalized score is attained. -/
theorem block_score {C E : Type*} [Fintype C] [Nonempty C]
    (edges : Finset E) (cost : E → ℚ) :
    (∑ e ∈ edges, 𝔼 _a : C, 𝔼 _b : C, cost e) = ∑ e ∈ edges, cost e := by
  simp only [Fintype.expect_const]

/-- Position numbers may have gaps; their only relevant feature is their
strict total ordering. Restricting an interleaved order to one clone per
candidate still gives an injective position map. -/
theorem restriction_injective {I C : Type*} (rank : I × C → ℕ)
    (hr : Function.Injective rank) (s : I → C) :
    Function.Injective (fun i => rank (i,s i)) :=
  fun _ _ h => congrArg Prod.fst (hr h)

/-- A block position assigns L consecutive slots to one candidate. -/
def blockPosition {I : Type*} (rank : I → ℕ) (L : ℕ) (p : I × Fin L) : ℕ :=
  rank p.1 * L + p.2.val

private theorem block_strict {L x y : ℕ} (h : x < y) (a b : Fin L) :
    x * L + a.val < y * L + b.val := by
  calc
    _ < x * L + L := Nat.add_lt_add_left a.isLt _
    _ = (x+1) * L := (Nat.succ_mul x L).symm
    _ ≤ y * L := Nat.mul_le_mul_right _ h
    _ ≤ _ := Nat.le_add_right _ _

theorem block_injective {I : Type*} (rank : I → ℕ) (hr : Function.Injective rank) (L : ℕ) :
    Function.Injective (blockPosition rank L) := by
  rintro ⟨i,a⟩ ⟨j,b⟩ h
  change rank i * L + a.val = rank j * L + b.val at h
  rcases lt_trichotomy (rank i) (rank j) with hlt | heq | hgt
  · exact False.elim ((block_strict hlt a b).ne h)
  · have hij := hr heq
    subst j
    have hab : a = b := Fin.ext (Nat.add_left_cancel h)
    subst b
    rfl
  · exact False.elim ((block_strict hgt b a).ne h.symm)

/-- The scaled optimum theorem for actual ranking positions. If best is the
optimum on the original candidates and is attained, it is the attained
optimum of the normalized cloned objective over *all* injective positions,
including arbitrary interleavings. -/
theorem clone_optimum {I E : Type*} [Fintype I] [DecidableEq I]
    (L : ℕ) [NeZero L] (edges : Finset E) (src dst : E → I)
    (hne : ∀ e ∈ edges, dst e ≠ src e) (w : E → ℚ) (best : ℚ)
    (htop : ∀ q : I → ℕ, Function.Injective q →
      (∑ e ∈ edges, if q (src e) < q (dst e) then w e else 0) ≤ best)
    (q : I → ℕ) (hq : Function.Injective q)
    (hatt : (∑ e ∈ edges, if q (src e) < q (dst e) then w e else 0) = best) :
    let value := fun r : I × Fin L → ℕ =>
      ∑ e ∈ edges, 𝔼 a : Fin L, 𝔼 b : Fin L,
        if r (src e,a) < r (dst e,b) then w e else 0
    (∀ r, Function.Injective r → value r ≤ best) ∧
      ∃ r, Function.Injective r ∧ value r = best := by
  dsimp only
  constructor
  · intro r hr
    apply interleaving_bound edges src dst hne
      (fun e a b => if r (src e,a) < r (dst e,b) then w e else 0) best
    exact fun s => htop _ (restriction_injective r hr s)
  · refine ⟨blockPosition q L, block_injective q hq L, ?_⟩
    rw [← hatt]
    apply Finset.sum_congr rfl
    intro e he
    have qne : q (src e) ≠ q (dst e) := fun h => hne e he (hq h).symm
    by_cases hlt : q (src e) < q (dst e)
    · have hh (a b : Fin L) :
          blockPosition q L (src e,a) < blockPosition q L (dst e,b) := block_strict hlt a b
      simp only [hh, hlt, if_true, Fintype.expect_const]
    · have hgt : q (dst e) < q (src e) := lt_of_le_of_ne (le_of_not_gt hlt) qne.symm
      have hh (a b : Fin L) :
          ¬ blockPosition q L (src e,a) < blockPosition q L (dst e,b) :=
        not_lt_of_gt (block_strict hgt b a)
      simp only [hh, hlt, if_false, Fintype.expect_const]

end CloneRanking

#print axioms CloneRanking.two_coordinates
#print axioms CloneRanking.transversal_average
#print axioms CloneRanking.interleaving_bound
#print axioms CloneRanking.block_score

#print axioms CloneRanking.clone_optimum
