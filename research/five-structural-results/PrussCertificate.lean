import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Range
import Mathlib.Tactic.Choose

/-! The finite-trace obstruction and truncation step for Pruss's question. -/

namespace PrussDiagonal

abbrev Classifier (α : Type*) := ℕ → Finset α

def fitsBlock {α : Type*} (x : ℕ → ℕ × α) (a : Classifier α) (j n : ℕ) : Prop :=
  ∀ k < n, (x k).1 = j → (x k).2 ∈ a j

/-- If every proposed piece misses some finite sample on its assigned block,
there is one classifier in none of the proposed pieces. -/
theorem missing_coverage {α : Type*} (x : ℕ → ℕ × α)
    (G : ℕ → Set (Classifier α))
    (h : ∀ j, ∃ n, ∀ a ∈ G j, ¬ fitsBlock x a j n) :
    ∃ a : Classifier α, ∀ j, a ∉ G j := by
  classical
  choose n hn using h
  let a : Classifier α := fun j =>
    ((Finset.range (n j)).filter (fun k => (x k).1 = j)).image (fun k => (x k).2)
  refine ⟨a, fun j hj => hn j a hj ?_⟩
  intro k hk hkj
  apply Finset.mem_image.mpr
  exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hkj⟩, rfl⟩

/-- A vanishing uniform error cannot fit every sample in a positive-mass
block at every size. The masses and errors are supplied as real sequences. -/
theorem eventually_misses {α : Type*} (x : ℕ → ℕ × α) (G : Set (Classifier α))
    (j : ℕ) (mass err : ℕ → ℝ) (p : ℝ) (hp : 0 < p)
    (hmass : Filter.Tendsto mass Filter.atTop (nhds p))
    (herr : Filter.Tendsto err Filter.atTop (nhds 0))
    (hfit : ∀ n, ∀ a ∈ G, fitsBlock x a j n → mass n ≤ err n) :
    ∃ n, ∀ a ∈ G, ¬ fitsBlock x a j n := by
  have hev : ∀ᶠ n in Filter.atTop, err n < mass n :=
    Filter.Tendsto.eventually_lt herr hmass hp
  obtain ⟨n, hn⟩ := hev.exists
  exact ⟨n, fun a ha hf => (not_le_of_gt hn) (hfit n a ha hf)⟩

/-- The sampled indices falling in one block. -/
def onBlock {α : Type*} (x : ℕ → ℕ × α) (j n : ℕ) : Finset ℕ :=
  (Finset.range n).filter fun k => (x k).1 = j

/-- The sampled indices accepted by a classifier. -/
noncomputable def accepted {α : Type*} (x : ℕ → ℕ × α)
    (a : Classifier α) (n : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range n).filter fun k => (x k).2 ∈ a (x k).1

/-- A sample path with positive limiting frequencies in every block defeats
any proposed countable cover whose empirical masses converge uniformly to zero. -/
theorem no_countable_uniform_cover {α : Type*} (x : ℕ → ℕ × α)
    (G : ℕ → Set (Classifier α)) (p : ℕ → ℝ) (err : ℕ → ℕ → ℝ)
    (hp : ∀ j, 0 < p j)
    (hmass : ∀ j, Filter.Tendsto (fun n => ((onBlock x j n).card : ℝ) / n)
      Filter.atTop (nhds (p j)))
    (herr : ∀ j, Filter.Tendsto (err j) Filter.atTop (nhds 0))
    (hupper : ∀ j n a, a ∈ G j → ((accepted x a n).card : ℝ) / n ≤ err j n) :
    ∃ a : Classifier α, ∀ j, a ∉ G j := by
  classical
  apply missing_coverage x G
  intro j
  apply eventually_misses x (G j) j _ (err j) (p j) (hp j) (hmass j) (herr j)
  intro n a ha hfit
  have hsub : onBlock x j n ⊆ accepted x a n := by
    intro k hk
    obtain ⟨hkn, hkj⟩ := Finset.mem_filter.mp hk
    apply Finset.mem_filter.mpr
    exact ⟨hkn, hkj ▸ hfit k (Finset.mem_range.mp hkn) hkj⟩
  have hc : ((onBlock x j n).card : ℝ) ≤ (accepted x a n).card := by
    exact_mod_cast Finset.card_le_card hsub
  exact (div_le_div_of_nonneg_right hc (Nat.cast_nonneg n)).trans (hupper j n a ha)

/-- Pointwise errors vanish when each finite prefix error vanishes and the
two tail masses converge to a common quantity which tends to zero. -/
theorem truncate {ι : Type*} (err : ι → ℕ → ℝ) (head : ι → ℕ → ℕ → ℝ)
    (sampleTail : ℕ → ℕ → ℝ) (trueTail : ℕ → ℝ)
    (hnonneg : ∀ a n, 0 ≤ err a n)
    (hbound : ∀ a J n, err a n ≤ head a J n + max (sampleTail J n) (trueTail J))
    (hhead : ∀ a J, Filter.Tendsto (head a J) Filter.atTop (nhds 0))
    (hsample : ∀ J, Filter.Tendsto (sampleTail J) Filter.atTop (nhds (trueTail J)))
    (htail : Filter.Tendsto trueTail Filter.atTop (nhds 0)) :
    ∀ a, Filter.Tendsto (err a) Filter.atTop (nhds 0) := by
  intro a
  apply tendsto_order.2
  constructor
  · intro b hb
    exact Filter.Eventually.of_forall fun n => lt_of_lt_of_le hb (hnonneg a n)
  · intro b hb
    obtain ⟨J, hJ⟩ := (htail.eventually_lt_const hb).exists
    have hmajor : Filter.Tendsto
        (fun n => head a J n + max (sampleTail J n) (trueTail J))
        Filter.atTop (nhds (trueTail J)) := by
      simpa using (hhead a J).add ((hsample J).max (tendsto_const_nhds (x := trueTail J)))
    filter_upwards [hmajor.eventually_lt_const hJ] with n hn
    exact lt_of_le_of_lt (hbound a J n) hn

#print axioms missing_coverage
#print axioms eventually_misses
#print axioms no_countable_uniform_cover
#print axioms truncate

end PrussDiagonal
