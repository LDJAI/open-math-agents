import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Real.Basic

/-!
# Highest-rival-price unit-demand auction

The first theorem proves dominant-strategy truthfulness for the actual mathematical
per-buyer choice rule. The fixed rival prices and priority flags are its inputs.
The second theorem proves the welfare bound for any matching, given the incidence
and winner facts about the itemwise highest-bid computation. It does not formalize
the graph-query data structure, random loads, or correspondence to the Python code.
-/

namespace LocalAuction

open Finset
open scoped BigOperators

variable {Item Buyer : Type*}

noncomputable def provisional (listed : Finset Item) (bid : ℝ)
    (price : Item → ℝ) (tieWins : Item → Prop) : Finset Item := by
  classical
  exact listed.filter (fun j => price j < bid ∨ price j = bid ∧ tieWins j)

theorem mem_provisional {listed : Finset Item} {bid : ℝ} {price : Item → ℝ}
    {tieWins : Item → Prop} {j : Item} :
    j ∈ provisional listed bid price tieWins ↔
      j ∈ listed ∧ (price j < bid ∨ price j = bid ∧ tieWins j) := by
  classical
  simp [provisional]

/-- Any least-price minimizer is sufficient. Buy an item whenever there is one. -/
noncomputable def cheapest (items : Finset Item) (price : Item → ℝ) : Option Item := by
  classical
  exact if h : items.Nonempty then some (items.exists_min_image price h).choose else none

def utility [DecidableEq Item] (actual : Finset Item) (value : ℝ) (price : Item → ℝ) : Option Item → ℝ
  | none => 0
  | some j => (if j ∈ actual then value else 0) - price j

/-- Even an unrestricted choice of alternative outcome cannot beat the truthful
outcome if the prices are fixed by the other buyers. In particular this holds for
the outcome from changing both the report's list and the report's bid. -/
theorem truthful_menu [DecidableEq Item] (actual : Finset Item) (value : ℝ) (price : Item → ℝ)
    (tieWins : Item → Prop) (nonneg : ∀ j, 0 ≤ price j) (alternative : Option Item) :
    utility actual value price alternative ≤
      utility actual value price (cheapest (provisional actual value price tieWins) price) := by
  classical
  let won := provisional actual value price tieWins
  change _ ≤ utility actual value price (cheapest won price)
  by_cases h : won.Nonempty
  · let j := (won.exists_min_image price h).choose
    have hj : j ∈ won := (won.exists_min_image price h).choose_spec.1
    have hmin : ∀ x ∈ won, price j ≤ price x := (won.exists_min_image price h).choose_spec.2
    have hactual := (mem_provisional.mp hj)
    have hjprice : price j ≤ value := hactual.2.elim le_of_lt (fun t => le_of_eq t.1)
    have hir : 0 ≤ value - price j := sub_nonneg.mpr hjprice
    rw [show cheapest won price = some j by simp [cheapest, h, j]]
    simp only [utility, if_pos hactual.1]
    cases alternative with
    | none => exact hir
    | some x =>
      by_cases hx : x ∈ actual
      · by_cases hxprice : price x < value
        · have hw : x ∈ won := mem_provisional.mpr ⟨hx, Or.inl hxprice⟩
          simpa [utility, hx] using sub_le_sub_left (hmin x hw) value
        · simpa [utility, hx] using
            (sub_nonpos.mpr (le_of_not_gt hxprice)).trans hir
      · simpa [utility, hx] using (neg_nonpos.mpr (nonneg x)).trans hir
  · rw [show cheapest won price = none by simp [cheapest, h]]
    cases alternative with
    | none => rfl
    | some x =>
      by_cases hx : x ∈ actual
      · have hxp : ¬ price x < value := fun hp =>
          h ⟨x, mem_provisional.mpr ⟨hx, Or.inl hp⟩⟩
        simpa [utility, hx] using (sub_nonpos.mpr (le_of_not_gt hxp))
      · simpa [utility, hx] using neg_nonpos.mpr (nonneg x)

/-- Charge any comparison matching's items to highest bidders. Every item has
a champion who wins one acceptable item, lists this item, and has at least the
comparison buyer's value. Each buyer lists at most k items. -/
theorem welfare_bound (items : Finset Item) (winners : Finset Buyer)
    (listed : Buyer → Finset Item) (champ benchmark : Item → Buyer)
    (value : Buyer → ℝ) (k : ℕ)
    (wins : ∀ j ∈ items, champ j ∈ winners)
    (wants : ∀ j ∈ items, j ∈ listed (champ j))
    (highest : ∀ j ∈ items, value (benchmark j) ≤ value (champ j))
    (sparse : ∀ i ∈ winners, (listed i).card ≤ k)
    (nonneg : ∀ i ∈ winners, 0 ≤ value i) :
    ∑ j ∈ items, value (benchmark j) ≤ (k : ℝ) * ∑ i ∈ winners, value i := by
  classical
  calc
    ∑ j ∈ items, value (benchmark j) ≤ ∑ j ∈ items, value (champ j) :=
      Finset.sum_le_sum highest
    _ = ∑ i ∈ winners, ∑ j ∈ items with champ j = i, value (champ j) :=
      (Finset.sum_fiberwise_of_maps_to wins (fun j => value (champ j))).symm
    _ ≤ ∑ i ∈ winners, (k : ℝ) * value i := by
      apply Finset.sum_le_sum
      intro i hi
      let fiber := items.filter (fun j => champ j = i)
      have es : ∀ j ∈ fiber, champ j = i := fun j hj => (Finset.mem_filter.mp hj).2
      have sub : fiber ⊆ listed i := by
        intro j hj
        rw [← es j hj]
        exact wants j (Finset.mem_filter.mp hj).1
      have bound : fiber.card ≤ k := (Finset.card_le_card sub).trans (sparse i hi)
      calc
        ∑ j ∈ fiber, value (champ j) = ∑ _j ∈ fiber, value i :=
          Finset.sum_congr rfl (fun j hj => congrArg value (es j hj))
        _ = (fiber.card : ℝ) * value i := by simp [nsmul_eq_mul]
        _ ≤ (k : ℝ) * value i :=
          mul_le_mul_of_nonneg_right (Nat.cast_le.mpr bound) (nonneg i hi)
    _ = (k : ℝ) * ∑ i ∈ winners, value i := (Finset.mul_sum ..).symm

/-- Express the welfare bound using the actual item choices, not only the list of
winners. The hypothesis on each comparison item supplies its highest bidder and
certifies this bidder's eligibility at the rivals' prices. -/
theorem welfare_of_choices [DecidableEq Item] (buyers : Finset Buyer) (items : Finset Item)
    (listed : Buyer → Finset Item) (value : Buyer → ℝ) (k : ℕ)
    (price : Buyer → Item → ℝ) (tieWins : Buyer → Item → Prop)
    (champ benchmark : Item → Buyer)
    (present : ∀ j ∈ items, champ j ∈ buyers)
    (eligible : ∀ j ∈ items,
      j ∈ provisional (listed (champ j)) (value (champ j)) (price (champ j)) (tieWins (champ j)))
    (highest : ∀ j ∈ items, value (benchmark j) ≤ value (champ j))
    (sparse : ∀ i ∈ buyers, (listed i).card ≤ k)
    (nonneg : ∀ i ∈ buyers, 0 ≤ value i) :
    ∑ j ∈ items, value (benchmark j) ≤ (k : ℝ) * ∑ i ∈ buyers,
      (match cheapest (provisional (listed i) (value i) (price i) (tieWins i)) (price i) with
      | none => 0
      | some item => if item ∈ listed i then value i else 0) := by
  classical
  let offers := fun i => provisional (listed i) (value i) (price i) (tieWins i)
  let winners := buyers.filter (fun i => (offers i).Nonempty)
  have bound := welfare_bound items winners listed champ benchmark value k
    (fun j hj => Finset.mem_filter.mpr ⟨present j hj, ⟨j, eligible j hj⟩⟩)
    (fun j hj => (mem_provisional.mp (eligible j hj)).1) highest
    (fun i hi => sparse i (Finset.mem_filter.mp hi).1)
    (fun i hi => nonneg i (Finset.mem_filter.mp hi).1)
  apply bound.trans_eq
  congr 1
  dsimp only [winners]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  change (if (offers i).Nonempty then value i else 0) =
    (match cheapest (offers i) (price i) with
    | none => 0
    | some item => if item ∈ listed i then value i else 0)
  by_cases h : (offers i).Nonempty
  · have hm := ((offers i).exists_min_image (price i) h).choose_spec.1
    have hl := (mem_provisional.mp hm).1
    simp [cheapest, h, hl]
  · simp [cheapest, h]

end LocalAuction
