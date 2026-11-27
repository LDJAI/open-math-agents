import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Fin

/-!
# Switching arcs of a cycle

For each edge, record the finite set of demands which use it. On a simple
cycle, replacing a demand's arc by the complementary arc toggles membership
at every edge. The theorem below verifies the resulting capacity calculation.
-/

namespace OrderedTrails

variable {Demand Edge : Type*} [DecidableEq Demand]

/-- Users of an edge after each demand in `switched` takes its complementary arc. -/
def switchedUsers (users switched : Finset Demand) : Finset Demand :=
  (users \ switched) ∪ (switched \ users)

/-- Switching any collection of demands increases the load of an edge
by at most the number of demands switched. -/
theorem switchedUsers_card_le (users switched : Finset Demand) :
    (switchedUsers users switched).card ≤ users.card + switched.card := by
  calc
    _ ≤ (users \ switched).card + (switched \ users).card := Finset.card_union_le _ _
    _ ≤ users.card + switched.card :=
      Nat.add_le_add (Finset.card_le_card Finset.sdiff_subset)
        (Finset.card_le_card Finset.sdiff_subset)

/-- Repair a distinguished edge of load `a` and capacity `c ≤ a`.
If every other edge has initial load at most `k - a` and capacity at least
`k - c`, all capacities hold after switching exactly `a - c` routes. -/
theorem repair_cycle_routing (users : Edge → Finset Demand)
    (capacity : Edge → ℕ) (e : Edge) (k : ℕ)
    (over : capacity e ≤ (users e).card)
    (size : (users e).card ≤ k)
    (otherLoad : ∀ f, f ≠ e → (users f).card ≤ k - (users e).card)
    (otherCapacity : ∀ f, f ≠ e → k - capacity e ≤ capacity f) :
    ∃ switched ⊆ users e,
      switched.card = (users e).card - capacity e ∧
      (switchedUsers (users e) switched).card = capacity e ∧
      ∀ f, (switchedUsers (users f) switched).card ≤ capacity f := by
  obtain ⟨s, hs, hcard⟩ := Finset.exists_subset_card_eq
    (Nat.sub_le (users e).card (capacity e))
  have fixedLoad : (switchedUsers (users e) s).card = capacity e := by
    rw [switchedUsers, Finset.sdiff_eq_empty_iff_subset.mpr hs,
      Finset.union_empty, Finset.card_sdiff_of_subset hs, hcard]
    omega
  refine ⟨s, hs, hcard, fixedLoad, fun f => ?_⟩
  by_cases h : f = e
  · simpa [h] using fixedLoad.le
  · have bound := switchedUsers_card_le (users f) s
    have initial := otherLoad f h
    have cap := otherCapacity f h
    omega

#print axioms repair_cycle_routing

end OrderedTrails

namespace OrderedTrails

variable {Demand Edge : Type*} [DecidableEq Demand]

private theorem fit_or_repair (users : Edge → Finset Demand) (cap : Edge → ℕ)
    (e : Edge) (k : ℕ)
    (size : (users e).card ≤ k)
    (minimum : ∀ f, cap e ≤ cap f)
    (cuts : ∀ f, f ≠ e → k ≤ cap e + cap f)
    (span : ∀ f, (users f).card ≤ (users e).card + 1)
    (room : ∀ f, f ≠ e → (users f).card ≤ k - (users e).card) :
    ∃ s ⊆ users e, ∀ f, (switchedUsers (users f) s).card ≤ cap f := by
  by_cases overloaded : cap e ≤ (users e).card
  · have capRoom (f : Edge) (h : f ≠ e) : k - cap e ≤ cap f := by
      have := cuts f h
      omega
    obtain ⟨s, hs, _, _, good⟩ :=
      repair_cycle_routing users cap e k overloaded size room capRoom
    exact ⟨s, hs, good⟩
  · refine ⟨∅, Finset.empty_subset _, fun f => ?_⟩
    simp only [switchedUsers, Finset.sdiff_empty, Finset.empty_sdiff, Finset.union_empty]
    have := span f
    have := minimum f
    omega

private theorem complement_switch (U A S : Finset Demand) (hA : A ⊆ U) (hS : S ⊆ U) :
    switchedUsers (U \ A) S = switchedUsers A (U \ S) := by
  ext x
  by_cases hx : x ∈ U
  · simp only [switchedUsers, Finset.mem_union, Finset.mem_sdiff, hx, true_and]
    tauto
  · have ha : x ∉ A := fun h => hx (hA h)
    have hs : x ∉ S := fun h => hx (hS h)
    simp [switchedUsers, hx, ha, hs]

/-- Suppose the loads induced by choosing all clockwise arcs differ by at most
one. A cut separating the endpoints of two cycle edges has capacity at least
`k`, and there are at most `k` demands. Then there exists a simultaneous
choice of clockwise or complementary arcs routing every demand within capacity.

The input records the users of each edge for the all-clockwise choice and one
edge `e` of minimum capacity. The output is exactly the set of demands which
should take the opposite arc. -/
theorem route_of_span_one (U : Finset Demand) (users : Edge → Finset Demand)
    (cap : Edge → ℕ) (e : Edge) (k : ℕ)
    (contained : ∀ f, users f ⊆ U) (size : U.card ≤ k)
    (minimum : ∀ f, cap e ≤ cap f)
    (cuts : ∀ f, f ≠ e → k ≤ cap e + cap f)
    (span : ∀ f g, (users f).card ≤ (users g).card + 1) :
    ∃ s ⊆ U, ∀ f, (switchedUsers (users f) s).card ≤ cap f := by
  have useCard (f : Edge) : (users f).card ≤ U.card := Finset.card_le_card (contained f)
  have forward (room : ∀ f, (users f).card ≤ k - (users e).card) :
      ∃ s ⊆ U, ∀ f, (switchedUsers (users f) s).card ≤ cap f := by
    obtain ⟨s, hs, ok⟩ := fit_or_repair users cap e k
      ((useCard e).trans size) minimum cuts (fun f => span f e) (fun f _ => room f)
    exact ⟨s, hs.trans (contained e), ok⟩
  by_cases room : ∀ f, (users f).card ≤ k - (users e).card
  · exact forward room
  push Not at room
  obtain ⟨g, hg⟩ := room
  let back (f : Edge) := U \ users f
  have backwardCount (f : Edge) : (back f).card = U.card - (users f).card :=
    Finset.card_sdiff_of_subset (contained f)
  have backSmall : (back e).card ≤ k := by rw [backwardCount]; omega
  have backSpan (f : Edge) : (back f).card ≤ (back e).card + 1 := by
    rw [backwardCount, backwardCount]
    have := span e f
    have := useCard e
    have := useCard f
    omega
  have backRoom (f : Edge) (_ : f ≠ e) : (back f).card ≤ k - (back e).card := by
    rw [backwardCount, backwardCount]
    have := span g f
    have := useCard e
    have := useCard f
    omega
  obtain ⟨s, hs, ok⟩ := fit_or_repair back cap e k backSmall minimum cuts backSpan backRoom
  have sU : s ⊆ U := hs.trans Finset.sdiff_subset
  refine ⟨U \ s, Finset.sdiff_subset, fun f => ?_⟩
  rw [← complement_switch U (users f) s (contained f) sU]
  exact ok f

#print axioms route_of_span_one

end OrderedTrails


/-!
# Loads of clockwise arcs along an ordered demand chain

The vertices and links of an n-cycle are labelled from 0 to n−1, with
link e leaving vertex e in clockwise direction. The formula below also
works on arbitrary natural labels. A zero-length hop uses no clockwise link.
-/

namespace OrderedCycle

/-- The clockwise arc from vertex `s` to vertex `t` uses link `e`. -/
def clockwise (s t e : ℕ) : Prop :=
  if s ≤ t then s ≤ e ∧ e < t else s ≤ e ∨ e < t

instance (s t e : ℕ) : Decidable (clockwise s t e) := by
  unfold clockwise
  split <;> infer_instance

/-- All demand indices using link `e` along their clockwise arc. -/
def users (v : ℕ → ℕ) (m e : ℕ) : Finset ℕ :=
  (Finset.range m).filter (fun i => clockwise (v i) (v (i + 1)) e)

/-- The number of times a hop wraps around label zero. -/
def wraps (v : ℕ → ℕ) (m : ℕ) : ℕ :=
  ((Finset.range m).filter (fun i => v (i + 1) < v i)).card

private theorem next_load (v : ℕ → ℕ) (m e : ℕ) :
    (users v (m + 1) e).card = (users v m e).card +
      (if clockwise (v m) (v (m + 1)) e then 1 else 0) := by
  by_cases hc : clockwise (v m) (v (m + 1)) e <;>
    simp [users, Finset.range_add_one, Finset.filter_insert, hc]

private theorem next_wraps (v : ℕ → ℕ) (m : ℕ) :
    wraps v (m + 1) = wraps v m + (if v (m + 1) < v m then 1 else 0) := by
  by_cases h : v (m + 1) < v m <;>
    simp [wraps, Finset.range_add_one, Finset.filter_insert, h]

private theorem one_hop (s t e : ℕ) :
    (if clockwise s t e then 1 else 0) + (if t ≤ e then 1 else 0) =
      (if t < s then 1 else 0) + (if s ≤ e then 1 else 0) := by
  unfold clockwise
  split_ifs <;> omega

/-- All internal terminals cancel from the clockwise load. -/
theorem telescoping_load (v : ℕ → ℕ) (m e : ℕ) :
    (users v m e).card + (if v m ≤ e then 1 else 0) =
      wraps v m + (if v 0 ≤ e then 1 else 0) := by
  induction m with
  | zero => simp [users, wraps]
  | succ m ih =>
    rw [next_load, next_wraps]
    have hop := one_hop (v m) (v (m + 1)) e
    omega

/-- The loads of any two links differ by at most one. -/
theorem load_span (v : ℕ → ℕ) (m e f : ℕ) :
    (users v m e).card ≤ (users v m f).card + 1 := by
  have he := telescoping_load v m e
  have hf := telescoping_load v m f
  split_ifs at he hf <;> omega

#print axioms load_span

end OrderedCycle

namespace OrderedCycle

private theorem opposite_arcs_disjoint (s t e : ℕ) :
    clockwise t s e → ¬clockwise s t e := by
  unfold clockwise
  split_ifs <;> omega

/-- On a ring with at least three vertices, if every pair of distinct physical
links has combined capacity at least the number of demands, the ordered
chain admits a routing by clockwise and counterclockwise arcs. Each demand
takes exactly one of these two directions. Repeated vertices are permitted. -/
theorem route_ordered_ring {n : ℕ} (hn : 3 ≤ n) (m : ℕ)
    (v : ℕ → Fin n) (cap : Fin n → ℕ)
    (cuts : ∀ e f : Fin n, f ≠ e → m ≤ cap e + cap f) :
    ∃ s ⊆ Finset.range m, ∀ f : Fin n,
      ((Finset.range m).filter (fun i =>
        if i ∈ s then clockwise (v (i + 1)).val (v i).val f.val
        else clockwise (v i).val (v (i + 1)).val f.val)).card ≤ cap f := by
  let : NeZero n := ⟨by omega⟩
  obtain ⟨e, _, he⟩ := Finset.exists_min_image Finset.univ cap Finset.univ_nonempty
  let w (i : ℕ) := (v i).val
  obtain ⟨s, hs, good⟩ := OrderedTrails.route_of_span_one
    (Finset.range m) (fun f : Fin n => users w m f.val) cap e m
    (fun _ => Finset.filter_subset _ _) (by simp)
    (fun f => he f (Finset.mem_univ f)) (cuts e)
    (fun f g => load_span w m f.val g.val)
  refine ⟨s, hs, fun f => (Finset.card_le_card ?_).trans (good f)⟩
  intro i hi
  obtain ⟨hir, harc⟩ := Finset.mem_filter.mp hi
  by_cases h : i ∈ s
  · have rev : clockwise (w (i + 1)) (w i) f.val := by simpa [h, w] using harc
    have neg := opposite_arcs_disjoint (w i) (w (i + 1)) f.val rev
    simp [OrderedTrails.switchedUsers, users, h, neg]
  · have pos : clockwise (w i) (w (i + 1)) f.val := by simpa [h, w] using harc
    simp [OrderedTrails.switchedUsers, users, hir, h, pos]

#print axioms route_ordered_ring

end OrderedCycle
