import Mathlib.Data.Fintype.Powerset

/-! A restricted SAT representation bound. A variable is false when it belongs to its
set of zeros. A graph CNF has one positive clause (u ∨ v) per edge. The encoding below
splits the vertices and edges at a cut. It makes no claim about general SAT decision. -/

namespace ResidualStateBound

structure CutGraph (α β : Type*) where
  prefixEdge : α → α → Prop
  crossEdge : α → β → Prop
  suffixEdge : β → β → Prop

def CutGraph.accepts (g : CutGraph α β) (p : Set α) (q : Set β) : Prop :=
  (∀ a ∈ p, ∀ b ∈ p, ¬g.prefixEdge a b) ∧
  (∀ a ∈ p, ∀ b ∈ q, ¬g.crossEdge a b) ∧
  (∀ a ∈ q, ∀ b ∈ q, ¬g.suffixEdge a b)

structure MatchingProbe (g : CutGraph α β) (ι : Type*) where
  left : ι → α
  right : ι → β
  independentLeft : ∀ i j, ¬g.prefixEdge (left i) (left j)
  diagonalCross : ∀ i j, g.crossEdge (left i) (right j) ↔ i = j
  looplessRight : ∀ i, ¬g.suffixEdge (right i) (right i)

theorem probe_iff (g : CutGraph α β) (m : MatchingProbe g ι) (s : Set ι) (j : ι) :
    g.accepts (m.left '' s) {m.right j} ↔ j ∉ s := by
  constructor
  · intro h hj
    exact h.2.1 (m.left j) ⟨j, hj, rfl⟩ (m.right j) rfl ((m.diagonalCross j j).2 rfl)
  · intro hj
    refine ⟨?_, ?_, ?_⟩
    · rintro _ ⟨i, _, rfl⟩ _ ⟨k, _, rfl⟩
      exact m.independentLeft i k
    · rintro _ ⟨i, hi, rfl⟩ _ rfl hcross
      exact hj ((m.diagonalCross i j).1 hcross ▸ hi)
    · rintro _ rfl _ rfl
      exact m.looplessRight j

/-- Every exact summary of prefix assignments has a different state for every
subset of matched vertices. The decoder may perform arbitrary computations. -/
theorem state_injective (g : CutGraph α β) (m : MatchingProbe g ι)
    (state : Set α → σ) (finish : σ → Set β → Prop)
    (correct : ∀ p q, finish (state p) q ↔ g.accepts p q) :
    Function.Injective (fun s : Set ι => state (m.left '' s)) := by
  intro s t hst
  apply Set.ext
  intro j
  have hs := (correct (m.left '' s) {m.right j}).trans (probe_iff g m s j)
  have ht := (correct (m.left '' t) {m.right j}).trans (probe_iff g m t j)
  change state (m.left '' s) = state (m.left '' t) at hst
  rw [hst] at hs
  exact not_iff_not.mp (hs.symm.trans ht)

/-- The number of reachable distinctions is at least 2^k at a matching probe of size k. -/
theorem finite_state_bound (g : CutGraph α β) (m : MatchingProbe g (Fin k))
    [Fintype σ] (state : Set α → σ) (finish : σ → Set β → Prop)
    (correct : ∀ p q, finish (state p) q ↔ g.accepts p q) :
    2 ^ k ≤ Fintype.card σ := by
  classical
  simpa using Fintype.card_le_of_injective _ (state_injective g m state finish correct)

/-- The formulas above have the uniform satisfying assignment with no zeros.
The state lower bound concerns retaining the entire residual truth function. -/
theorem has_model (g : CutGraph α β) : ∃ p q, g.accepts p q := by
  exact ⟨∅, ∅, by simp [CutGraph.accepts]⟩

/-- A concrete example at every width. For each i it has exactly the clause x_i ∨ y_i. -/
def paired (k : Nat) : CutGraph (Fin k) (Fin k) where
  prefixEdge := fun _ _ => False
  crossEdge := Eq
  suffixEdge := fun _ _ => False

def pairedProbe (k : Nat) : MatchingProbe (paired k) (Fin k) where
  left := id
  right := id
  independentLeft := by intro i j; exact id
  diagonalCross := by intro i j; exact Iff.rfl
  looplessRight := by intro i; exact id

theorem paired_lower_bound (k : Nat) [Fintype σ]
    (state : Set (Fin k) → σ) (finish : σ → Set (Fin k) → Prop)
    (correct : ∀ p q, finish (state p) q ↔ (paired k).accepts p q) :
    2 ^ k ≤ Fintype.card σ :=
  finite_state_bound (paired k) (pairedProbe k) state finish correct

/-- Storing the k-bit input mask attains the bound exactly. -/
theorem paired_upper_bound (k : Nat) :
    ∃ (state : Set (Fin k) → Set (Fin k))
      (finish : Set (Fin k) → Set (Fin k) → Prop),
      (∀ p q, finish (state p) q ↔ (paired k).accepts p q) ∧
      Fintype.card (Set (Fin k)) = 2 ^ k := by
  exact ⟨id, (paired k).accepts, fun _ _ => Iff.rfl, by simp⟩

end ResidualStateBound

#print axioms ResidualStateBound.finite_state_bound
#print axioms ResidualStateBound.paired_lower_bound
#print axioms ResidualStateBound.paired_upper_bound
#print axioms ResidualStateBound.has_model
