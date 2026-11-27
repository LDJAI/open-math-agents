import RankingDecision

namespace AdaptiveRanking
open scoped BigOperators

variable {A E : Type*} [DecidableEq A] [DecidableEq E]

/-- Each recorded answer earns one extra point precisely when the ranking respects it. -/
def kept (dir : A → E → Bool) (a : A) : List (E × Bool) → ℕ
  | [] => 0
  | p :: ps => kept dir a ps + if dir a p.1 = p.2 then 1 else 0

omit [DecidableEq A] [DecidableEq E] in
theorem kept_le (dir : A → E → Bool) (a : A) (past : List (E × Bool)) :
    kept dir a past ≤ past.length := by
  induction past with
  | nil => simp [kept]
  | cons p ps ih =>
    simp only [kept, List.length_cons]
    split <;> omega

omit [DecidableEq A] [DecidableEq E] in
theorem kept_full (dir : A → E → Bool) (a : A) (past : List (E × Bool)) :
    kept dir a past = past.length ↔ ∀ p ∈ past, dir a p.1 = p.2 := by
  induction past with
  | nil => simp [kept]
  | cons p ps ih =>
    simp only [kept, List.length_cons, List.forall_mem_cons]
    have hl := kept_le dir a ps
    by_cases h : dir a p.1 = p.2
    · simp [h, ih]
    · simp [h]; omega

/-- The algorithm's only data-dependent operation is to threshold the next oracle answer. -/
def run (estimate : List (E × Bool) → E → ℚ) :
    List E → List (E × Bool) → List (E × Bool)
  | [], past => past
  | e :: todo, past =>
      run estimate todo ((e, decide ((1:ℚ)/2 ≤ estimate past e)) :: past)

def bestExtension (s : Finset A) (score : A → ℕ) (best : ℕ) (dir : A → E → Bool)
    (past : List (E × Bool)) : Prop :=
  ∃ a ∈ s, score a = best ∧ ∀ p ∈ past, dir a p.1 = p.2

omit [DecidableEq E] in
/-- A pointwise approximation bound and the expectation bound suffice to take one step.
Here mass is the distribution of representative rankings for the current input. -/
theorem step (s : Finset A) (score : A → ℕ) (best : ℕ) (dir : A → E → Bool)
    (hbest : ∀ a ∈ s, score a ≤ best) (past : List (E × Bool)) (e : E)
    (mass : A → ℚ) (est : ℚ) (hnonneg : ∀ a ∈ s, 0 ≤ mass a)
    (hnorm : ∑ a ∈ s, mass a = 1)
    (hregret : (∑ a ∈ s, mass a *
        ((best + past.length - (score a + kept dir a past) : ℕ) : ℚ)) < 1/4)
    (herror : |(∑ a ∈ s.filter (fun a => dir a e = true), mass a) - est| ≤ 1/4) :
    bestExtension s score best dir ((e, decide ((1:ℚ)/2 ≤ est)) :: past) := by
  let chosen := decide ((1:ℚ)/2 ≤ est)
  let selected := s.filter (fun a => dir a e = chosen)
  let yes := ∑ a ∈ s.filter (fun a => dir a e = true), mass a
  have hquarter := RankingDecision.quarter_oracle_branch yes est herror
  have hpartition : yes + (∑ a ∈ s.filter (fun a => dir a e = false), mass a) = 1 := by
    rw [← hnorm]
    simpa [yes] using Finset.sum_filter_add_sum_filter_not s (fun a => dir a e = true) mass
  have hm : (1:ℚ)/4 ≤ ∑ a ∈ selected, mass a := by
    by_cases hh : (1:ℚ)/2 ≤ est
    · rw [if_pos hh] at hquarter
      have hc : chosen = true := decide_eq_true hh
      simpa only [selected, hc, yes] using hquarter
    · rw [if_neg hh] at hquarter
      have hc : chosen = false := decide_eq_false hh
      simp only [selected, hc]
      linarith
  let val := fun a => score a + kept dir a past
  have hv : ∀ a ∈ s, val a ≤ best + past.length := by
    intro a ha
    exact Nat.add_le_add (hbest a ha) (kept_le dir a past)
  obtain ⟨a, ha, he⟩ :=
    RankingDecision.orientation_contains_optimum s selected (Finset.filter_subset ..)
      mass hnonneg val (best+past.length) hv (hregret.trans_le hm)
  obtain ⟨has, had⟩ := Finset.mem_filter.mp ha
  have h1 := hbest a has
  have h2 := kept_le dir a past
  change score a + kept dir a past = best + past.length at he
  refine ⟨a, has, by omega, ?_⟩
  exact List.forall_mem_cons.mpr ⟨had, (kept_full dir a past).mp (by omega)⟩

/-- The laws are required only at prefixes already realized by a true optimum.
They describe the quantitative obligations supplied by the cloned Gibbs model. -/
structure OracleLaws (s : Finset A) (score : A → ℕ) (best : ℕ)
    (dir : A → E → Bool) (estimate : List (E × Bool) → E → ℚ) where
  mass : List (E × Bool) → A → ℚ
  nonneg : ∀ ps a, a ∈ s → 0 ≤ mass ps a
  norm : ∀ ps, ∑ a ∈ s, mass ps a = 1
  regret : ∀ ps, bestExtension s score best dir ps →
    (∑ a ∈ s, mass ps a *
      ((best+ps.length - (score a + kept dir a ps) : ℕ) : ℚ)) < 1/4
  error : ∀ ps, bestExtension s score best dir ps → ∀ e,
    |(∑ a ∈ s.filter (fun a => dir a e = true), mass ps a) - estimate ps e| ≤ 1/4

omit [DecidableEq E] in
theorem run_has_best (s : Finset A) (score : A → ℕ) (best : ℕ)
    (dir : A → E → Bool) (estimate : List (E × Bool) → E → ℚ)
    (hbest : ∀ a ∈ s, score a ≤ best) (laws : OracleLaws s score best dir estimate)
    (todo : List E) (past : List (E × Bool)) (invariant : bestExtension s score best dir past) :
    bestExtension s score best dir (run estimate todo past) := by
  induction todo generalizing past with
  | nil => exact invariant
  | cons e es ih =>
    exact ih _ (step s score best dir hbest past e (laws.mass past) (estimate past e)
      (laws.nonneg past) (laws.norm past) (laws.regret past invariant) (laws.error past invariant e))

omit [DecidableEq E] in
theorem keeps_history (estimate : List (E × Bool) → E → ℚ)
    (todo : List E) (past : List (E × Bool)) :
    ∀ p ∈ past, p ∈ run estimate todo past := by
  induction todo generalizing past with
  | nil => simp [run]
  | cons e es ih =>
    intro p hp
    exact ih _ p (List.mem_cons_of_mem _ hp)

omit [DecidableEq E] in
theorem answers_all (estimate : List (E × Bool) → E → ℚ)
    (todo : List E) (past : List (E × Bool)) :
    ∀ e ∈ todo, ∃ b, (e,b) ∈ run estimate todo past := by
  induction todo generalizing past with
  | nil => simp
  | cons x xs ih =>
    intro e he
    rcases List.mem_cons.mp he with h | h
    · subst e
      exact ⟨_, keeps_history estimate xs _ _ (List.mem_cons_self)⟩
    · exact ih _ e h

/-- The output determines every queried comparison exactly as some optimizer orders it.
When the list contains all pairs, its tournament agreement score is the optimum. -/
theorem recover (s : Finset A) (score : A → ℕ) (best : ℕ) (dir : A → E → Bool)
    (estimate : List (E × Bool) → E → ℚ) (todo : List E)
    (hbest : ∀ a ∈ s, score a ≤ best) (hattain : ∃ a ∈ s, score a = best)
    (laws : OracleLaws s score best dir estimate) :
    ∃ a ∈ s, score a = best ∧ ∀ e ∈ todo,
      decide ((e,true) ∈ run estimate todo []) = dir a e := by
  obtain ⟨w, hw, hwb⟩ := hattain
  have init : bestExtension s score best dir [] := ⟨w, hw, hwb, by simp⟩
  obtain ⟨a, ha, hb, htail⟩ := run_has_best s score best dir estimate hbest laws todo [] init
  refine ⟨a, ha, hb, ?_⟩
  intro e he
  obtain ⟨b, hmem⟩ := answers_all estimate todo [] e he
  have hdir := htail (e,b) hmem
  by_cases ht : (e,true) ∈ run estimate todo []
  · have := htail (e,true) ht
    simpa [ht] using this.symm
  · have hbf : b = false := by cases b <;> simp_all
    simpa [ht, hbf] using hdir.symm

/-- Count matched tournament arcs directly from comparison answers. -/
def agreement (edges : Finset E) (dir tournament : E → Bool) : ℕ :=
  ∑ e ∈ edges, if dir e = tournament e then 1 else 0

/-- The program computes the optimum number of forward arcs from its output bits.
It does not have to enumerate the candidate rankings to decode its result. -/
theorem recover_optimal_score (s : Finset A) (dir : A → E → Bool) (tournament : E → Bool)
    (todo : List E) (estimate : List (E × Bool) → E → ℚ) (best : ℕ)
    (hbest : ∀ a ∈ s, agreement todo.toFinset (dir a) tournament ≤ best)
    (hattain : ∃ a ∈ s, agreement todo.toFinset (dir a) tournament = best)
    (laws : OracleLaws s (fun a => agreement todo.toFinset (dir a) tournament)
      best dir estimate) :
    agreement todo.toFinset (fun e => decide ((e,true) ∈ run estimate todo [])) tournament =
      best := by
  obtain ⟨a, _, ha, hs⟩ := recover s _ best dir estimate todo hbest hattain laws
  rw [← ha]
  apply Finset.sum_congr rfl
  intro e he
  exact congrArg (fun b => if b = tournament e then (1 : ℕ) else 0) (hs e (List.mem_toFinset.mp he))

end AdaptiveRanking

#print axioms AdaptiveRanking.step
#print axioms AdaptiveRanking.recover

#print axioms AdaptiveRanking.recover_optimal_score
