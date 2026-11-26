import OMAStatements.S_mo_93022
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Tactic.FinCases

namespace OMA.S_mo_93022

def BoundedConnecting {n : ℕ} (f : Fin n → Fin n) : Prop :=
  ∀ p q, p ≠ q → ∃ k : Fin n, f^[k.val + 1] p = q ∨ f^[k.val + 1] q = p

instance {n : ℕ} (f : Fin n → Fin n) : Decidable (BoundedConnecting f) := by
  unfold BoundedConnecting
  infer_instance



private theorem shortest_orbit_injective {n m : ℕ} (f : Fin n → Fin n)
    (p q : Fin n) (hm : f^[m] p = q)
    (minimal : ∀ j < m, f^[j] p ≠ q) :
    Function.Injective (fun i : Fin (m + 1) => f^[i.val] p) := by
  have distinct {i j : Fin (m + 1)} (hij : i.val < j.val)
      (h : f^[i.val] p = f^[j.val] p) : False := by
    have hj := j.isLt
    have htime : m - j.val + j.val = m := by omega
    have hshort : m - j.val + i.val < m := by omega
    apply minimal _ hshort
    rw [Function.iterate_add_apply, h, ← Function.iterate_add_apply, htime, hm]
  intro i j h
  rcases lt_trichotomy i.val j.val with lt | eq | gt
  · exact (distinct lt h).elim
  · exact Fin.ext eq
  · exact (distinct gt h.symm).elim

private theorem bound_positive_exponent {n k : ℕ} (f : Fin n → Fin n)
    {p q : Fin n} (hpq : p ≠ q) (hit : f^[k] p = q) :
    ∃ j : Fin n, f^[j.val + 1] p = q := by
  classical
  have reaches : ∃ s : ℕ, f^[s] p = q := ⟨k, hit⟩
  let m := Nat.find reaches
  have hm : f^[m] p = q := Nat.find_spec reaches
  have inj := shortest_orbit_injective f p q hm (fun j hj => Nat.find_min reaches hj)
  have hc := Fintype.card_le_of_injective _ inj
  simp only [Fintype.card_fin] at hc
  have hpos : 0 < m := by
    by_contra! hz
    have hm0 : m = 0 := by omega
    rw [hm0] at hm
    exact hpq hm
  refine ⟨⟨m - 1, by omega⟩, ?_⟩
  have hback : m - 1 + 1 = m := by omega
  simpa only [hback] using hm

/-- A finite exponent as used in the site statement is equivalent to the source's
unbounded positive exponent, for all finite state spaces and all maps. -/
theorem bounded_iff_connecting {n : ℕ} (f : Fin n → Fin n) :
    BoundedConnecting f ↔ Connecting f := by
  constructor
  · intro h p q hpq
    obtain ⟨j, hj⟩ := h p q hpq
    exact ⟨j.val + 1, by omega, hj⟩
  · intro h p q hpq
    obtain ⟨k, _, h₁ | h₂⟩ := h p q hpq
    · obtain ⟨j, hj⟩ := bound_positive_exponent f hpq h₁
      exact ⟨j, Or.inl hj⟩
    · obtain ⟨j, hj⟩ := bound_positive_exponent f hpq.symm h₂
      exact ⟨j, Or.inr hj⟩


/-- Every word of length at most k over a finite ordered alphabet. -/
def wordsThrough {a : ℕ} : ℕ → List (List (Fin a))
  | 0 => [[]]
  | k + 1 => [] :: (List.finRange a).flatMap (fun l => (wordsThrough k).map (l :: ·))

theorem mem_wordsThrough {a : ℕ} (k : ℕ) (w : List (Fin a)) (h : w.length ≤ k) :
    w ∈ wordsThrough k := by
  induction k generalizing w with
  | zero =>
    have hw : w = [] := List.length_eq_zero_iff.mp (by omega)
    simp [hw, wordsThrough]
  | succ k ih =>
    cases w with
    | nil => simp [wordsThrough]
    | cons l w =>
      have ht : w ∈ wordsThrough k := ih w (by simpa using h)
      simp only [wordsThrough, List.mem_cons, List.mem_flatMap, List.mem_finRange,
        List.mem_map, true_and]
      exact Or.inr ⟨l, w, ht, rfl⟩

namespace Binary

def transition (l : Fin 2) (s : Fin 5) : Fin 5 :=
  if l = 0 then ![4, 3, 2, 1, 0] s else ![4, 0, 3, 2, 1] s

def tour : List (Fin 2) := [0, 1, 0, 1, 1, 1]

theorem connects : Connecting (run transition tour) := by
  apply (bounded_iff_connecting _).mp
  decide +kernel

theorem strong : Strong transition := by
  have reaches : ∀ p q : Fin 5, ∃ k : Fin 5,
      run transition (List.replicate k.val tour).flatten p = q := by decide +kernel
  intro p q
  obtain ⟨k, h⟩ := reaches p q
  exact ⟨_, h⟩

theorem shortest (w : List (Fin 2)) (hw : Connecting (run transition w)) :
    6 ≤ w.length := by
  have cert : ∀ v ∈ @wordsThrough 2 5, ¬ BoundedConnecting (run transition v) := by
    decide +kernel
  by_contra! h
  exact cert w (mem_wordsThrough 5 w (by omega)) ((bounded_iff_connecting _).mpr hw)

/-- Follow a local trajectory, requiring it to avoid state 2 at every command boundary. -/
def avoids : List (Fin 2) → Fin 5 → Bool
  | [], p => p != 2
  | l :: w, p => (p != 2) && avoids w (transition l p)

/-- All local programs of length at most four have a closed trajectory
whose entire trace avoids the common state. Used in the family argument. -/
theorem short_word_trap (w : List (Fin 2)) (hw : w.length ≤ 4) :
    ∃ (p : Fin 5) (t : Fin 5), let v := (List.replicate (t.val+1) w).flatten
      avoids v p = true ∧ run transition v p = p := by
  have cert : ∀ v ∈ @wordsThrough 2 4, ∃ (p : Fin 5) (t : Fin 5),
      let u := (List.replicate (t.val+1) v).flatten
      avoids u p = true ∧ run transition u p = p := by decide +kernel
  exact cert w (mem_wordsThrough 4 w hw)

end Binary

namespace Synchronizing

def transition (l : Fin 3) (s : Fin 5) : Fin 5 :=
  if l = 0 then ![4, 3, 2, 1, 0] s
  else if l = 1 then ![4, 0, 3, 2, 1] s
  else ![4, 0, 2, 2, 1] s

theorem resets : ∀ p, run transition [2, 0, 1, 2, 0, 2, 0, 2] p = 2 := by decide +kernel

theorem connects : Connecting (run transition [0, 1, 0, 1, 1, 1]) := by
  apply (bounded_iff_connecting _).mp
  decide +kernel

theorem strong : Strong transition := by
  have hits : ∀ p q : Fin 5, ∃ k : Fin 5,
      run transition (List.replicate k.val [0, 1, 0, 1, 1, 1]).flatten p = q := by
    decide +kernel
  intro p q
  obtain ⟨k,h⟩ := hits p q
  exact ⟨_, h⟩

/-- Two periodic points on disjoint cycles certify failure even of weak connectivity. -/
theorem two_cycles (w : List (Fin 3)) (hw : w.length ≤ 4) :
    ∃ p q : Fin 5, p ≠ q ∧ (∃ k : Fin 5, (run transition w)^[k.val+1] p = p) ∧
      (∃ k : Fin 5, (run transition w)^[k.val+1] q = q) ∧
      ∀ k : Fin 5, (run transition w)^[k.val+1] p ≠ q := by
  have cert : ∀ v ∈ @wordsThrough 3 4, ∃ p q : Fin 5, p ≠ q ∧
      (∃ k : Fin 5, (run transition v)^[k.val+1] p = p) ∧
      (∃ k : Fin 5, (run transition v)^[k.val+1] q = q) ∧
      ∀ k : Fin 5, (run transition v)^[k.val+1] p ≠ q := by decide +kernel
  exact cert w (mem_wordsThrough 4 w hw)

end Synchronizing
end OMA.S_mo_93022

open OMA.S_mo_93022

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_93022.main) := by
  intro h
  obtain ⟨w, hw, hc⟩ := h 5 2 (by decide) Binary.transition Binary.strong
    ⟨Binary.tour, Binary.connects⟩
  have lower := Binary.shortest w hc
  omega
