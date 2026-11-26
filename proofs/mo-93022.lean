import OMAStatements.S_mo_93022
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.GroupTheory.Perm.Cycle.Basic

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

namespace OMA.S_mo_93022.Family

/-- The shared hub is none. All other states belong to exactly one copy. -/
abbrev State (m : ℕ) := Option (Fin m × {p : Fin 5 // p ≠ 2})
abbrev Letter (m : ℕ) := Fin m × Fin 2

def embed {m : ℕ} (i : Fin m) (p : Fin 5) : State m :=
  if h : p = 2 then none else some (i, ⟨p, h⟩)

def step {m : ℕ} (l : Letter m) : State m → State m
  | none => embed l.1 (Binary.transition l.2 2)
  | some (i, p) =>
    if l.1 = i then embed i (Binary.transition l.2 p.val) else some (i, p)

def localWord {m : ℕ} (i : Fin m) : List (Letter m) → List (Fin 2)
  | [] => []
  | l :: w => if l.1 = i then l.2 :: localWord i w else localWord i w

def action {m : ℕ} (w : List (Letter m)) (p : State m) : State m :=
  w.foldl (fun s l => step l s) p

/-- If the entire local trajectory avoids the hub, outside commands fix it. -/
theorem run_local {m : ℕ} (i : Fin m) (w : List (Letter m)) (p : Fin 5)
    (h : Binary.avoids (localWord i w) p = true) :
    action w (embed i p) = embed i (run Binary.transition (localWord i w) p) := by
  induction w generalizing p with
  | nil => rfl
  | cons l w ih =>
    by_cases e : l.1 = i
    · simp only [localWord, if_pos e, Binary.avoids, Bool.and_eq_true, bne_iff_ne] at h
      change action w (step l (embed i p)) = _
      have hx : step l (embed i p) = embed i (Binary.transition l.2 p) := by
        simp [embed, h.1, step, e]
      rw [hx, ih _ h.2]
      simp [localWord, e, run]
    · simp only [localWord, if_neg e] at h ⊢
      have hp : p ≠ 2 := by
        cases hh : localWord i w with
        | nil => simpa [hh, Binary.avoids] using h
        | cons x xs => simp only [hh, Binary.avoids, Bool.and_eq_true, bne_iff_ne] at h
                       exact h.1
      change action w (step l (embed i p)) = _
      have hx : step l (embed i p) = embed i p := by simp [embed, hp, step, e]
      rw [hx]
      exact ih p h

/-- A nonempty set of local boundary states is trapped and avoids the hub. -/
theorem trap_set (v : List (Fin 2)) (hv : v.length ≤ 4) :
    ∃ mask : Fin 32, (∃ p : Fin 5, mask.val.testBit p.val = true) ∧
      ∀ p : Fin 5, mask.val.testBit p.val = true →
        p ≠ 2 ∧ Binary.avoids v p = true ∧
        mask.val.testBit (run Binary.transition v p).val = true := by
  have cert : ∀ u ∈ @wordsThrough 2 4, ∃ mask : Fin 32,
      (∃ p : Fin 5, mask.val.testBit p.val = true) ∧ ∀ p : Fin 5,
      mask.val.testBit p.val = true → p ≠ 2 ∧ Binary.avoids u p = true ∧
      mask.val.testBit (run Binary.transition u p).val = true := by decide +kernel
  exact cert v (mem_wordsThrough 4 v hv)

/-- Every copy in a tour needs at least five local commands. -/
theorem five_per_copy {m : ℕ} (w : List (Letter m)) (i : Fin m)
    (tour : ∀ p : State m, ∃ k : ℕ, (action w)^[k] p = none) :
    5 ≤ (localWord i w).length := by
  by_contra! short
  obtain ⟨mask, ⟨p, hp⟩, keep⟩ := trap_set (localWord i w) (by omega)
  have stays (k : ℕ) : ∃ q : Fin 5, mask.val.testBit q.val = true ∧
      (action w)^[k] (embed i p) = embed i q := by
    induction k with
    | zero => exact ⟨p, hp, rfl⟩
    | succ k ih =>
      obtain ⟨q, hq, he⟩ := ih
      obtain ⟨_, avoid, next⟩ := keep q hq
      exact ⟨_, next, by rw [Function.iterate_succ_apply', he, run_local i w q avoid]⟩
  obtain ⟨k, hit⟩ := tour (embed i p)
  obtain ⟨q, hq, he⟩ := stays k
  have qprivate := (keep q hq).1
  rw [he] at hit
  simp [embed, qprivate] at hit

theorem sum_local_lengths {m : ℕ} (w : List (Letter m)) :
    ∑ i : Fin m, (localWord i w).length = w.length := by
  induction w with
  | nil => simp [localWord]
  | cons l w ih =>
    have each (i : Fin m) : (localWord i (l :: w)).length =
        (if l.1 = i then 1 else 0) + (localWord i w).length := by
      by_cases h : l.1 = i <;> simp [localWord, h, Nat.add_comm]
    simp_rw [each]
    simp [Finset.sum_add_distrib, ih, Nat.add_comm]

theorem length_lower_bound {m : ℕ} (w : List (Letter m))
    (tour : ∀ p : State m, ∃ k : ℕ, (action w)^[k] p = none) : 5 * m ≤ w.length := by
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun (i : Fin m) _ => five_per_copy w i tour)
  simpa [sum_local_lengths, Nat.mul_comm] using h

theorem embed_apply {m : ℕ} (i : Fin m) (a : Fin 2) (p : Fin 5) :
    step (i, a) (embed i p) = embed i (Binary.transition a p) := by
  by_cases h : p = 2 <;> simp [embed, step, h]

theorem step_iterate_embed {m : ℕ} (i : Fin m) (a : Fin 2) (p : Fin 5) (k : ℕ) :
    (step (i, a))^[k] (embed i p) = embed i ((Binary.transition a)^[k] p) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih, embed_apply, Function.iterate_succ_apply']

theorem step_injective {m : ℕ} (l : Letter m) : Function.Injective (step l) := by
  obtain ⟨i,a⟩ := l
  have order : ∀ (z : Fin 2) (p : Fin 5), (Binary.transition z)^[6] p = p := by decide +kernel
  have closes (p : State m) : (step (i,a))^[6] p = p := by
    cases p with
    | none =>
      change (step (i,a))^[6] (embed i 2) = embed i 2
      rw [step_iterate_embed, order]
    | some t =>
      obtain ⟨j, q⟩ := t
      by_cases h : i = j
      · subst j
        have he : embed i q.val = some (i, q) := by simp [embed, q.property]
        rw [← he, step_iterate_embed, order]
      · have fixed : Function.IsFixedPt (step (i,a)) (some (j, q)) := by simp [Function.IsFixedPt, step, h]
        exact fixed.iterate 6
  intro x y eq
  calc
    x = (step (i,a))^[6] x := (closes x).symm
    _ = (step (i,a))^[6] y := congrArg ((step (i,a))^[5]) eq
    _ = y := closes y

theorem action_injective {m : ℕ} (w : List (Letter m)) : Function.Injective (action w) := by
  induction w with
  | nil => exact Function.injective_id
  | cons l w ih => exact ih.comp (step_injective l)

/-- The lower bound with the original question's pairwise directed condition. -/
theorem connecting_lower_bound {m : ℕ} (w : List (Letter m))
    (h : ∀ p q : State m, p ≠ q → ∃ k : ℕ, 0 < k ∧
      ((action w)^[k] p = q ∨ (action w)^[k] q = p)) :
    5 * m ≤ w.length := by
  apply length_lower_bound
  intro p
  by_cases e : p = none
  · exact ⟨0, e⟩
  obtain ⟨k, _, hp | hp⟩ := h p none e
  · exact ⟨k, hp⟩
  · obtain ⟨j, hj, hperiod⟩ := (action_injective w).mem_periodicPts none
    have many : (action w)^[j * k] none = none := (hperiod.mul_const k).eq
    have hk : k ≤ j * k := by simpa only [one_mul] using Nat.mul_le_mul_right k (show 1 ≤ j from hj)
    refine ⟨j * k - k, ?_⟩
    rw [← hp, ← Function.iterate_add_apply, Nat.sub_add_cancel hk, many]

end OMA.S_mo_93022.Family

namespace OMA.S_mo_93022.Family

/-- Applying the swaps (h,x) chronologically for each x in the list. -/
def stars {α : Type} [DecidableEq α] (h : α) (xs : List α) (p : α) : α :=
  xs.foldl (fun s x => Equiv.swap h x s) p

theorem stars_eq_cycle {α : Type} [DecidableEq α] (h : α) (xs : List α)
    (hd : (h :: xs).Nodup) (p : α) : stars h xs p = (h :: xs).formPerm p := by
  induction xs generalizing p with
  | nil => simp [stars]
  | cons x xs ih =>
    have tail : (h :: xs).Nodup := List.nodup_cons.mpr
      ⟨fun e => (List.nodup_cons.mp hd).1 (List.mem_cons_of_mem _ e),
        (List.nodup_cons.mp (List.nodup_cons.mp hd).2).2⟩
    have rot : (xs ++ [h,x]).formPerm = (h :: x :: xs).formPerm := by
      simpa only [List.rotate_cons_succ, List.cons_append, List.rotate_zero,
        List.append_assoc, List.singleton_append, List.nil_append] using (List.formPerm_rotate _ hd 2)
    have rot1 : (xs ++ [h]).formPerm = (h :: xs).formPerm := by
      simpa only [List.rotate_cons_succ, List.rotate_zero] using (List.formPerm_rotate_one _ tail)
    change stars h xs (Equiv.swap h x p) = _
    rw [ih tail, ← rot, List.formPerm_append_pair, rot1]
    rfl

theorem stars_map {α β : Type} [DecidableEq α] [DecidableEq β]
    {f : α → β} (hf : Function.Injective f) (h : α) (xs : List α) (p : α) :
    stars (f h) (xs.map f) (f p) = f (stars h xs p) := by
  induction xs generalizing p with
  | nil => rfl
  | cons x xs ih =>
    change stars (f h) (xs.map f) (Equiv.swap (f h) (f x) (f p)) = _
    rw [hf.swap_apply, ih]
    rfl

theorem stars_outside {α : Type} [DecidableEq α] (h p : α) (xs : List α)
    (hp : p ≠ h) (hx : p ∉ xs) : stars h xs p = p := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change stars h xs (Equiv.swap h x p) = p
    rw [Equiv.swap_apply_of_ne_of_ne hp (fun e => hx (List.mem_cons.mpr (Or.inl e)))]
    exact ih (fun e => hx (List.mem_cons_of_mem _ e))

def order : List (Fin 5) := [1, 3, 4, 0]
def privateStates {m : ℕ} (i : Fin m) : List (State m) := order.map (embed i)
def block {m : ℕ} (i : Fin m) : List (Letter m) := Binary.tour.map (Prod.mk i)

theorem embed_injective {m : ℕ} (i : Fin m) : Function.Injective (embed i) := by
  intro p q e
  by_cases a : p = 2 <;> by_cases b : q = 2 <;> simp_all [embed]

theorem local_block {m : ℕ} (i : Fin m) (v : List (Fin 2)) (p : Fin 5) :
    action (v.map (Prod.mk i)) (embed i p) = embed i (run Binary.transition v p) := by
  induction v generalizing p with
  | nil => rfl
  | cons l w ih =>
    change action (w.map (Prod.mk i)) (step (i,l) (embed i p)) = _
    rw [embed_apply, ih]
    rfl

theorem outside_block {m : ℕ} (i j : Fin m) (h : i ≠ j) (v : List (Fin 2))
    (p : {x : Fin 5 // x ≠ 2}) : action (v.map (Prod.mk i)) (some (j,p)) = some (j,p) := by
  induction v with
  | nil => rfl
  | cons l w ih =>
    change action (w.map (Prod.mk i)) (step (i,l) (some (j,p))) = _
    simpa only [step, if_neg h] using ih

theorem block_eq_stars {m : ℕ} (i : Fin m) (p : State m) :
    action (block i) p = stars none (privateStates i) p := by
  have localEq (x : Fin 5) : action (block i) (embed i x) =
      stars none (privateStates i) (embed i x) := by
    have table : ∀ y, run Binary.transition Binary.tour y = stars 2 order y := by decide +kernel
    change action (Binary.tour.map (Prod.mk i)) (embed i x) =
      stars (embed i 2) (order.map (embed i)) (embed i x)
    rw [local_block, stars_map (embed_injective _), table]
  cases p with
  | none => exact localEq 2
  | some t =>
    obtain ⟨j,q⟩ := t
    by_cases ij : i = j
    · subst j
      simpa [embed, q.property] using localEq q.val
    · rw [block, outside_block i j ij]
      apply Eq.symm
      apply stars_outside _ _ _ (by simp)
      intro mem
      obtain ⟨x, _, eq⟩ := List.mem_map.mp mem
      by_cases h : x = 2 <;> simp_all [embed]

def program {m : ℕ} (is : List (Fin m)) : List (Letter m) := is.flatMap block

theorem program_action {m : ℕ} (is : List (Fin m)) (p : State m) :
    action (program is) p = stars none (is.flatMap privateStates) p := by
  induction is generalizing p with
  | nil => rfl
  | cons i is ih =>
    change action (block i ++ program is) p = stars none (privateStates i ++ is.flatMap privateStates) p
    rw [show action (block i ++ program is) p = action (program is) (action (block i) p) from List.foldl_append,
      ih, block_eq_stars]
    exact List.foldl_append.symm

theorem list_complete {m : ℕ} (p : State m) :
    p ∈ (none :: (List.finRange m).flatMap privateStates) := by
  cases p with
  | none => simp
  | some t =>
    obtain ⟨i,q⟩ := t
    apply List.mem_cons_of_mem
    apply List.mem_flatMap.mpr
    refine ⟨i, List.mem_finRange _, List.mem_map.mpr ⟨q.val, ?_, ?_⟩⟩
    · have table : ∀ y : Fin 5, y ≠ 2 → y ∈ order := by decide +kernel
      exact table _ q.property
    · simp [embed, q.property]

theorem list_nodup (m : ℕ) : (none :: (List.finRange m).flatMap privateStates).Nodup := by
  have priv {i : Fin m} {p : State m} (hp : p ∈ privateStates i) :
      ∃ q : {x : Fin 5 // x ≠ 2}, p = some (i, q) := by
    obtain ⟨x, xm, rfl⟩ := List.mem_map.mp hp
    have h : x ≠ 2 := fun e => by subst x; exact (by decide : (2 : Fin 5) ∉ order) xm
    exact ⟨⟨x,h⟩, by simp [embed,h]⟩
  apply List.nodup_cons.mpr
  constructor
  · intro hn
    obtain ⟨i,_,hi⟩ := List.mem_flatMap.mp hn
    obtain ⟨_, he⟩ := priv hi
    cases he
  · apply List.nodup_flatMap.mpr
    refine ⟨fun i _ => (show order.Nodup by decide).map (embed_injective i), ?_⟩
    apply (List.nodup_finRange m).imp
    intro i j hij p hp₁ hp₂
    obtain ⟨q,hq⟩ := priv hp₁
    obtain ⟨r,hr⟩ := priv hp₂
    have eq : some (i,q) = some (j,r) := hq.symm.trans hr
    exact hij (congrArg Prod.fst (Option.some.inj eq))

theorem explicit_tour (m : ℕ) (p q : State m) :
    ∃ k : ℕ, (action (program (List.finRange m)))^[k] p = q := by
  let l : List (State m) := none :: (List.finRange m).flatMap privateStates
  have hd : l.Nodup := list_nodup m
  have he : action (program (List.finRange m)) = l.formPerm := by
    funext x
    rw [program_action, stars_eq_cycle _ _ hd]
  have same := hd.isCycleOn_formPerm.2 (list_complete p) (list_complete q)
  obtain ⟨k,hk⟩ := same.exists_nat_pow_eq
  refine ⟨k, ?_⟩
  rw [he]
  simpa only [Equiv.Perm.coe_pow] using hk

theorem program_length {m : ℕ} (is : List (Fin m)) : (program is).length = 6 * is.length := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    change (block i ++ program is).length = _
    simp [block, Binary.tour, ih, Nat.mul_succ]

theorem state_count (m : ℕ) : Fintype.card (State m) = 4*m+1 := by
  have hn : Fintype.card {p : Fin 5 // p ≠ 2} = 4 := by decide
  simp [State, Fintype.card_prod, hn, Nat.mul_comm]

end OMA.S_mo_93022.Family

namespace OMA.S_mo_93022.Family

/-- The family has 4m+1 states. A word of length 6m visits every state from
every starting state on repetition. Every connecting word has length at least 5m. -/
theorem family_bounds (m : ℕ) :
    Fintype.card (State m) = 4*m+1 ∧
    (∃ w : List (Letter m), w.length = 6*m ∧ ∀ p q : State m,
      ∃ k : ℕ, (action w)^[k] p = q) ∧
    (∀ w : List (Letter m), (∀ p q : State m, p ≠ q → ∃ k : ℕ, 0 < k ∧
      ((action w)^[k] p = q ∨ (action w)^[k] q = p)) → 5*m ≤ w.length) := by
  exact ⟨state_count m,
    ⟨program (List.finRange m), by simp [program_length], explicit_tour m⟩,
    fun w hw => connecting_lower_bound w hw⟩

end OMA.S_mo_93022.Family

open OMA.S_mo_93022

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_93022.main) := by
  intro h
  obtain ⟨w, hw, hc⟩ := h 5 2 (by decide) Binary.transition Binary.strong
    ⟨Binary.tour, Binary.connects⟩
  have lower := Binary.shortest w hc
  omega
