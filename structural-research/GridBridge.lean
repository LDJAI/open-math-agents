import GridCore
import Mathlib.Logic.Function.Iterate

namespace GridCounter

/-- Edges represented by the two endpoint masks, with both traversal directions. -/
def edge (n H V a b : Nat) : Prop :=
  (b = a+1 ∧ H.testBit a) ∨ (a = b+1 ∧ H.testBit b) ∨
  (b = a+(n+1) ∧ V.testBit a) ∨ (a = b+(n+1) ∧ V.testBit b)

/-- At most k edges are used, with an initial set of vertices encoded by the bit mask s. -/
def boundedWalk (n H V s : Nat) : Nat → Nat → Prop
  | 0, b => s.testBit b
  | k+1, b => boundedWalk n H V s k b ∨ ∃ a, boundedWalk n H V s k a ∧ edge n H V a b

theorem expand_correct (n H V s b : Nat) :
    (expand n H V s).testBit b ↔ s.testBit b ∨ ∃ a, s.testBit a ∧ edge n H V a b := by
  simp only [expand, Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft,
    Nat.testBit_shiftRight, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · intro h
    rcases h with ((((hs|hr)|hl)|hd)|hu)
    · exact Or.inl hs
    · exact Or.inr ⟨b-1,hr.2.1,Or.inl ⟨by omega,hr.2.2⟩⟩
    · exact Or.inr ⟨1+b,hl.1,Or.inr (Or.inl ⟨by omega,hl.2⟩)⟩
    · exact Or.inr ⟨b-(n+1),hd.2.1,Or.inr (Or.inr (Or.inl ⟨by omega,hd.2.2⟩))⟩
    · exact Or.inr ⟨n+1+b,hu.1,Or.inr (Or.inr (Or.inr ⟨by omega,hu.2⟩))⟩
  · rintro (hs|⟨a,hs,he⟩)
    · exact Or.inl (Or.inl (Or.inl (Or.inl hs)))
    · rcases he with ⟨e,h⟩ | ⟨e,h⟩ | ⟨e,h⟩ | ⟨e,h⟩
      · subst b; exact Or.inl (Or.inl (Or.inl (Or.inr ⟨by omega, by simpa using hs, by simpa using h⟩)))
      · subst a; exact Or.inl (Or.inl (Or.inr ⟨by simpa [Nat.add_comm] using hs,h⟩))
      · subst b; exact Or.inl (Or.inr ⟨by omega, by simpa using hs, by simpa using h⟩)
      · subst a; exact Or.inr ⟨by simpa [Nat.add_comm] using hs,h⟩

theorem rounds_iterate (n H V k s : Nat) :
    rounds n H V k s = (expand n H V)^[k] s := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    rw [rounds, Function.iterate_succ_apply]
    by_cases h : expand n H V s = s
    · simp [h,Function.iterate_fixed h k]
    · simp [h,ih]

theorem rounds_correct (n H V s k b : Nat) :
    (rounds n H V k s).testBit b ↔ boundedWalk n H V s k b := by
  rw [rounds_iterate]
  induction k generalizing b with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', expand_correct]
    simp only [ih,boundedWalk]

theorem forward_walk (n : Nat) (hdel vdel : List Nat) (x y : Nat) :
    forward n hdel vdel x y ↔ boundedWalk n (horizontalMask n hdel) (verticalMask n vdel)
        1 ((n+1)*(n+1)) (y*(n+1)+x) := rounds_correct _ _ _ _ _ _

end GridCounter
