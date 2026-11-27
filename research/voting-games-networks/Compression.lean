import Mathlib.Data.List.Basic

/-!
# Connectivity after rematching the boundary edges of two shores

Each list entry is a separate physical edge, so parallel edges are allowed.
The hypotheses concern cuts of one shore with the other shore contracted to
a single vertex. They are invariant under any re-pairing of the port lists.
-/

namespace ShoreCompression

variable {L R V : Type*}

/-- Edges of a single shore crossed by a Boolean partition. -/
def internal (edges : List (V × V)) (p : V → Bool) : ℕ :=
  edges.countP (fun z => p z.1 != p z.2)

/-- Edges joining two shores crossed by independent Boolean partitions. -/
def crossing (edges : List (L × R)) (p : L → Bool) (q : R → Bool) : ℕ :=
  edges.countP (fun z => p z.1 != q z.2)

def leftPorts (edges : List (L × R)) (p : L → Bool) : ℕ :=
  edges.countP (fun z => p z.1)

def rightPorts (edges : List (L × R)) (q : R → Bool) : ℕ :=
  edges.countP (fun z => q z.2)

private theorem internal_flip (E : List (V × V)) (p : V → Bool) :
    internal E (fun x => !(p x)) = internal E p := by
  unfold internal
  congr 1
  funext z
  change ((!p z.1) != (!p z.2)) = (p z.1 != p z.2)
  cases p z.1 <;> cases p z.2 <;> rfl

private theorem count_complement (E : List V) (p : V → Bool) :
    E.countP p + E.countP (fun x => !(p x)) = E.length := by
  induction E with
  | nil => rfl
  | cons e es ih =>
    simp only [List.countP_cons, List.length_cons]
    cases p e <;> simp <;> omega

private theorem left_sum (P : List (L × R)) (p : L → Bool) :
    leftPorts P p + leftPorts P (fun x => !(p x)) = P.length :=
  count_complement P (fun z => p z.1)

private theorem right_sum (P : List (L × R)) (q : R → Bool) :
    rightPorts P q + rightPorts P (fun x => !(q x)) = P.length :=
  count_complement P (fun z => q z.2)

/-- A shore split into two nonempty pieces contributes at least half the
global connectivity internally, even before any matched port edges are counted. -/
theorem split_shore_twice (k d a b : ℕ) (ports : a+b = k)
    (one : k ≤ d+a) (other : k ≤ d+b) : k ≤ d+d := by omega

/-- If each shore and its contracted complement have connectivity at least
`k` and exactly `k` edges join the shores, every cut of the joined graph
has at least `k` edges. The end vertices in each shore determine the two
local hypotheses; the pairing of the end vertices is arbitrary. -/
theorem rematch_preserves_connectivity
    (EL : List (L × L)) (ER : List (R × R)) (P : List (L × R)) (k : ℕ)
    (pk : P.length = k)
    (leftConnected : ∀ p : L → Bool, (∃ x, p x = true) →
      k ≤ internal EL p + leftPorts P p)
    (rightConnected : ∀ q : R → Bool, (∃ y, q y = true) →
      k ≤ internal ER q + rightPorts P q)
    (p : L → Bool) (q : R → Bool)
    (hasTrue : (∃ x, p x = true) ∨ (∃ y, q y = true))
    (hasFalse : (∃ x, p x = false) ∨ (∃ y, q y = false)) :
    k ≤ internal EL p + internal ER q + crossing P p q := by
  classical
  by_cases lt : ∃ x, p x = true
  · by_cases lf : ∃ x, p x = false
    · by_cases rt : ∃ y, q y = true
      · by_cases rf : ∃ y, q y = false
        · have ll := leftConnected p lt
          obtain ⟨x, hx⟩ := lf
          have lr := leftConnected (fun t => !(p t)) ⟨x, by simp [hx]⟩
          have rr := rightConnected q rt
          obtain ⟨y, hy⟩ := rf
          have rl := rightConnected (fun t => !(q t)) ⟨y, by simp [hy]⟩
          rw [internal_flip] at lr rl
          have ld := split_shore_twice k _ _ _ ((left_sum P p).trans pk) ll lr
          have rd := split_shore_twice k _ _ _ ((right_sum P q).trans pk) rr rl
          omega
        · have all : ∀ y, q y = true := by
            intro y
            cases h : q y <;> simp_all
          obtain ⟨x, hx⟩ := lf
          have lower := leftConnected (fun t => !(p t)) ⟨x, by simp [hx]⟩
          rw [internal_flip] at lower
          have eq : crossing P p q = leftPorts P (fun t => !(p t)) := by
            unfold crossing leftPorts
            congr 1
            funext z
            rw [all]
            change (p z.1 != true) = !p z.1
            cases p z.1 <;> rfl
          omega
      · have all : ∀ y, q y = false := by
          intro y
          cases h : q y <;> simp_all
        have lower := leftConnected p lt
        have eq : crossing P p q = leftPorts P p := by
          unfold crossing leftPorts
          congr 1
          funext z
          rw [all]
          cases p z.1 <;> rfl
        omega
    · have all : ∀ x, p x = true := by
        intro x
        cases h : p x <;> simp_all
      obtain ⟨y, hy⟩ := hasFalse.resolve_left lf
      have lower := rightConnected (fun t => !(q t)) ⟨y, by simp [hy]⟩
      rw [internal_flip] at lower
      have eq : crossing P p q = rightPorts P (fun t => !(q t)) := by
        unfold crossing rightPorts
        congr 1
        funext z
        rw [all]
        change (true != q z.2) = !q z.2
        cases q z.2 <;> rfl
      omega
  · have all : ∀ x, p x = false := by
      intro x
      cases h : p x <;> simp_all
    have lower := rightConnected q (hasTrue.resolve_left lt)
    have eq : crossing P p q = rightPorts P q := by
      unfold crossing rightPorts
      congr 1
      funext z
      rw [all]
      cases q z.2 <;> rfl
    omega

#print axioms rematch_preserves_connectivity

end ShoreCompression
