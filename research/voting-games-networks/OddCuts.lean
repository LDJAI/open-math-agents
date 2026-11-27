import Mathlib.Data.List.Basic

/-!
# Odd minimum cuts do not cross

An undirected multigraph is a list of endpoint pairs. Repeating a pair represents
integer capacity. A four-way partition witnesses a crossing of the two cuts
precisely when every region occurs. The theorem applies to arbitrary topology.
-/

namespace OrderedTrails.OddCuts

inductive Region | a | b | c | d
  deriving DecidableEq

open Region

def top : Region → Bool
  | a | b => true
  | c | d => false

def left : Region → Bool
  | a | c => true
  | b | d => false

def cut {V : Type*} (edges : List (V × V)) (side : V → Bool) : ℕ :=
  ((edges.filter (fun e => side e.1 != side e.2))).length

def joins (e : Region × Region) (u v : Region) : Bool :=
  (e.1 == u && e.2 == v) || (e.1 == v && e.2 == u)

def between (edges : List (Region × Region)) (u v : Region) : ℕ :=
  (edges.filter (fun e => joins e u v)).length

private theorem cut_formula (edges : List (Region × Region)) (p : Region → Bool) :
    cut edges p =
      (if p a != p b then between edges a b else 0) +
      (if p a != p c then between edges a c else 0) +
      (if p a != p d then between edges a d else 0) +
      (if p b != p c then between edges b c else 0) +
      (if p b != p d then between edges b d else 0) +
      (if p c != p d then between edges c d else 0) := by
  induction edges with
  | nil => simp [cut, between]
  | cons e es ih =>
    rcases e with ⟨s,t⟩
    have step (q : Region × Region → Bool) :
        (List.filter q ((s,t) :: es)).length =
          (List.filter q es).length + (if q (s,t) then 1 else 0) := by
      cases h : q (s,t) <;> simp [h]
    unfold cut between at ih ⊢
    simp only [step]
    by_cases h : p s = p t
    · cases s <;> cases t <;> simp [joins, h] at ih ⊢ <;> omega
    · have hr := Ne.symm h
      cases s <;> cases t <;> simp_all [joins] <;> omega

private theorem project_cut {V : Type*} (edges : List (V × V)) (zone : V → Region)
    (p : Region → Bool) :
    cut (edges.map fun e => (zone e.1, zone e.2)) p = cut edges (p ∘ zone) := by
  induction edges with
  | nil => rfl
  | cons e edges ih =>
    cases h : (p (zone e.1) != p (zone e.2)) <;>
      simpa [cut, Function.comp_def, h] using ih

/-- If all nontrivial cuts have size at least 2m+1, then two cuts of that
size cannot realize all four intersections of their shores. -/
theorem odd_min_cuts_cannot_cross {V : Type*} (edges : List (V × V))
    (zone : V → Region) (m : ℕ)
    (connected : ∀ s : V → Bool, (∃ x, s x = true) →
      (∃ y, s y = false) → 2*m+1 ≤ cut edges s)
    (ht : cut edges (top ∘ zone) = 2*m+1)
    (hl : cut edges (left ∘ zone) = 2*m+1) : ¬ Function.Surjective zone := by
  intro onto
  let es := edges.map fun e => (zone e.1, zone e.2)
  have htop : cut es top = 2*m+1 := (project_cut edges zone top).trans ht
  have hleft : cut es left = 2*m+1 := (project_cut edges zone left).trans hl
  have one (r s : Region) (diff : s ≠ r) :
      2*m+1 ≤ cut es (fun x => x == r) := by
    obtain ⟨v, hv⟩ := onto r
    obtain ⟨w, hw⟩ := onto s
    rw [show cut es (fun x => x == r) = _ from project_cut edges zone _]
    exact connected _ ⟨v, by simp [hv]⟩
      ⟨w, by simp [hw, diff]⟩
  have ha := one a b (by decide)
  have hb := one b c (by decide)
  have hc := one c d (by decide)
  have hd := one d a (by decide)
  simp [cut_formula, top, left] at htop hleft ha hb hc hd
  omega

#print axioms odd_min_cuts_cannot_cross

end OrderedTrails.OddCuts
