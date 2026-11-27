import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Tactic.NormNum

/-!
# Infinite atoms: the four-site counterexample
The four coordinates are the integer sites -1, 0, 1 and 2. Every packet is finite
and contained in an interval of diameter three. A measure supported on these four
sites can only use packets on these same sites, by positivity.
Credit: @LDJAI with OpenAI Codex.
-/

namespace InfiniteAtoms
open scoped ENNReal NNReal
noncomputable section

@[ext] structure Sites (α : Type) where
  left : α
  zero : α
  one : α
  right : α

abbrev Packet := Sites ℝ≥0
abbrev Measure := Sites ℝ≥0∞

def mass (a : Packet) : ℝ := a.left + a.zero + a.one + a.right
def first (a : Packet) : ℝ := -(a.left:ℝ) + a.one + 2 * a.right

def total (a : ℕ → Packet) : Measure :=
  ⟨∑' i, ((a i).left : ℝ≥0∞), ∑' i, ((a i).zero : ℝ≥0∞),
   ∑' i, ((a i).one : ℝ≥0∞), ∑' i, ((a i).right : ℝ≥0∞)⟩

/-- Finite or countable families can be padded with empty packet pairs. -/
def Move (p q : Measure) : Prop :=
  ∃ a b : ℕ → Packet, total a = p ∧ total b = q ∧
    ∀ i, mass (a i) = mass (b i) ∧ first (a i) = first (b i)

def source : Measure := ⟨0,⊤,0,0⟩
def middle : Measure := ⟨⊤,0,0,⊤⟩
def target : Measure := ⟨0,0,⊤,0⟩

theorem step_one : Move source middle := by
  refine ⟨fun _ => ⟨0,3,0,0⟩,fun _ => ⟨2,0,0,1⟩,?_,?_,?_⟩
  · ext <;> norm_num [total,source,ENNReal.tsum_const_eq_top_of_ne_zero]
  · ext <;> norm_num [total,middle,ENNReal.tsum_const_eq_top_of_ne_zero]
  · intro i; norm_num [mass,first]

theorem step_two : Move middle target := by
  refine ⟨fun _ => ⟨1,0,0,2⟩,fun _ => ⟨0,0,3,0⟩,?_,?_,?_⟩
  · ext <;> norm_num [total,middle,ENNReal.tsum_const_eq_top_of_ne_zero]
  · ext <;> norm_num [total,target,ENNReal.tsum_const_eq_top_of_ne_zero]
  · intro i; norm_num [mass,first]

theorem col_zero {f : ℕ → ℝ≥0} (eq : (∑' i, (f i : ℝ≥0∞))=0) (i : ℕ) : f i = 0 :=
  ENNReal.coe_eq_zero.mp ((ENNReal.tsum_eq_zero.mp eq) i)

theorem no_direct : ¬ Move source target := by
  rintro ⟨a,b,ha,hb,hbal⟩
  have al := @col_zero (fun i => (a i).left) (congrArg Sites.left ha)
  have ao := @col_zero (fun i => (a i).one) (congrArg Sites.one ha)
  have ar := @col_zero (fun i => (a i).right) (congrArg Sites.right ha)
  have bl := @col_zero (fun i => (b i).left) (congrArg Sites.left hb)
  have bz := @col_zero (fun i => (b i).zero) (congrArg Sites.zero hb)
  have br := @col_zero (fun i => (b i).right) (congrArg Sites.right hb)
  have van (i : ℕ) : (a i).zero = 0 := by
    obtain ⟨hm,hf⟩ := hbal i
    simp [mass,al i,ao i,ar i,bl i,bz i,br i] at hm
    simp [first,al i,ao i,ar i,bl i,br i] at hf
    exact hm.trans (NNReal.coe_eq_zero.mp hf.symm)
  have inf := congrArg Sites.zero ha
  change (∑' i, ((a i).zero : ℝ≥0∞))=⊤ at inf
  simp [van] at inf

theorem counterexample : Move source middle ∧ Move middle target ∧ ¬ Move source target :=
  ⟨step_one,step_two,no_direct⟩

end
end InfiniteAtoms

#print axioms InfiniteAtoms.counterexample
