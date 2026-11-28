import OMAStatements.S_oeis_a374527
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

open OMA.S_oeis_a374527
namespace IndependentCollatzSidon

private def powers : Set ℕ := {x | ∃ e : ℕ, x = 2^e}

private theorem maxBound {a b c d : ℕ} (e : (2:ℕ)^a+2^b=2^c+2^d) :
    max a b ≤ max c d := by
  by_contra! h
  have h1 : 2^(max c d+1) ≤ (2:ℕ)^(max a b) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have h2 : (2:ℕ)^c ≤ 2^(max c d) := Nat.pow_le_pow_right (by decide) (le_max_left ..)
  have h3 : (2:ℕ)^d ≤ 2^(max c d) := Nat.pow_le_pow_right (by decide) (le_max_right ..)
  rw [pow_succ] at h1
  have ha : 0 < (2:ℕ)^a := pow_pos (by decide) _
  have hb : 0 < (2:ℕ)^b := pow_pos (by decide) _
  rcases le_total a b with h | h
  · rw [max_eq_right h] at h1; omega
  · rw [max_eq_left h] at h1; omega

private theorem powerSidon : IsSidonSet powers := by
  rintro _ ⟨a,rfl⟩ _ ⟨b,rfl⟩ _ ⟨c,rfl⟩ _ ⟨d,rfl⟩ e
  have h := le_antisymm (maxBound e) (maxBound e.symm)
  rcases le_total a b with hab|hab <;> rcases le_total c d with hcd|hcd <;>
    first | rw [max_eq_right hab,max_eq_right hcd] at h; subst_vars; omega
          | rw [max_eq_right hab,max_eq_left hcd] at h; subst_vars; omega
          | rw [max_eq_left hab,max_eq_right hcd] at h; subst_vars; omega
          | rw [max_eq_left hab,max_eq_left hcd] at h; subst_vars; omega

private def binaryResidue (r : ℕ) : Prop :=
  r=0 ∨ r=1 ∨ r=2 ∨ r=4 ∨ r=8 ∨ r=16 ∨ r=32

private theorem residuePow {x : ℕ} (h : x ∈ powers) : binaryResidue (x%64) := by
  obtain ⟨e,rfl⟩ := h
  by_cases he : 6 ≤ e
  · obtain ⟨f,rfl⟩ := Nat.exists_eq_add_of_le he
    left
    simp [pow_add,show (2:ℕ)^6=64 by decide]
  · have : e=0 ∨ e=1 ∨ e=2 ∨ e=3 ∨ e=4 ∨ e=5 := by omega
    rcases this with h|h|h|h|h|h <;> subst e <;> unfold binaryResidue <;> decide

private theorem extended {s : ℕ} (hs : s%64=21) : IsSidonSet (insert s powers) := by
  have mixed {x y z : ℕ} (hx : x ∈ powers) (hy : y ∈ powers) (hz : z ∈ powers) :
      s+x ≠ y+z := by
    intro he
    have eq := congrArg (·%64) he
    simp only [Nat.add_mod s x, Nat.add_mod y z, hs] at eq
    have rule : ∀ i j k : Fin 64, binaryResidue i.val → binaryResidue j.val →
        binaryResidue k.val → (21+i.val)%64 ≠ (j.val+k.val)%64 := by
      intro i j k hi hj hk
      unfold binaryResidue at *
      omega
    exact rule ⟨_,Nat.mod_lt x (by decide)⟩ ⟨_,Nat.mod_lt y (by decide)⟩
      ⟨_,Nat.mod_lt z (by decide)⟩ (residuePow hx) (residuePow hy) (residuePow hz) eq
  have dbl {x y : ℕ} (hx : x ∈ powers) (hy : y ∈ powers) : s+s ≠ x+y := by
    intro e
    have eq := congrArg (·%64) e
    simp only [Nat.add_mod s s,Nat.add_mod x y,hs] at eq
    have h1 := residuePow hx
    have h2 := residuePow hy
    unfold binaryResidue at h1 h2
    omega
  intro a ha b hb c hc d hd e
  rcases Set.mem_insert_iff.mp ha with ea|ha <;> rcases Set.mem_insert_iff.mp hb with eb|hb <;>
    rcases Set.mem_insert_iff.mp hc with ec|hc <;> rcases Set.mem_insert_iff.mp hd with ed|hd
  all_goals
    try exact powerSidon _ ha _ hb _ hc _ hd e
    try have h := mixed ha hc hd
    try have h := mixed hb hc hd
    try have h := mixed hc ha hb
    try have h := mixed hd ha hb
    try have h := dbl ha hb
    try have h := dbl hc hd
    all_goals omega

private def seed : ℕ → ℕ
  | 0 => 0
  | k+1 => 4*seed k+1

private theorem formula (k : ℕ) : 3*seed k+1=4^k := by
  induction k with
  | zero => decide
  | succ k ih => rw [pow_succ,← ih]; simp only [seed]; ring

private theorem seedResidue (k : ℕ) : seed (k+3)%64=21 := by
  change (4*(4*(4*seed k+1)+1)+1)%64=21
  omega

private theorem descending (m j : ℕ) (hj : j ≤ m) :
    collatzStep^[j] (2^m) = 2^(m-j) := by
  induction j generalizing m with
  | zero => simp
  | succ j ih =>
    cases m with
    | zero => omega
    | succ m =>
      rw [Function.iterate_succ_apply,show collatzStep (2^(m+1)) = 2^m by
        simp [collatzStep,pow_succ]]
      simpa using ih m (by omega)

theorem family :
    ∀ k : ℕ, 1 ≤ k → k ≠ 2 →
      Odd ((4 ^ k - 1) / 3) ∧ HasSidonCollatzTrajectory ((4 ^ k - 1) / 3) := by
  intro k hk htwo
  have eq : (4^k-1)/3 = seed k := by have := formula k; omega
  rw [eq]
  cases k with
  | zero => omega
  | succ k =>
    refine ⟨⟨2*seed k,by simp only [seed]; omega⟩,?_⟩
    by_cases hk0 : k=0
    · subst k
      refine ⟨0,rfl,by omega,?_⟩
      rintro a ⟨i,hi,ha⟩ b ⟨j,hj,hb⟩ c ⟨l,hl,hc⟩ d ⟨m,hm,hd⟩ _
      have ei : i=0 := by omega
      have ej : j=0 := by omega
      have el : l=0 := by omega
      have em : m=0 := by omega
      subst i; subst j; subst l; subst m
      exact Or.inl ⟨ha.symm.trans hc,hb.symm.trans hd⟩
    have hres : seed (k+1)%64=21 := by
      obtain ⟨n,hn⟩ := Nat.exists_eq_add_of_le (show 2 ≤ k by omega)
      have hnk : k+1=n+3 := by omega
      rw [hnk]; exact seedResidue n
    let m := 2*(k+1)
    have hstep : collatzStep (seed (k+1))=2^m := by
      have hr : seed (k+1)%2=1 := by change (4*seed k+1)%2=1; omega
      rw [collatzStep,hr,if_neg (by decide),formula]
      dsimp [m]; rw [pow_mul]; rfl
    have after (j : ℕ) (hj : j ≤ m) :
        collatzStep^[j+1] (seed (k+1))=2^(m-j) := by
      rw [Function.iterate_succ_apply,hstep,descending _ _ hj]
    refine ⟨m+1,by simpa using after m (by omega),?_,?_⟩
    · intro j hj
      cases j with
      | zero => change seed (k+1) ≠ 1; omega
      | succ j =>
        rw [after j (by omega)]
        exact ne_of_gt (one_lt_pow₀ (by decide : (1:ℕ)<2) (by omega))
    · have sub : {x : ℕ | ∃ j ≤ m+1, collatzStep^[j] (seed (k+1))=x} ⊆
          insert (seed (k+1)) powers := by
        rintro x ⟨j,hj,rfl⟩
        cases j with
        | zero => exact Or.inl rfl
        | succ j => exact Or.inr ⟨m-j,after j (by omega)⟩
      intro a ha b hb c hc d hd
      exact extended hres a (sub ha) b (sub hb) c (sub hc) d (sub hd)

end IndependentCollatzSidon

theorem OMA.solution : type_of% @OMA.S_oeis_a374527.main := IndependentCollatzSidon.family
