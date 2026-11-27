import OMAStatements.S_mo_331165

/-! Counterexample to Berger's pointwise parallelism conjecture, by @LDJAI with OpenAI Codex. -/

open scoped Matrix
open OMA.S_mo_331165

namespace BergerCounterexample

noncomputable def density (x : Space) : ℝ := Real.exp (x 0)

noncomputable def velocity (x : Space) : Space := Real.exp (-(x 0)) • Pi.single 1 1

theorem density_pos (x : Space) : 0 < density x := Real.exp_pos _

theorem density_diff : Differentiable ℝ density := by
  unfold density
  fun_prop

theorem velocity_diff : Differentiable ℝ velocity := by
  unfold velocity
  fun_prop

theorem current_constant (B : Space) :
    current density velocity B = fun _ => B ⨯₃ Pi.single 1 1 := by
  funext x
  simp only [current, density, velocity, map_smul, smul_smul]
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, one_smul]

theorem divergence_zero (B x : Space) : divField (current density velocity B) x = 0 := by
  rw [current_constant]
  simp [divField, coordDeriv]

theorem not_parallel (x : Space) : ¬ ∃ a : ℝ, velocity x = a • grad density x := by
  rintro ⟨a, h⟩
  have hs := congrFun h (1 : Fin 3)
  simp [velocity, grad, density, coordDeriv] at hs

end BergerCounterexample

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_331165.main) := by
  intro h
  open BergerCounterexample in
    exact not_parallel 0 (h density velocity density_diff density_pos velocity_diff
      (fun B _ x => divergence_zero B x) 0)

#print axioms OMA.disproof
