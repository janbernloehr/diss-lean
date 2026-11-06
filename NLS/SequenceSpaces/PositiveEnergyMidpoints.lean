import NLS.SequenceSpaces.PositiveEnergyDisplacements

/-! # Native normalized energy midpoints from symmetric frequency data -/
noncomputable section
set_option autoImplicit false
open Set Complex
namespace NLS.Coeff

def positiveEnergyMidpoints (c : ℝ) (d : Coeff 2) (g : Coeff 1) : Coeff 2 :=
  positiveEnergyDisplacements c d +
    (1/4 : ℂ) • multiplierCLM positiveIndexReciprocal
      (positiveDeletedProjection 2 0 (exponentInclusion (by norm_num : (1 : ENNReal) ≤ 2) g))

theorem analyticOnNhd_positiveEnergyMidpoints (c : ℝ) :
    AnalyticOnNhd ℂ (fun t : Coeff 2 × Coeff 1 => positiveEnergyMidpoints c t.1 t.2) univ := by
  intro t _
  have hd := (analyticOnNhd_positiveEnergyDisplacements c t.1 (mem_univ _)).comp analyticAt_fst
  have hg := ((exponentInclusion (by norm_num : (1 : ENNReal) ≤ 2)).analyticAt t.2).comp analyticAt_snd
  have hp := ((positiveDeletedProjection 2 0).analyticAt _).comp hg
  have hr := ((multiplierCLM (p := 2) positiveIndexReciprocal).analyticAt _).comp hp
  exact hd.add (hr.const_smul (c := (1/4 : ℂ)))

theorem positiveEnergyMidpoints_positive (c : ℝ) (d : Coeff 2) (g : Coeff 1) (n : ℕ+) :
    positiveEnergyMidpoints c d g (n : ℤ) =
      (((Real.pi : ℂ)*(n : ℕ)+d (n : ℤ))^2+g (n : ℤ)/4-
        (c : ℂ)^2-((Real.pi : ℂ)*(n : ℕ))^2)/(n : ℂ) := by
  have hn : (0 : ℤ) < (n : ℤ) := by exact_mod_cast n.property
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast n.ne_zero
  simp only [positiveEnergyMidpoints,lp.coeFn_add,Pi.add_apply,
    positiveEnergyDisplacements_positive,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,
    multiplierCLM_apply,multiplier_apply,positiveDeletedProjection_apply,
    if_pos (show 0 < (n : ℤ) ∧ (n : ℤ) ≠ 0 from ⟨hn,ne_of_gt hn⟩),
    exponentInclusion_apply,positiveIndexReciprocal_apply,positiveIndexWeight,if_pos hn]
  simp only [Int.cast_natCast]
  field_simp [hn0]
  ring

theorem positiveEnergyMidpoints_nonpositive (c : ℝ) (d : Coeff 2) (g : Coeff 1)
    (j : ℤ) (hj : j ≤ 0) : positiveEnergyMidpoints c d g j = 0 := by
  simp only [positiveEnergyMidpoints,lp.coeFn_add,Pi.add_apply,
    positiveEnergyDisplacements_nonpositive c d j hj,lp.coeFn_smul,Pi.smul_apply,
    smul_eq_mul,multiplierCLM_apply,multiplier_apply,positiveDeletedProjection_apply,
    if_neg (show ¬(0 < j ∧ j ≠ 0) from fun h => (not_lt.mpr hj) h.1),
    mul_zero,zero_add]

end NLS.Coeff
