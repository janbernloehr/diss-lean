import NLS.MKdV.MiuraCentralHalfTurnConstants

/-! # The central half turn reverses the signed mean globally

An affine path from a physical profile to its constant mean stays in
the same mean leaf. The actual half-turn mean is continuous there and
has fixed square. The verified constant value determines its sign.
-/
noncomputable section
open Set Complex Filter Topology
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

theorem miuraRealL2_mean_im_eq_zero (a : MiuraRealL2) : (a.val 0).im = 0 := by
  have h := congrArg Complex.im (a.property 0)
  simp only [neg_zero,Complex.conj_im] at h
  linarith

/-- The actual central NLS half turn changes the literal signed mean to
its negative on the entire physical original-L2 diagonal. -/
theorem miuraCentralHalfTurn_mean (a : MiuraRealL2) : (miuraCentralHalfTurn a).val 0 = -a.val 0 := by
  by_cases hm : a.val 0 = 0
  · have h := miuraCentralHalfTurn_mean_square a
    rw [hm,zero_pow (by norm_num : 2 ≠ 0)] at h
    simpa only [hm,neg_zero] using sq_eq_zero_iff.mp h
  let c := miuraRealConstant (a.val 0).re
  have hc : c.val 0 = a.val 0 := by
    rw [miuraRealConstant_mean]
    have hr : a.val 0 = ((a.val 0).re : ℂ) := by
      apply Complex.ext
      · rfl
      · exact miuraRealL2_mean_im_eq_zero a
    exact hr.symm
  let γ : ℝ → MiuraRealL2 := fun t => a+t • (c-a)
  have hγ : Continuous γ := continuous_const.add (continuous_id.smul continuous_const)
  have hγ0 : γ 0 = a := by simp [γ]
  have hγ1 : γ 1 = c := by change a+(1 : ℝ) • (c-a) = c; rw [one_smul]; abel
  have hmean (t : ℝ) : (γ t).val 0 = a.val 0 := by
    change a.val 0+t • (c.val 0-a.val 0) = a.val 0
    rw [hc,sub_self,smul_zero,add_zero]
  let F : ℝ → ℂ := fun t => (miuraCentralHalfTurn (γ t)).val 0
  have hF : Continuous F := (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 0).continuous.comp
    (continuous_subtype_val.comp (continuous_miuraCentralHalfTurn.comp hγ))
  have hsq (t : ℝ) : (F t)^2 = (-a.val 0)^2 := by
    have h := miuraCentralHalfTurn_mean_square (γ t)
    rw [hmean t] at h
    simpa only [F,neg_sq] using h
  have hF1 : F 1 = -a.val 0 := by
    change (miuraCentralHalfTurn (γ 1)).val 0 = -a.val 0
    rw [hγ1]
    change (miuraCentralHalfTurn (miuraRealConstant (a.val 0).re)).val 0 = -a.val 0
    rw [miuraCentralHalfTurn_constant_mean]
    exact congrArg Neg.neg hc
  have hG : ContinuousOn (fun _ : ℝ => -a.val 0) univ := continuousOn_const
  have he := isPreconnected_univ.eq_of_sq_eq hF.continuousOn hG
    (fun t _ => hsq t) (fun _ => neg_ne_zero.mpr hm) (mem_univ (1 : ℝ)) hF1
  simpa only [F,hγ0] using he (mem_univ (0 : ℝ))

end NLS.MKdV
