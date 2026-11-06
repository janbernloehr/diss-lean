import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Normed.Operator.Banach

/-! # The fixed global real inverse is analytic at a bijective derivative -/
noncomputable section
set_option autoImplicit false
open Filter Topology
namespace NLS.ComplexAnalysis

theorem analyticAt_equiv_symm_of_fderiv_bijective
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (e : E ≃ F) (a : E) (hf : AnalyticAt ℝ e a)
    (hb : Function.Bijective (fderiv ℝ e a)) : AnalyticAt ℝ e.symm (e a) := by
  let i := ContinuousLinearEquiv.ofBijective (fderiv ℝ e a)
    (LinearMap.ker_eq_bot.mpr hb.1) (LinearMap.range_eq_top.mpr hb.2)
  have hd : HasStrictFDerivAt e i.toContinuousLinearMap a := hf.hasStrictFDerivAt
  let P := hd.toOpenPartialHomeomorph e
  have hP : (P : E → F)=e := hd.toOpenPartialHomeomorph_coe
  have haP : a∈P.source := hd.mem_toOpenPartialHomeomorph_source
  have hga : AnalyticAt ℝ P.symm (e a) := by
    have h := P.analyticAt_symm' haP (by rw [hP];exact hf)
      (i := i) (by rw [hP];rfl)
    rwa [hP] at h
  apply hga.congr
  have htarget : e a∈P.target := by rw [←hP];exact P.map_source haP
  filter_upwards [P.open_target.mem_nhds htarget] with y hy
  apply e.injective
  rw [e.apply_symm_apply]
  rw [←hP]
  exact P.right_inv hy

end NLS.ComplexAnalysis
