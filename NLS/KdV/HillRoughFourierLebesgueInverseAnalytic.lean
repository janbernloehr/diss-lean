import NLS.KdV.HillRoughFourierLebesgueCompactDerivative
import NLS.KdV.HillRoughFourierLebesgueDerivativeInjective
import NLS.FunctionalAnalysis.CompactEquivPerturbationScalar
import NLS.ComplexAnalysis.RealAnalyticEquivInverse

/-! # Native analyticity of the already-fixed physical inverse

The actual derivative is injective by the weak inclusion diagram and a
compact perturbation of its literal bounded Fourier principal. The
Fredholm alternative gives bijectivity in both original native norms.
-/
noncomputable section
set_option autoImplicit false
open Set
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData

theorem fourierLebesgueForward_fderiv_bijective_of_two_lt (D : GlobalRoughAbelianForwardData)
    (s p : ℝ) (hs : -1/2≤s) (hp : 2<p) [Fact (1≤ENNReal.ofReal p)]
    (a : physicalRealMeanZeroWeightedExponent (Weight.sobolev s) (ENNReal.ofReal p)) :
    Function.Bijective (fderiv ℝ (D.fourierLebesgueForward s hs (ENNReal.ofReal p)
      ENNReal.ofReal_ne_top (by exact_mod_cast ENNReal.ofReal_le_ofReal hp.le)) a) := by
  obtain ⟨Q,hQ⟩ := D.exists_fourierLebesgueForward_compact_principal s p hs hp a
  exact NLS.bijective_of_compact_sub_equiv_of_injective_scalar _ Q hQ
    (D.fourierLebesgueForward_fderiv_injective s hs (ENNReal.ofReal p) ENNReal.ofReal_ne_top
      (by exact_mod_cast ENNReal.ofReal_le_ofReal hp.le) a)

theorem fourierLebesgueEquiv_symm_analytic_of_two_lt (D : GlobalRoughAbelianForwardData)
    (s p : ℝ) (hs : -1/2≤s) (hp : 2<p) [Fact (1≤ENNReal.ofReal p)] :
    AnalyticOnNhd ℝ (D.fourierLebesgueEquiv s hs (ENNReal.ofReal p)
      ENNReal.ofReal_ne_top (by exact_mod_cast ENNReal.ofReal_le_ofReal hp.le)).symm univ := by
  let h2p : (2 : ℝ≥0∞)≤ENNReal.ofReal p := by exact_mod_cast ENNReal.ofReal_le_ofReal hp.le
  let e := D.fourierLebesgueEquiv s hs (ENNReal.ofReal p) ENNReal.ofReal_ne_top h2p
  intro b _
  have hf : AnalyticAt ℝ e (e.symm b) :=
    D.fourierLebesgueForward_analytic s hs (ENNReal.ofReal p) ENNReal.ofReal_ne_top h2p _ (mem_univ _)
  have h := NLS.ComplexAnalysis.analyticAt_equiv_symm_of_fderiv_bijective e (e.symm b) hf
    (D.fourierLebesgueForward_fderiv_bijective_of_two_lt s p hs hp (e.symm b))
  simpa only [e.apply_symm_apply] using h

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
