import NLS.ComplexAnalysis.ConjugationRealForm
import NLS.ComplexAnalysis.LocalRealAxisDerivative
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! A locally real scalar functional has a real differential on the
fixed real form of an isometric conjugation. The full complex-linear
differential consequently intertwines the two conjugations. -/
noncomputable section
open Set Complex Filter Topology
open scoped ComplexConjugate
namespace NLS.ComplexAnalysis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem fderiv_im_eq_zero_of_fixed_real_germ
    (J : E ≃ₗᵢ⋆[ℂ] E) (F : E → ℂ) (q : E) (hq : J q = q)
    (hF : AnalyticAt ℂ F q)
    (hreal : ∀ᶠ p in 𝓝 q, J p = p → (F p).im = 0)
    (v : E) (hv : J v = v) : ((fderiv ℂ F q) v).im = 0 := by
  have hline : HasDerivAt (fun z : ℂ => q+z • v) v 0 := by
    simpa only [one_smul,id_eq] using! ((hasDerivAt_id (0:ℂ)).smul_const v).const_add q
  have hfc : HasFDerivAt F (fderiv ℂ F q) (q+(0:ℂ) • v) := by
    simpa only [zero_smul,add_zero] using hF.differentiableAt.hasFDerivAt
  have hd := hfc.comp_hasDerivAt 0 hline
  apply HasDerivAt.im_eq_zero_of_eventually_real (fun z : ℂ => F (q+z • v)) _ 0 hd
  have ht : Tendsto (fun t : ℝ => q+(t:ℂ) • v) (𝓝 0) (𝓝 q) := by
    have hc : Continuous (fun t : ℝ => q+(t:ℂ) • v) := by fun_prop
    simpa only [ofReal_zero,zero_smul,add_zero] using hc.tendsto (0:ℝ)
  filter_upwards [ht hreal] with t hp
  apply hp
  rw [map_add,map_smulₛₗ,hq,hv]
  simp

theorem clm_conjugation_of_real_on_fixed_form
    (J : E ≃ₗᵢ⋆[ℂ] E) (hJ : ∀ v, J (J v)=v) (L : E →L[ℂ] ℂ)
    (hL : ∀ v : E, J v = v → (L v).im=0) (v : E) :
    L (J v) = conj (L v) := by
  let a := conjugationRealPart J v
  let b := conjugationImagPart J v
  have ha : J a=a := conjugationRealPart_fixed J hJ v
  have hb : J b=b := conjugationImagPart_fixed J hJ v
  have hra : conj (L a)=L a := conj_eq_iff_im.mpr (hL a ha)
  have hrb : conj (L b)=L b := conj_eq_iff_im.mpr (hL b hb)
  have he : v=a+I • b := conjugation_real_imag_decomp J v
  conv_lhs => rw [he]
  conv_rhs => rw [he]
  simp only [map_add,map_smulₛₗ,RingHom.id_apply,ha,hb,starRingEnd_apply,smul_eq_mul,
    map_mul,hra,hrb]

end NLS.ComplexAnalysis
