import NLS.ComplexAnalysis.AnalyticTwoZeroRoot
import NLS.ZakharovShabat.SourceStandardRootRealExteriorSign
import NLS.ComplexAnalysis.RealGapEllipse

/-! # The standard root is strictly positive and real to the left of ordered real endpoints. -/

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
open NLS.ZakharovShabat
namespace NLS.ComplexAnalysis
theorem endpointRoot_real_left (a b x : ℝ) (hab : a ≤ b) (hx : x < a) :
    0 < (endpointRoot a b x).re ∧ (endpointRoot a b x).im = 0 := by
  have hp : 0 < (endpointRoot a b x).re := by
    simpa only [endpointRoot,ofReal_div,ofReal_add,ofReal_sub,ofReal_pow,ofReal_ofNat] using
      normalizedStandardRoot_re_pos_of_lt_leftEndpoint a b x hab hx
  have hs : (x : ℂ) ∉ segment ℝ (a : ℂ) b := by
    intro h
    have hbound := re_mem_Icc_of_mem_real_segment a b hab (x : ℂ) h
    simp only [ofReal_re] at hbound
    linarith [hbound.1]
  have hi := congrArg Complex.im (endpointRoot_sq a b x hs)
  simp only [pow_two,mul_im,sub_im,ofReal_im,sub_self,mul_zero,zero_mul,add_zero] at hi
  exact ⟨hp,by nlinarith⟩

end NLS.ComplexAnalysis
