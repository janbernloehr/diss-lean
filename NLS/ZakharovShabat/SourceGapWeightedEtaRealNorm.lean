import NLS.ZakharovShabat.SourceGapWeightedEtaSquare
import NLS.ZakharovShabat.SourceAngularOriginalEtaIntegral

/-! # Exact original eta norm on any actual real source domain

This uses the original integral phase and its proved real value. No
strong-source estimates or global H1 assumptions are required.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceLemma12_12Data
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {W₀ W : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

theorem norm_gapWeightedEta_original_eq_gap (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (hr : IsRealType (CoeffPair.toMax p ψ)) (n : ℤ) :
    ‖sourceGapWeightedEtaCoordinate hp hp1 n s 1 ψ‖ = ‖sourcePeriodicGapDisplacement hp hp1 ψ n‖ := by
  by_cases hg : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n = 0
  · rw [H.gapWeightedEta_original_closed ψ hψ hr n hg 1,sourcePeriodicGapDisplacement_apply,hg]
  · have hη := H.eta_original_integral_im_eq_zero ψ hψ hr n hg
    rw [H.gapWeightedEta_original_plus ψ hψ n hg,norm_mul,Complex.norm_exp]
    have he : (I*sourceAngularOriginalEta hp hp1 n s ψ).re = 0 := by
      simp only [mul_re,I_re,I_im,zero_mul,one_mul,zero_sub,hη,neg_zero]
    rw [he,Real.exp_zero,mul_one,sourcePeriodicGapDisplacement_apply]

end NLS.ZakharovShabat.SourceLemma12_12Data
