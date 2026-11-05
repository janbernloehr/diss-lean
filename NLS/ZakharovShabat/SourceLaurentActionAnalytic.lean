import NLS.ZakharovShabat.SourceLaurentActionContour
import NLS.ComplexAnalysis.ParametricCircleIntegralHigher

/-! # Banach analyticity of actual Laurent-weighted action contours

The weight has arbitrary integer exponent. A fixed zero-excluding circle
therefore supplies all levels on the same open source neighborhood.
-/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem sourceLaurentPrimitiveCircle_analyticOnNhd
    (hp : p ≠ ⊤) (hp1 : 1 < p) (W U : Set (CoeffPair p)) (n k : ℤ)
    (hU : IsOpen U) (hD : IsOpen (sourceCanonicalRootJointDomain hp hp1 U))
    (hF : AnalyticOnNhd ℂ (sourceFullAbelianPrimitive hp hp1 W n)
      (sourceCanonicalRootJointDomain hp hp1 U))
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hc : ∀ ψ ∈ U, sphere c R ⊆ sourceCanonicalRootDomain hp hp1 ψ)
    (hzero : (0 : ℂ) ∉ sphere c R) :
    AnalyticOnNhd ℂ (fun ψ => sourceLaurentPrimitiveCircle hp hp1 W n k ψ c R) U := by
  let D := sourceCanonicalRootJointDomain hp hp1 U ∩ {t : ℂ × CoeffPair p | t.1 ≠ 0}
  have hDopen : IsOpen D := hD.inter (isOpen_ne_fun continuous_fst continuous_const)
  have hi := analyticOnNhd_circleIntegral_of_jointAnalytic
    (fun t : ℂ × CoeffPair p => t.1^(k-1)*sourceFullAbelianPrimitive hp hp1 W n t)
    hDopen (fun t ht => (analyticAt_fst.zpow ht.2).mul (hF t ht.1)) c R hR hU
    (fun ψ hψ z hz => ⟨⟨hψ,hc ψ hψ hz⟩,by intro he; exact hzero (he ▸ hz)⟩)
  exact fun ψ hψ => analyticAt_const.mul (hi ψ hψ)

end NLS.ZakharovShabat
