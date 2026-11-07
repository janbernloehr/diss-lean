import NLS.ZakharovShabat.SourceIndexedHigherAction
import NLS.ZakharovShabat.SourcePeriodCircleSymmetries
import NLS.ComplexAnalysis.CircleIntegralReflection

/-! # Exact higher-action contour substitutions

The actual critical/root quotient is even under simultaneous source and
spectral reflection. The derivative of z -> -z supplies the orientation
factor, leaving precisely the parity of the printed level minus one.
-/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem sourceCriticalRootRatioJoint_componentSwap (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (z : ℂ) :
    sourceCriticalRootRatioJoint hp hp1 (-z,sourceComponentSwap φ) =
      sourceCriticalRootRatioJoint hp hp1 (z,φ) := by
  simp only [sourceCriticalRootRatioJoint,sourceDiscriminant_deriv_componentSwap hp hp1 φ z,
    sourceCanonicalRoot_componentSwap,div_neg,neg_div,neg_neg]

theorem sourceCriticalRootRatioJoint_midpointReflection (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (z : ℂ) :
    sourceCriticalRootRatioJoint hp hp1 (-z,sourceMidpointReflection φ) =
      sourceCriticalRootRatioJoint hp hp1 (z,φ) := by
  simp only [sourceCriticalRootRatioJoint,sourceDiscriminant_deriv_midpointReflection hp hp1 φ z,
    sourceCanonicalRoot_midpointReflection,div_neg,neg_div,neg_neg]

theorem sourceCriticalRootRatioJoint_reciprocalScaling (hp : p ≠ ⊤) (hp1 : 1 < p)
    (c : ℂ) (hc : c ≠ 0) (φ : CoeffPair p) (z : ℂ) :
    sourceCriticalRootRatioJoint hp hp1 (z,sourceReciprocalScaling c φ) =
      sourceCriticalRootRatioJoint hp hp1 (z,φ) := by
  simp only [sourceCriticalRootRatioJoint,sourceDiscriminant_deriv_reciprocalScaling hp hp1 c hc,
    sourceCanonicalRoot_reciprocalScaling hp hp1 c hc]

theorem sourceHigherActionCircle_spectralNegation (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ χ : CoeffPair p) (c : ℂ) (R : ℝ) (k : ℕ)
    (h : ∀ z, sourceCriticalRootRatioJoint hp hp1 (-z,χ) =
      sourceCriticalRootRatioJoint hp hp1 (z,φ)) :
    sourceHigherActionCircle hp hp1 χ (-c) R k =
      (-1:ℂ)^k*sourceHigherActionCircle hp hp1 φ c R k := by
  unfold sourceHigherActionCircle
  rw [← circleIntegral_neg_pullback]
  have he : (fun z : ℂ => -((-z)^(k+1)*sourceCriticalRootRatioJoint hp hp1 (-z,χ))) =
      (fun z : ℂ => (-1:ℂ)^k*(z^(k+1)*sourceCriticalRootRatioJoint hp hp1 (z,φ))) := by
    funext z
    rw [h z,neg_pow,pow_succ (-1:ℂ)]
    ring
  rw [he,circleIntegral.integral_const_mul]
  ring

theorem sourceIndexedHigherAction_componentSwap (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (n : ℤ) (D : SourceCriticalRootPeriodCircle hp hp1 φ n) (k : ℕ) :
    sourceIndexedHigherAction hp hp1 (-n) k (sourceComponentSwap φ) =
      (-1:ℂ)^k*sourceIndexedHigherAction hp hp1 n k φ := by
  rw [sourceIndexedHigherAction_eq_circle D.componentSwap,sourceIndexedHigherAction_eq_circle D]
  change sourceHigherActionCircle hp hp1 _ ((-D.center : ℝ) : ℂ) D.radius k = _
  rw [ofReal_neg]
  exact sourceHigherActionCircle_spectralNegation hp hp1 φ _ _ _ k
    (sourceCriticalRootRatioJoint_componentSwap hp hp1 φ)

theorem sourceIndexedHigherAction_midpointReflection (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (n : ℤ) (D : SourceCriticalRootPeriodCircle hp hp1 φ n) (k : ℕ) :
    sourceIndexedHigherAction hp hp1 (-n) k (sourceMidpointReflection φ) =
      (-1:ℂ)^k*sourceIndexedHigherAction hp hp1 n k φ := by
  rw [sourceIndexedHigherAction_eq_circle D.midpointReflection,sourceIndexedHigherAction_eq_circle D]
  change sourceHigherActionCircle hp hp1 _ ((-D.center : ℝ) : ℂ) D.radius k = _
  rw [ofReal_neg]
  exact sourceHigherActionCircle_spectralNegation hp hp1 φ _ _ _ k
    (sourceCriticalRootRatioJoint_midpointReflection hp hp1 φ)

theorem sourceIndexedHigherAction_reciprocalScaling (hp : p ≠ ⊤) (hp1 : 1 < p)
    (c : ℂ) (hc : c ≠ 0) (φ : CoeffPair p) (n : ℤ)
    (D : SourceCriticalRootPeriodCircle hp hp1 φ n) (k : ℕ) :
    sourceIndexedHigherAction hp hp1 n k (sourceReciprocalScaling c φ) =
      sourceIndexedHigherAction hp hp1 n k φ := by
  rw [sourceIndexedHigherAction_eq_circle (D.reciprocalScaling c hc),sourceIndexedHigherAction_eq_circle D]
  change sourceHigherActionCircle hp hp1 _ (D.center:ℂ) D.radius k = _
  unfold sourceHigherActionCircle
  apply congrArg (((k+1:ℂ)*(Real.pi:ℂ))⁻¹ * ·)
  apply circleIntegral.integral_congr D.radius_pos.le
  intro z _
  dsimp only
  rw [sourceCriticalRootRatioJoint_reciprocalScaling hp hp1 c hc]

end NLS.ZakharovShabat
