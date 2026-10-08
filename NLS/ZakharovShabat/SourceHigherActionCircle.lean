import NLS.ZakharovShabat.SourcePrimitivePowerCircle
import NLS.ComplexAnalysis.CirclePolynomialIntegrationByParts

/-! # The higher-level action contour from Section 24

The natural index `k` represents level `k+1`. Integration by parts gives
exactly `-1/pi` times the contour integral of `z^k F_n(z)`.
-/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The defining higher-action contour with the dissertation's normalization. -/
def sourceHigherActionCircle (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (c : ℂ) (R : ℝ) (k : ℕ) : ℂ :=
  ((k+1 : ℂ)*(Real.pi : ℂ))⁻¹ *
    ∮ z in C(c,R), z^(k+1) * sourceCriticalRootRatioJoint hp hp1 (z,ψ)

/-- Formula (5.2), with no analyticity through the enclosed cut assumed. -/
theorem sourceHigherActionCircle_eq_primitive
    (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p)) (n : ℤ)
    (ψ : CoeffPair p) (D : SourceAbelianSpectralChart hp hp1 W ψ)
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hc : sphere c R ⊆ sourceCanonicalRootDomain hp hp1 ψ) (k : ℕ) :
    sourceHigherActionCircle hp hp1 ψ c R k =
      -(Real.pi : ℂ)⁻¹ * ∮ z in C(c,R), z^k * sourceFullAbelianPrimitive hp hp1 W n (z,ψ) := by
  let F : ℂ → ℂ := fun z => sourceFullAbelianPrimitive hp hp1 W n (z,ψ)
  have hi := circleIntegral_pow_mul_deriv_eq_neg F
    (sourceOpenGapComplement hp hp1 ψ) (sourceFullAbelianPrimitive_spectral_analytic D n)
    c R hR (hc.trans (sourceCanonicalRootDomain_subset_openGapComplement hp hp1 ψ)) k
  have he : (∮ z in C(c,R), z^(k+1)*sourceCriticalRootRatioJoint hp hp1 (z,ψ)) =
      ∮ z in C(c,R), z^(k+1)*deriv F z := by
    apply circleIntegral.integral_congr hR
    intro z hz
    exact congrArg (fun v => z^(k+1)*v) (sourceFullAbelianPrimitive_hasDerivAt D n z (hc hz)).deriv.symm
  rw [sourceHigherActionCircle,he,hi]
  have hk : (k+1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  dsimp only [F]
  field_simp

@[simp] theorem sourceHigherActionCircle_zero (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (c : ℂ) (R : ℝ) :
    sourceHigherActionCircle hp hp1 ψ c R 0 = sourceActionCircle hp hp1 ψ c R := by
  simp only [sourceHigherActionCircle,Nat.cast_zero,zero_add,one_mul,pow_one,sourceActionCircle]

end NLS.ZakharovShabat
