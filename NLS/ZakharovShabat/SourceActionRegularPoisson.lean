import NLS.ZakharovShabat.SourceActionRegularCotangent

/-! # Action commutation throughout the full finite exponent range

The constructed regular action cotangents are contour integrals of
regular discriminant variations. Their physical pairing vanishes by
discriminant commutation and the bilinear contour formula. This proves
the action/action part of Corollary 13.2 for every finite `p > 1`.
-/

noncomputable section
open Set Metric Complex NLS.ComplexAnalysis NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem sourceActionVariationRegularCotangent_bivector_eq_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) (z w : ℂ) :
    (sourceActionVariationRegularCotangent hp hp1 φ z).bivector
      (sourceActionVariationRegularCotangent hp hp1 φ w) = 0 := by
  simp only [sourceActionVariationRegularCotangent,
    RegularSourceCotangent.bivector_smul_left, RegularSourceCotangent.bivector_smul_right,
    sourceDiscriminantRegularCotangent_bivector_eq_zero hp hp1 φ, mul_zero]

theorem sourceActionRegularCotangentOnChart_bivector_eq_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n m : ℤ)
    (cn : SourceRealActionBallChart hp hp1 n) (cm : SourceRealActionBallChart hp hp1 m)
    (φ : CoeffPair p) (hn : φ ∈ ball cn.center cn.radius) (hm : φ ∈ ball cm.center cm.radius) :
    (sourceActionRegularCotangentOnChart hp hp1 n cn φ hn).bivector
      (sourceActionRegularCotangentOnChart hp hp1 m cm φ hm) = 0 := by
  have hgn := cn.geometry φ hn
  have hgm := cm.geometry φ hm
  have hcn := sourceCanonicalRootDomain_of_enclosingCircle hp hp1 φ n
    cn.spectralCenter cn.spectralRadius hgn.1 hgn.2
  have hcm := sourceCanonicalRootDomain_of_enclosingCircle hp hp1 φ m
    cm.spectralCenter cm.spectralRadius hgm.1 hgm.2
  have hin := circleIntegrable_sourceActionVariationRegularCoefficients hp hp1 φ
    cn.spectralCenter cn.spectralRadius cn.spectralRadius_pos.le hcn
  have him := circleIntegrable_sourceActionVariationRegularCoefficients hp hp1 φ
    cm.spectralCenter cm.spectralRadius cm.spectralRadius_pos.le hcm
  simp only [sourceActionRegularCotangentOnChart, RegularSourceCotangent.smul,
    RegularSourceCotangent.bivector, RegularSourceCotangent.contourIntegral,
    map_smul, smul_apply, smul_eq_mul]
  rw [bilinear_circleIntegral hilbertPairBivector hin him]
  have hzero (z w : ℂ) :
      hilbertPairBivector (sourceActionVariationRegularCotangent hp hp1 φ z).coefficients
        (sourceActionVariationRegularCotangent hp hp1 φ w).coefficients = 0 :=
    sourceActionVariationRegularCotangent_bivector_eq_zero hp hp1 φ z w
  simp only [hzero]
  simp [circleIntegral]

/-- The actual indexed action derivatives commute at every real
source, including collapsed gaps, for all finite `p > 1`. -/
theorem sourceActionRegularCotangent_bivector_eq_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n m : ℤ) (φ : realTypeSourceLocus p) :
    (sourceActionRegularCotangent hp hp1 n φ).bivector
      (sourceActionRegularCotangent hp hp1 m φ) = 0 := by
  unfold sourceActionRegularCotangent
  exact sourceActionRegularCotangentOnChart_bivector_eq_zero hp hp1 n m _ _ φ.val _ _

/-- Above two this is exactly the previously defined action bracket. -/
theorem sourceActionRegularCotangent_bivector_eq_sourceBracket
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (n m : ℤ) (φ : realTypeSourceLocus p) :
    (sourceActionRegularCotangent hp hp1 n φ).bivector
      (sourceActionRegularCotangent hp hp1 m φ) =
        sourceBracket h2p (sourceComplexAction hp hp1 n) (sourceComplexAction hp hp1 m) φ.val := by
  change _ = (RegularSourceCotangent.ofCotangent h2p (fderiv ℂ (sourceComplexAction hp hp1 n) φ.val)).bivector
    (RegularSourceCotangent.ofCotangent h2p (fderiv ℂ (sourceComplexAction hp hp1 m) φ.val))
  apply RegularSourceCotangent.bivector_congr <;>
    exact sourceActionRegularCotangent_toCotangent hp hp1 _ φ

/-- Absolute convergence of the original Fourier pairing of the
actual action differentials, including below exponent two. -/
theorem sourceAction_pairing_summable_norm
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n m : ℤ) (φ : realTypeSourceLocus p) :
    Summable (fun k : ℤ => ‖
      fderiv ℂ (sourceComplexAction hp hp1 n) φ.val (CoeffPair.inlCLM (lp.single p k 1)) *
        fderiv ℂ (sourceComplexAction hp hp1 m) φ.val (CoeffPair.inrCLM (lp.single p (-k) 1)) -
      fderiv ℂ (sourceComplexAction hp hp1 n) φ.val (CoeffPair.inrCLM (lp.single p k 1)) *
        fderiv ℂ (sourceComplexAction hp hp1 m) φ.val (CoeffPair.inlCLM (lp.single p (-k) 1))‖) := by
  simpa only [sourceActionRegularCotangent_toCotangent] using
    (sourceActionRegularCotangent hp hp1 n φ).summable_norm (sourceActionRegularCotangent hp hp1 m φ)

/-- Corollary 13.2's action/action identity as the literal physical
Fourier bracket of the actual derivatives on the full exponent range. -/
theorem sourceAction_fourier_bracket_eq_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n m : ℤ) (φ : realTypeSourceLocus p) :
    -I * (∑' k : ℤ,
      (fderiv ℂ (sourceComplexAction hp hp1 n) φ.val (CoeffPair.inlCLM (lp.single p k 1)) *
        fderiv ℂ (sourceComplexAction hp hp1 m) φ.val (CoeffPair.inrCLM (lp.single p (-k) 1)) -
      fderiv ℂ (sourceComplexAction hp hp1 n) φ.val (CoeffPair.inrCLM (lp.single p k 1)) *
        fderiv ℂ (sourceComplexAction hp hp1 m) φ.val (CoeffPair.inlCLM (lp.single p (-k) 1)))) = 0 := by
  have h := (sourceActionRegularCotangent hp hp1 n φ).bivector_eq_tsum
    (sourceActionRegularCotangent hp hp1 m φ)
  rw [sourceActionRegularCotangent_bivector_eq_zero hp hp1 n m φ] at h
  simpa only [sourceActionRegularCotangent_toCotangent] using h.symm

end NLS.ZakharovShabat
