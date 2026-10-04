import NLS.ZakharovShabat.SourceAbelianMomentCancellation
import NLS.ZakharovShabat.SourceFullAbelianSquare
import NLS.ZakharovShabat.SourceStandardRootOmittedJointAnalytic

/-! # The analytic numerator of even Abelian moments

The canonical filled square removes the primitive's slit. Every even
moment is a weighted selected-root integral whose numerator is analytic
across the selected gap, including its endpoints.
-/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The filled numerator for order `2*m`, before dividing by the selected root. -/
def sourceAbelianMomentEvenNumerator (hp : p ≠ ⊤) (hp1 : 1 < p)
    (W : Set (CoeffPair p)) (n k : ℤ) (m : ℕ) (a : Coeff p) (ψ : CoeffPair p) (z : ℂ) : ℂ :=
  (sourceFullAbelianSquare hp hp1 W k (z,ψ))^m * sourceMomentRegularNumerator hp hp1 n k a ψ z

/-- The weighted representation agrees with the original integrand
throughout the canonical root domain, for complex sources as well. -/
theorem sourceAbelianMomentIntegrand_even_eq_weighted
    (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p))
    (n k : ℤ) (m : ℕ) (a : Coeff p) (ψ : CoeffPair p)
    (D : SourceAbelianSpectralChart hp hp1 W ψ)
    (z : ℂ) (hz : z ∈ sourceCanonicalRootDomain hp hp1 ψ) :
    sourceAbelianMomentIntegrand hp hp1 W n k (2*m) (z,(a,ψ)) =
      sourceAbelianMomentEvenNumerator hp hp1 W n k m a ψ z / sourceStandardRoot hp hp1 ψ k z := by
  unfold sourceAbelianMomentIntegrand sourceAbelianMomentEvenNumerator
  have he := sourceFullAbelianSquare_eq_sq D k
    (sourceCanonicalRootDomain_subset_openGapComplement hp hp1 ψ hz)
  dsimp only at he ⊢
  rw [he,sourcePsiContourIntegrand_eq_regular_div_root,pow_mul,mul_div_assoc]

/-- Exact weighted-circle representation of every even moment. -/
theorem sourceAbelianMomentCircle_even_eq_weighted
    (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p))
    (n k : ℤ) (m : ℕ) (a : Coeff p) (ψ : CoeffPair p)
    (D : SourceAbelianSpectralChart hp hp1 W ψ)
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hcircle : sphere c R ⊆ sourceCanonicalRootDomain hp hp1 ψ) :
    sourceAbelianMomentCircle hp hp1 W n k (2*m) a ψ c R =
      ∮ z in C(c,R), sourceAbelianMomentEvenNumerator hp hp1 W n k m a ψ z /
        sourceStandardRoot hp hp1 ψ k z := by
  apply circleIntegral.integral_congr hR
  intro z hz
  exact sourceAbelianMomentIntegrand_even_eq_weighted hp hp1 W n k m a ψ D z (hcircle hz)

/-- On a common Cauchy neighborhood, filling the square gives an analytic
numerator on the plane with only the other gaps removed. -/
theorem SourceFullAbelianUniformCauchyFamily.evenNumerator_analytic
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W)
    (ψ : CoeffPair p) (hψ : ψ ∈ ball C.discs.source.val C.discs.sourceRadius)
    (n k : ℤ) (m : ℕ) (a : Coeff p)
    (hO : AnalyticOnNhd ℂ (sourceStandardRootOmittedProduct hp hp1 k ψ)
      (sourceStandardRootOmittedDomain hp hp1 ψ k)) :
    AnalyticOnNhd ℂ (sourceAbelianMomentEvenNumerator hp hp1 W n k m a ψ)
      (sourceStandardRootOmittedDomain hp hp1 ψ k) := by
  intro z hz
  exact ((C.fullSquare_analytic k ψ hψ z (fun j hj _ => hz j hj)).pow m).mul
    (sourceMomentRegularNumerator_analyticOnNhd hp hp1 n k a ψ hO z hz)

/-- At any real source, the canonical numerator is analytic across its
gap with no supplied Cauchy family or omitted-product regularity premise. -/
theorem sourceAbelianMomentEvenNumerator_real_analytic
    (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p))
    (φ : realTypeSourceSubmodule p) (D : SourceAbelianSpectralChart hp hp1 W φ.val)
    (n k : ℤ) (m : ℕ) (a : Coeff p) :
    AnalyticOnNhd ℂ (sourceAbelianMomentEvenNumerator hp hp1 W n k m a φ.val)
      (sourceStandardRootOmittedDomain hp hp1 φ.val k) := by
  obtain ⟨V,_,_,hfamilies⟩ := exists_sourceFullAbelianUniformCauchyFamilies hp hp1
  obtain ⟨C,hC⟩ := hfamilies φ
  have hφ : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius := by
    rw [hC]
    exact mem_ball_self C.discs.sourceRadius_pos
  obtain ⟨E⟩ := C.charts φ.val hφ
  obtain ⟨O,_,_,hrealO,hOdata⟩ := exists_global_source_analytic_omittedJointProduct hp hp1
  have hO := sourceStandardRootOmittedProduct_analyticOnNhd_spectral hp hp1 k O
    (hOdata k).2.1 φ.val (hrealO φ.property)
  have he : sourceAbelianMomentEvenNumerator hp hp1 W n k m a φ.val =
      sourceAbelianMomentEvenNumerator hp hp1 V n k m a φ.val := by
    funext z
    unfold sourceAbelianMomentEvenNumerator
    rw [sourceFullAbelianSquare_independent_neighborhood D E]
  rw [he]
  exact C.evenNumerator_analytic φ.val hφ n k m a hO

end NLS.ZakharovShabat
