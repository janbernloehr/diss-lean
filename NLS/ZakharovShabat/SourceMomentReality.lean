import NLS.ZakharovShabat.SourceAbelianMomentRealCosine
import NLS.ZakharovShabat.SourceAngularRealNumerator
import NLS.ZakharovShabat.SourceSecondMomentFrequencyAnalytic

/-! # Reality of the actual moments and renormalized frequencies -/
noncomputable section
open Set Metric Complex ComplexConjugate Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {W V : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- On a real selected gap the even-moment numerator is purely imaginary,
including the filled values at endpoints and collapsed gaps. -/
theorem sourceAbelianMomentEvenNumerator_re_eq_zero_on_real_gap
    (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiIsolatingComplexExtension hp hp1 V s)
    (φ : realTypeSourceSubmodule p) (n k : ℤ) (m : ℕ) (z : ℂ)
    (hz : z ∈ sourcePeriodicSegment hp hp1 φ.val k) :
    (sourceAbelianMomentEvenNumerator hp hp1 W n k m (s n φ.val : Coeff p) φ.val z).re = 0 := by
  let φ₀ : realTypeSourceLocus p := ⟨φ.val,φ.property⟩
  obtain ⟨D⟩ := (A.localChart φ₀).charts φ.val (mem_ball_self (A.localChart φ₀).radius_pos)
  have hzI := sourcePeriodicSegment_re_mem_Icc hp hp1 φ.val k z hz
  have hzim := sourcePeriodicSegment_im_eq_zero_of_realType hp hp1 φ.val φ.property k z hz
  have hzreal : (z.re : ℂ) = z := by simpa [hzim] using Complex.re_add_im z
  have hnum : (sourcePsiCandidate n (z,(s n φ.val : Coeff p))).im = 0 := by
    have hc := sourcePsiCandidate_conj_of_real_roots hp hp1 n (s n φ.val : Coeff p)
      (hs.displacedRoots_im_eq_zero_of_realType φ.val φ.property n) z
    rw [Complex.conj_eq_iff_im.mpr hzim] at hc
    exact Complex.conj_eq_iff_im.mp hc.symm
  have hden : (sourceStandardRootOmittedProduct hp hp1 k φ.val z).im = 0 := by
    rw [← hzreal]
    exact sourceStandardRootOmittedProduct_im_eq_zero_on_realGap_closedGap hp hp1 φ.val φ.property k z.re hzI
  have hsquare : sourceFullAbelianSquare hp hp1 W k (z,φ.val) =
      (sourceRealGapArcoshProfile hp φ.val k z.re : ℂ)^2 := by
    rw [sourceFullAbelianSquare_eq_real φ D k,← hzreal]
    exact sourceAbelianSquare_eq_arcosh_sq hp hp1 φ.val φ.property k z.re hzI
  rw [sourceAbelianMomentEvenNumerator,hsquare]
  have hpow : (((sourceRealGapArcoshProfile hp φ.val k z.re : ℂ)^2)^m).im = 0 := by
    rw [← Complex.ofReal_pow,← Complex.ofReal_pow]
    rfl
  simp [sourceMomentRegularNumerator,Complex.mul_re,Complex.mul_im,Complex.div_re,hnum,hden,hpow]

namespace SourceAbelianMomentAtlas

/-- Every positive even moment at an actual real source is real. -/
theorem positive_even_moment_im_eq_zero
    (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiIsolatingComplexExtension hp hp1 V s)
    (φ : realTypeSourceSubmodule p) (n k : ℤ) (m : ℕ) :
    (A.moment n k (2*(m+1)) φ.val).im = 0 := by
  let f := fun θ : ℝ => sourceAbelianMomentEvenNumerator hp hp1 W n k (m+1)
    (s n φ.val : Coeff p) φ.val (sourceStandardRootMidpoint hp hp1 φ.val k +
      sourceStandardRootHalfGap hp hp1 φ.val k * (Real.cos θ : ℂ))
  have hf (θ : ℝ) : conj (f θ) = -f θ := by
    have hz : sourceStandardRootMidpoint hp hp1 φ.val k +
        sourceStandardRootHalfGap hp hp1 φ.val k * (Real.cos θ : ℂ) ∈
          sourcePeriodicSegment hp hp1 φ.val k := by
      rw [sourcePeriodicSegment_eq_midpoint_segment]
      simpa only [cosineGapPoint,← Complex.ofReal_cos] using cosineGapPoint_real_mem_segment
        (sourceStandardRootMidpoint hp hp1 φ.val k) (sourceStandardRootHalfGap hp hp1 φ.val k) θ
    have hr := sourceAbelianMomentEvenNumerator_re_eq_zero_on_real_gap A hs φ n k (m+1) _ hz
    change (f θ).re = 0 at hr
    apply Complex.ext <;>
      simp only [Complex.conj_re,Complex.neg_re,Complex.conj_im,Complex.neg_im,hr,neg_zero]
  have hint : conj (∫ θ in (0:ℝ)..Real.pi, f θ) = -(∫ θ in (0:ℝ)..Real.pi, f θ) := by
    calc
      conj (∫ θ in (0:ℝ)..Real.pi, f θ) = ∫ θ in (0:ℝ)..Real.pi, conj (f θ) := by
        simp only [intervalIntegral, map_sub, integral_conj]
      _ = _ := by simp_rw [hf]; rw [intervalIntegral.integral_neg]
  rw [A.real_positive_even_moment_eq_cosineMean φ n k m]
  change (-(2*Complex.I)*(∫ θ in (0:ℝ)..Real.pi, f θ)).im = 0
  apply Complex.conj_eq_iff_im.mp
  rw [map_mul,map_neg,map_mul,hint]
  simp [Complex.conj_ofNat]

/-- The actual renormalized frequency is real at every real source. -/
theorem renormalizedFrequency_im_eq_zero
    (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiIsolatingComplexExtension hp hp1 V s)
    (φ : realTypeSourceSubmodule p) (n : ℤ) :
    (A.renormalizedFrequency n φ.val).im = 0 := by
  have hm (k : ℤ) : conj (A.moment n k 2 φ.val) = A.moment n k 2 φ.val :=
    Complex.conj_eq_iff_im.mpr (A.positive_even_moment_im_eq_zero hs φ n k 0)
  apply Complex.conj_eq_iff_im.mp
  simp [renormalizedFrequency,Complex.conj_tsum,Complex.conj_ofNat,hm]

end SourceAbelianMomentAtlas
end NLS.ZakharovShabat
