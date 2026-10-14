import NLS.ZakharovShabat.SourceCanonicalRootBoundaryDomain
import NLS.ZakharovShabat.SourcePsiFree
import NLS.ZakharovShabat.SourceCanonicalRootUpperParitySign
import NLS.ZakharovShabat.SourceCanonicalRootRealBand

/-!
# Canonical-root normalization and the signs in Figure 2.4

The free function is entire with value -2i at pi/2. A collapsed gap
retains a simple zero with derivative -2i f_n(tau_n). The real-source
boundary and adjacent-band signs include every negative integer index.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- At zero source the canonical product is the entire function with its actual negative sign. -/
theorem sourceCanonicalRoot_zero_source_entire (hp : p ≠ ⊤) (hp1 : 1 < p) :
    AnalyticOnNhd ℂ (sourceCanonicalRoot hp hp1 (0 : CoeffPair p)) univ := by
  have he := funext (sourceCanonicalRoot_zero_source_eq_free_sine hp hp1 0)
  rw [he]
  exact analyticOnNhd_const.mul Complex.analyticOnNhd_sin

/-- A concrete free value fixes the choice of square-root sign. -/
theorem sourceCanonicalRoot_zero_source_halfPi (hp : p ≠ ⊤) (hp1 : 1 < p) :
    sourceCanonicalRoot hp hp1 (0 : CoeffPair p) ((Real.pi:ℂ)/2) = -2*Complex.I := by
  rw [sourceCanonicalRoot_zero_source_eq_free_sine hp hp1 0,Complex.sin_pi_div_two,mul_one]

/-- At a collapsed isolated gap, analytic continuation retains a simple zero with a nonzero derivative. -/
theorem SourceLemma10_5Data.canonicalCollapsed_derivative
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (h : SourceLemma10_5Data hp hp1 W) (ψ : CoeffPair p) (hψ : ψ ∈ W) (n : ℤ)
    (hg : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n = 0) :
    let τ := canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n
    HasDerivAt (sourceCanonicalRoot hp hp1 ψ)
      (-2*Complex.I*sourceStandardRootOmittedProduct hp hp1 n ψ τ) τ ∧
    -2*Complex.I*sourceStandardRootOmittedProduct hp hp1 n ψ τ ≠ 0 := by
  dsimp only
  let τ := canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  have hτ : τ ∈ sourceStandardRootOmittedDomain hp hp1 ψ n := by
    simpa [sourceCanonicalRootGapPoint,sourceStandardRootMidpoint,τ] using
      h.canonicalGapPoint_mem ψ hψ n 0 (by constructor <;> norm_num)
  have hP := (h.spectral ψ hψ n τ hτ).differentiableAt.hasDerivAt
  have hlin : HasDerivAt (fun w : ℂ => τ-w) (-1) τ := by
    simpa using! (hasDerivAt_const τ τ).sub (hasDerivAt_id τ)
  have hd := (hlin.const_mul (2*Complex.I)).mul hP
  have he : sourceCanonicalRoot hp hp1 ψ =
      fun w => 2*Complex.I*(τ-w)*sourceStandardRootOmittedProduct hp hp1 n ψ w := by
    funext w
    rw [sourceCanonicalRoot_eq_omitted hp hp1 n,sourceStandardRoot_of_zeroGap hp hp1 ψ n w hg]
  constructor
  · rw [he]
    convert! hd using 1
    ring
  · exact mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) (h.nonzero ψ n τ hτ)

/-- The upper and lower real-gap arrows in Figure 2.4. -/
theorem sourceCanonicalRoot_figure_gap_signs (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hψ : IsRealType (CoeffPair.toMax p ψ)) (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re)
    (t : ℝ) (ht : t ∈ Ioo (-1:ℝ) 1) :
    (sourceCanonicalRootGapUpperValue hp hp1 ψ n t).im = 0 ∧
    0 < (-1:ℝ)^n.natAbs*(sourceCanonicalRootGapUpperValue hp hp1 ψ n t).re ∧
    (sourceCanonicalRootGapLowerValue hp hp1 ψ n t).im = 0 ∧
    (-1:ℝ)^n.natAbs*(sourceCanonicalRootGapLowerValue hp hp1 ψ n t).re < 0 := by
  have hu := sourceCanonicalRootGapUpperValue_im_eq_zero_and_ne_zero hp hp1 ψ hψ n hopen ht
  have hs := sourceCanonicalRootGapUpperValue_signed_re_pos hp hp1 ψ hψ n hopen ht
  have he : sourceCanonicalRootGapLowerValue hp hp1 ψ n t =
      -sourceCanonicalRootGapUpperValue hp hp1 ψ n t := by
    rw [sourceCanonicalRootGapUpperValue_eq_neg_lower]
    simp
  refine ⟨hu.1,hs,?_,?_⟩
  · rw [he,Complex.neg_im,hu.1,neg_zero]
  · rw [he,Complex.neg_re,mul_neg]
    exact neg_neg_of_pos hs

/-- The imaginary arrows immediately before and after the selected real gap. -/
theorem sourceCanonicalRoot_figure_band_signs (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hψ : IsRealType (CoeffPair.toMax p ψ)) (n : ℤ)
    (x y : ℝ) (hx : x ∈ sourceRealBand hp hp1 ψ (n-1)) (hy : y ∈ sourceRealBand hp hp1 ψ n) :
    (sourceCanonicalRoot hp hp1 ψ (x:ℂ)).re = 0 ∧
    0 < (-1:ℝ)^n.natAbs*(sourceCanonicalRoot hp hp1 ψ (x:ℂ)).im ∧
    (sourceCanonicalRoot hp hp1 ψ (y:ℂ)).re = 0 ∧
    (-1:ℝ)^n.natAbs*(sourceCanonicalRoot hp hp1 ψ (y:ℂ)).im < 0 := by
  have hs (k : ℤ) : (-1:ℝ)^k.natAbs = (-1:ℝ)^k := by
    rw [neg_one_pow_eq_ite,neg_one_zpow_eq_ite]
    simp only [Int.natAbs_even]
  have hparity : (-1:ℝ)^(n-1).natAbs = -((-1:ℝ)^n.natAbs) := by
    rw [hs (n-1),hs n,zpow_sub₀ (by norm_num)]
    norm_num [div_neg,div_one]
  have hL := sourceCanonicalRoot_realBand_sign hp hp1 ψ hψ (n-1) x hx
  have hR := sourceCanonicalRoot_realBand_sign hp hp1 ψ hψ n y hy
  refine ⟨hL.1,?_,hR⟩
  have hh := hL.2
  rw [hparity,neg_mul] at hh
  exact neg_neg_iff_pos.mp hh

/-- The continued canonical root vanishes at a collapsed gap, with the explicitly nonzero derivative. -/
theorem SourceLemma10_5Data.canonicalCollapsed_simple_zero
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (h : SourceLemma10_5Data hp hp1 W) (ψ : CoeffPair p) (hψ : ψ ∈ W) (n : ℤ)
    (hg : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n = 0) :
    let τ := canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n
    sourceCanonicalRoot hp hp1 ψ τ = 0 ∧
    HasDerivAt (sourceCanonicalRoot hp hp1 ψ)
      (-2*Complex.I*sourceStandardRootOmittedProduct hp hp1 n ψ τ) τ ∧
    -2*Complex.I*sourceStandardRootOmittedProduct hp hp1 n ψ τ ≠ 0 := by
  refine ⟨?_,h.canonicalCollapsed_derivative ψ hψ n hg⟩
  rw [sourceCanonicalRoot_eq_omitted hp hp1 n,sourceStandardRoot_of_zeroGap hp hp1 ψ n _ hg]
  simp

end NLS.ZakharovShabat
