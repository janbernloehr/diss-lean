import NLS.KdV.HillL2SourcePrimitive
import NLS.ComplexAnalysis.TracePrimitiveMoments

/-! # Analytic high contour moments of the actual L2 Hill primitive

These fixed-circle functionals use the source-normalized physical trace.
They are analytic near every checked high-index potential, vanish at the
free potential, and at every integer level satisfy the actual Arnold contour formula.
Identification with globally defined canonical actions, positivity and
quantitative action bounds remain separate obligations.
-/

noncomputable section
open Set Metric Complex
open NLS.ComplexAnalysis
namespace NLS.KdV

/-- The source-normalized moment on the explicit high energy circle.
Its physical interpretation is asserted only where the contour lies in
the checked continuation domain. -/
def hillL2HighContourMoment (n m : ℕ) (q : Coeff 2) : ℂ :=
  hillL2SourceFamily.contourMoment (freeHillValue n : ℂ) (n : ℝ) m q

theorem analyticAt_hillL2HighContourMoment
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (n : ℕ) (hn : 1 ≤ n) (hcut : 8*‖q‖ ≤ (n : ℝ)) (m : ℕ) :
    AnalyticAt ℂ (hillL2HighContourMoment n m) (SpectralWeight.one.toCoeff q) := by
  obtain ⟨V,_,hqV,ha⟩ := hillL2SourceFamily.exists_analytic_contourMoment
    (freeHillValue n : ℂ) (n : ℝ) (by positivity) (SpectralWeight.one.toCoeff q)
    (mem_hillL2ContinuationDomain_high_sphere q hq n hn hcut) m
  exact ha _ hqV

@[simp] theorem hillL2HighContourMoment_zero (n m : ℕ) (hn : 1 ≤ n) :
    hillL2HighContourMoment n m 0 = 0 :=
  hillL2SourceFamily.contourMoment_base (freeHillValue n : ℂ) (n : ℝ) (by positivity)
    (hillClosedBall_subset_slitPlane n hn) m

/-- Every integer hierarchy level has the source factor `1/((m+1)*pi)`. -/
theorem hillL2HighContourMoment_arnold_level
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (n : ℕ) (hn : 1 ≤ n) (hcut : 8*‖q‖ ≤ (n : ℝ)) (m : ℕ) :
    hillL2HighContourMoment n m (SpectralWeight.one.toCoeff q) =
      ((m+1 : ℂ)*(Real.pi : ℂ))⁻¹ * ∮ z in C((freeHillValue n : ℂ),(n : ℝ)),
        z^(m+1)*deriv (hillL2Discriminant (SpectralWeight.one.toCoeff q)) z /
          hillL2ContinuedRoot (z,SpectralWeight.one.toCoeff q) :=
  hillL2SourceFamily.contourMoment_arnold (freeHillValue n : ℂ) (n : ℝ) (by positivity)
    (SpectralWeight.one.toCoeff q) (mem_hillL2ContinuationDomain_high_sphere q hq n hn hcut) m

/-- The primitive moment has exactly the source's level-zero Arnold
integrand and normalization on the whole checked high circle. -/
theorem hillL2HighContourMoment_arnold
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (n : ℕ) (hn : 1 ≤ n) (hcut : 8*‖q‖ ≤ (n : ℝ)) :
    hillL2HighContourMoment n 0 (SpectralWeight.one.toCoeff q) =
      (Real.pi : ℂ)⁻¹ * ∮ z in C((freeHillValue n : ℂ),(n : ℝ)),
        z*deriv (hillL2Discriminant (SpectralWeight.one.toCoeff q)) z /
          hillL2ContinuedRoot (z,SpectralWeight.one.toCoeff q) := by
  simpa using hillL2HighContourMoment_arnold_level q hq n hn hcut 0

end NLS.KdV
