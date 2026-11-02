import NLS.KdV.HillOuterTraceDomain
import NLS.KdV.HillL2SquareGapPeriods

/-! # Exact finite outer-contour identities for the actual Hill primitive

All circle geometry and holomorphic domain hypotheses are proved for
the actual intrinsic gap circles. Finite-hole Cauchy decomposition then
identifies the normalized outer F-squared moment with the first N
weighted hierarchy actions. No physical Hamiltonian coefficient is assumed.
-/

noncomputable section
open Set Metric Complex
namespace NLS.KdV
open NLS.ComplexAnalysis

theorem circleIntegral_hillL2Square_eq_finite_gap_sum
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (N m : ℕ) :
    (∮ z in C((hillRealOuterCenter q hq hr : ℂ), hillRealOuterRadius q hq hr N),
      z ^ m * hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) z ^ 2) =
      ∑ n ∈ Finset.Icc 1 N,
        ∮ z in C((hillRealGapCenter q hq hr n : ℂ),
            hillRealGapHalfLength q hq hr n + hillRealGapCollar q hq hr n),
          z ^ m * hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) z ^ 2 := by
  apply circleIntegral_eq_sum_of_finite_holes _ _ (hillRealOuterRadius_pos q hq hr N).le
    (Finset.Icc 1 N) (fun n => (hillRealGapCenter q hq hr n : ℂ))
    (fun n => hillRealGapHalfLength q hq hr n + hillRealGapCollar q hq hr n)
    (hillRealGapOuterRadius q hq hr)
  · intro n hn
    exact (hillRealGapOuterRadius_bounds q hq hr n (Finset.mem_Icc.mp hn).1).1
  · intro n hn
    exact (hillRealGapOuterRadius_bounds q hq hr n (Finset.mem_Icc.mp hn).1).2.1
  · intro n hn
    exact hillRealGapOuter_enclosed q hq hr N n (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hn).2
  · intro i hi j hj hij
    exact hillRealGapOuter_disjoint q hq hr i j (Finset.mem_Icc.mp hi).1 (Finset.mem_Icc.mp hj).1 hij
  · exact analyticOnNhd_hillRealOuter_perforated_square q hq hr N m

theorem hillL2OuterSquarePeriod_eq_partial_moments
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (N m : ℕ) :
    ((Real.pi : ℂ) * I)⁻¹ *
      (∮ z in C((hillRealOuterCenter q hq hr : ℂ), hillRealOuterRadius q hq hr N),
        z ^ m * hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) z ^ 2) =
      ∑ n ∈ Finset.Icc 1 N, (2 * (n : ℂ) * Real.pi) * hillL2RealContourMoment q hq hr n m := by
  rw [circleIntegral_hillL2Square_eq_finite_gap_sum q hq hr N m, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  exact hillL2SquareGapPeriod_eq_weightedMoment q hq hr n (Finset.mem_Icc.mp hn).1 m

end NLS.KdV
