import NLS.KdV.HillFreeTraceContour
import NLS.KdV.HillL2SquareCircleAsymptotics
import NLS.ComplexAnalysis.QuadraticContourCoefficient

/-! # The actual smooth physical quadratic trace as a contour and gap-sum limit

The full-circle remainder evaluates the literal squared-primitive period.
The checked finite-hole decomposition then identifies its partial action
sums with the independently defined physical invariant H_0.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ContDiff
namespace NLS.KdV
open NLS.ComplexAnalysis

theorem tendsto_hillL2FreeSquarePeriod_quadraticInvariant_smooth
    (Q : C(AddCircle (2 : ℝ), ℂ))
    (hq : SpectralWeight.one.toCoeff (hillContinuousCoefficients Q) ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)))
    (hreal : ∀ x : AddCircle (2 : ℝ), (Q x).im = 0)
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2 : ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) 1)
    (hmean : (∫ x in (0 : ℝ)..1, Q (x : AddCircle (2 : ℝ))) = 0) :
    Tendsto (fun N => hillL2FreeSquarePeriod (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) N 0)
      atTop (𝓝 (classicalQuadraticInvariant (fun x : ℝ => Q (x : AddCircle (2 : ℝ))))) := by
  let q := hillContinuousCoefficients Q
  let A := classicalQuadraticInvariant (fun x : ℝ => Q (x : AddCircle (2 : ℝ)))
  obtain ⟨C, hC, K, hbound⟩ := exists_hillL2Square_circle_quadratic_remainder Q hq hr hreal hf hp hmean
  have hinv : Tendsto (fun N => (hillFreeBandFrequency N)⁻¹) atTop (𝓝 0) :=
    tendsto_hillFreeBandFrequency.inv_tendsto_atTop
  have hlim : Tendsto (fun N => 2*C/(hillFreeBandFrequency N)^2) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, inv_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero] using (hinv.pow 2).const_mul (2*C)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [eventually_hillFreeCircle_conditions q hq hr, eventually_ge_atTop K,
    hlim.eventually (gt_mem_nhds hε)] with N hN hKN hsmall
  have hR : 0 < (hillFreeBandFrequency N)^2 := sq_pos_of_pos (hillFreeBandFrequency_pos N)
  have hi : CircleIntegrable (fun w => hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) w ^ 2)
      0 ((hillFreeBandFrequency N)^2) := by
    simpa only [pow_zero, one_mul] using circleIntegrable_hillL2FreeSquareIntegrand q hq hr N hN.1 hN.2.1 hN.2.2 0
  have hh := norm_quadratic_circle_coefficient_sub_le
    (fun w => hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) w ^ 2) A
    ((hillFreeBandFrequency N)^2) C hR hi (by
      intro w hw
      rw [show ((hillFreeBandFrequency N)^2)^2 = (hillFreeBandFrequency N)^4 by ring]
      exact hbound N hKN w hw)
  rw [dist_eq_norm]
  apply (show ‖hillL2FreeSquarePeriod (SpectralWeight.one.toCoeff q) N 0 - A‖ ≤
      2*C/(hillFreeBandFrequency N)^2 from by
        simpa only [hillL2FreeSquarePeriod, pow_zero, one_mul] using hh).trans_lt hsmall

theorem tendsto_partial_hillL2Actions_quadraticInvariant_smooth
    (Q : C(AddCircle (2 : ℝ), ℂ))
    (hq : SpectralWeight.one.toCoeff (hillContinuousCoefficients Q) ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)))
    (hreal : ∀ x : AddCircle (2 : ℝ), (Q x).im = 0)
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2 : ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) 1)
    (hmean : (∫ x in (0 : ℝ)..1, Q (x : AddCircle (2 : ℝ))) = 0) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, (2*(n : ℂ)*Real.pi) *
      hillL2RealContourMoment (hillContinuousCoefficients Q) hq hr n 0) atTop
      (𝓝 (classicalQuadraticInvariant (fun x : ℝ => Q (x : AddCircle (2 : ℝ))))) := by
  apply (tendsto_hillL2FreeSquarePeriod_quadraticInvariant_smooth Q hq hr hreal hf hp hmean).congr'
  filter_upwards [eventually_hillL2FreeSquarePeriod_eq_partial_moments (hillContinuousCoefficients Q) hq hr] with N hN
  exact hN 0

end NLS.KdV
