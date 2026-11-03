import NLS.KdV.HillFreeTraceContour
import NLS.KdV.HillL2EnergySquareCircleAsymptotics
import NLS.ComplexAnalysis.EnergyContourCoefficient

/-! # Actual smooth energy contour and finite-moment limits -/

noncomputable section
open scoped ContDiff
open Set Metric Complex Filter Topology
namespace NLS.KdV
open NLS.ComplexAnalysis

theorem tendsto_hillL2FreeSquarePeriod_energy_smooth
    (Q : C(AddCircle (2 : ℝ), ℂ))
    (hq : SpectralWeight.one.toCoeff (hillContinuousCoefficients Q) ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)))
    (hreal : ∀ x : AddCircle (2 : ℝ), (Q x).im = 0)
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2 : ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) 1)
    (hmean : (∫ x in (0 : ℝ)..1, Q (x : AddCircle (2 : ℝ))) = 0) :
    Tendsto (fun N => hillL2FreeSquarePeriod (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) N 1)
      atTop (𝓝 (classicalHamiltonian (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) / 4)) := by
  let q := hillContinuousCoefficients Q
  let A := classicalQuadraticInvariant (fun x : ℝ => Q (x : AddCircle (2 : ℝ)))
  let B := classicalHamiltonian (fun x : ℝ => Q (x : AddCircle (2 : ℝ)))
  obtain ⟨C, hC, K, hbound⟩ := exists_hillL2Square_circle_energy_remainder Q hq hr hreal hf hp hmean
  have hinv : Tendsto (fun N => (hillFreeBandFrequency N)⁻¹) atTop (𝓝 0) :=
    tendsto_hillFreeBandFrequency.inv_tendsto_atTop
  have hlim : Tendsto (fun N => 2*C/(hillFreeBandFrequency N)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using hinv.const_mul (2*C)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [eventually_hillFreeCircle_conditions q hq hr, eventually_ge_atTop K,
    hlim.eventually (gt_mem_nhds hε)] with N hN hKN hsmall
  have hi : CircleIntegrable (fun w => w * hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) w ^ 2)
      0 ((hillFreeBandFrequency N)^2) := by
    simpa only [pow_one] using circleIntegrable_hillL2FreeSquareIntegrand q hq hr N hN.1 hN.2.1 hN.2.2 1
  have hh := norm_energy_circle_coefficient_sub_le
    (fun w => hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) w ^ 2) A B
    (hillFreeBandFrequency N) C (hillFreeBandFrequency_pos N) hi
    (fun w hw => hbound N hKN w hw)
  rw [dist_eq_norm]
  apply (show ‖hillL2FreeSquarePeriod (SpectralWeight.one.toCoeff q) N 1 - B/4‖ ≤
      2*C/(hillFreeBandFrequency N) from by
        simpa only [hillL2FreeSquarePeriod, pow_one] using hh).trans_lt hsmall

theorem tendsto_partial_hillL2Moments_energy_smooth
    (Q : C(AddCircle (2 : ℝ), ℂ))
    (hq : SpectralWeight.one.toCoeff (hillContinuousCoefficients Q) ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)))
    (hreal : ∀ x : AddCircle (2 : ℝ), (Q x).im = 0)
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2 : ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) 1)
    (hmean : (∫ x in (0 : ℝ)..1, Q (x : AddCircle (2 : ℝ))) = 0) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, (2*(n : ℂ)*Real.pi) *
      hillL2RealContourMoment (hillContinuousCoefficients Q) hq hr n 1) atTop
      (𝓝 (classicalHamiltonian (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) / 4)) := by
  apply (tendsto_hillL2FreeSquarePeriod_energy_smooth Q hq hr hreal hf hp hmean).congr'
  filter_upwards [eventually_hillL2FreeSquarePeriod_eq_partial_moments (hillContinuousCoefficients Q) hq hr] with N hN
  exact hN 1



end NLS.KdV
