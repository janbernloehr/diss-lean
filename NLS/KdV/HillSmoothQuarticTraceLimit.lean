import NLS.KdV.HillFreeQuarticContour
import NLS.KdV.HillL2QuarticCircleAsymptotics
import NLS.ComplexAnalysis.QuarticContourCoefficient

/-! # The physical KdV energy as the actual quartic contour and gap-sum limit -/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ContDiff
namespace NLS.KdV
open NLS.ComplexAnalysis

theorem tendsto_hillL2FreeQuarticPeriod_Hamiltonian_smooth
    (Q : C(AddCircle (2 : ℝ), ℂ))
    (hq : SpectralWeight.one.toCoeff (hillContinuousCoefficients Q) ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)))
    (hreal : ∀ x : AddCircle (2 : ℝ), (Q x).im = 0)
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2 : ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) 1)
    (hmean : (∫ x in (0 : ℝ)..1, Q (x : AddCircle (2 : ℝ))) = 0) :
    Tendsto (fun N => hillL2FreeQuarticPeriod (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) N)
      atTop (𝓝 (classicalHamiltonian (fun x : ℝ => Q (x : AddCircle (2 : ℝ))))) := by
  let q := hillContinuousCoefficients Q
  let A := classicalHamiltonian (fun x : ℝ => Q (x : AddCircle (2 : ℝ)))
  obtain ⟨C, hC, K, hbound⟩ := exists_hillL2Quartic_circle_energy_remainder Q hq hr hreal hf hp hmean
  have hinv : Tendsto (fun N => (hillFreeBandFrequency N)⁻¹) atTop (𝓝 0) :=
    tendsto_hillFreeBandFrequency.inv_tendsto_atTop
  have hlim : Tendsto (fun N => 4*C/hillFreeBandFrequency N) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, inv_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero] using hinv.const_mul (4*C)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [eventually_hillFreeCircle_conditions q hq hr, eventually_ge_atTop K,
    hlim.eventually (gt_mem_nhds hε)] with N hN hKN hsmall
  have hR : 0 < (hillFreeBandFrequency N)^2 := sq_pos_of_pos (hillFreeBandFrequency_pos N)
  have hi : CircleIntegrable (fun w => hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) w ^ 4)
      0 ((hillFreeBandFrequency N)^2) := by
    exact circleIntegrable_hillL2FreeQuarticIntegrand q hq hr N hN.1 hN.2.1 hN.2.2
  have hh := norm_quartic_circle_coefficient_sub_le
    (fun w => hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) w ^ 4)
    (classicalQuadraticInvariant (fun x : ℝ => Q (x : AddCircle (2 : ℝ)))) A
    (hillFreeBandFrequency N) C (hillFreeBandFrequency_pos N) hi (hbound N hKN)
  rw [dist_eq_norm]
  apply (show ‖hillL2FreeQuarticPeriod (SpectralWeight.one.toCoeff q) N - A‖ ≤
      4*C/hillFreeBandFrequency N from by
        simpa only [hillL2FreeQuarticPeriod, pow_zero, one_mul] using hh).trans_lt hsmall

theorem tendsto_partial_hillL2Actions_and_cubic_Hamiltonian_smooth
    (Q : C(AddCircle (2 : ℝ), ℂ))
    (hq : SpectralWeight.one.toCoeff (hillContinuousCoefficients Q) ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)))
    (hreal : ∀ x : AddCircle (2 : ℝ), (Q x).im = 0)
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2 : ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) 1)
    (hmean : (∫ x in (0 : ℝ)..1, Q (x : AddCircle (2 : ℝ))) = 0) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N,
      (((8*(n : ℝ)^3*Real.pi^3 : ℝ) : ℂ)*hillL2RealContourMoment (hillContinuousCoefficients Q) hq hr n 0+
        ((8*(n : ℝ)*Real.pi : ℝ) : ℂ)*hillL2RealCubicContourMoment (hillContinuousCoefficients Q) hq hr n)) atTop
      (𝓝 (classicalHamiltonian (fun x : ℝ => Q (x : AddCircle (2 : ℝ))))) := by
  apply (tendsto_hillL2FreeQuarticPeriod_Hamiltonian_smooth Q hq hr hreal hf hp hmean).congr'
  filter_upwards [eventually_hillFreeCircle_conditions (hillContinuousCoefficients Q) hq hr] with N hN
  exact hillL2FreeQuarticPeriod_eq_partial_moments (hillContinuousCoefficients Q) hq hr N hN.1 hN.2.1 hN.2.2

end NLS.KdV
