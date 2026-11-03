import NLS.KdV.HillL2HierarchySquareAsymptotics
import NLS.KdV.HillFreeTraceContour

/-! # The actual smooth hierarchy contour limit and finite moment-sum limit at every order. -/

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ContDiff ComplexConjugate
namespace NLS.KdV
open NLS.ComplexAnalysis
theorem tendsto_hillL2FreeSquarePeriod_hierarchy_smooth
    (Q : C(AddCircle (2 : ℝ), ℂ))
    (hq : SpectralWeight.one.toCoeff (hillContinuousCoefficients Q) ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)))
    (hreal : ∀ x : AddCircle (2 : ℝ), (Q x).im = 0)
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2 : ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) 1)
    (hmean : (∫ x in (0 : ℝ)..1, Q (x : AddCircle (2 : ℝ))) = 0) (m : ℕ) :
    Tendsto (fun N => hillL2FreeSquarePeriod (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) N m)
      atTop (𝓝 (hillHierarchyTraceCoefficient
        (classicalKdVHierarchyHamiltonian (fun x : ℝ => Q (x : AddCircle (2 : ℝ)))) m)) := by
  let q := hillContinuousCoefficients Q
  let H := classicalKdVHierarchyHamiltonian (fun x : ℝ => Q (x : AddCircle (2 : ℝ)))
  obtain ⟨C,hC,K,hbound⟩ := exists_hillSquaredPhaseModel_circle_error Q hq hr hreal hf hp hmean (m+2)
  have hinv : Tendsto (fun N => (hillFreeBandFrequency N)⁻¹) atTop (𝓝 0) :=
    tendsto_hillFreeBandFrequency.inv_tendsto_atTop
  have hlim : Tendsto (fun N => 2*C/(hillFreeBandFrequency N)^2) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, inv_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero] using
      (hinv.pow 2).const_mul (2*C)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [eventually_hillFreeCircle_conditions q hq hr, eventually_ge_atTop K,
    hlim.eventually (gt_mem_nhds hε)] with N hN hKN hsmall
  have hi := circleIntegrable_hillL2FreeSquareIntegrand q hq hr N hN.1 hN.2.1 hN.2.2 m
  have hmodel := circleIntegrable_hillSourceSquaredPhaseModel H (m+2) m
    ((hillFreeBandFrequency N)^2) (sq_pos_of_pos (hillFreeBandFrequency_pos N))
  have hh := norm_weighted_circle_integral_sub_model_le
    (fun w => hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) w^2)
    (hillSourceSquaredPhaseModel H (m+2)) m (hillFreeBandFrequency N) C
    (hillFreeBandFrequency_pos N) hi hmodel
    (fun w hw => by simpa only [show 2*(m+2) = 2*m+4 by omega] using hbound N hKN w hw)
  rw [normalized_hillSourceSquaredPhaseModel_circle H (m+2) m (by omega)
    ((hillFreeBandFrequency N)^2) (sq_pos_of_pos (hillFreeBandFrequency_pos N))] at hh
  rw [dist_eq_norm]
  apply (show ‖hillL2FreeSquarePeriod (SpectralWeight.one.toCoeff q) N m-
      hillHierarchyTraceCoefficient H m‖ ≤ 2*C/(hillFreeBandFrequency N)^2 from by
        simpa only [hillL2FreeSquarePeriod] using hh).trans_lt hsmall


theorem tendsto_partial_hillL2Moments_hierarchy_smooth
    (Q : C(AddCircle (2 : ℝ), ℂ))
    (hq : SpectralWeight.one.toCoeff (hillContinuousCoefficients Q) ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)))
    (hreal : ∀ x : AddCircle (2 : ℝ), (Q x).im = 0)
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2 : ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) 1)
    (hmean : (∫ x in (0 : ℝ)..1, Q (x : AddCircle (2 : ℝ))) = 0) (m : ℕ) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, (2*(n : ℂ)*Real.pi) *
      hillL2RealContourMoment (hillContinuousCoefficients Q) hq hr n m) atTop
      (𝓝 (hillClassicalHierarchyTraceValue (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) m)) := by
  apply (tendsto_hillL2FreeSquarePeriod_hierarchy_smooth Q hq hr hreal hf hp hmean m).congr'
  filter_upwards [eventually_hillL2FreeSquarePeriod_eq_partial_moments (hillContinuousCoefficients Q) hq hr] with N hN
  exact hN m


end NLS.KdV
