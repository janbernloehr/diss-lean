import NLS.KdV.HillFiniteGapExterior
import NLS.KdV.HillSmoothPhysicalQuartic

/-! # Exact physical quartic Hill contours at finite-gap potentials

Actual finite-gap exterior analyticity makes the large centered-circle
periods independent of radius. The proved physical smooth contour limit
therefore identifies every such contour exactly with -H1/4. The Hamiltonian
is the actual period-one integral; no energy coefficient or frequency is
postulated. Angle Poisson brackets and frequency identification remain open.
-/
noncomputable section
open Set Metric Complex Filter Topology
open scoped ContDiff
namespace NLS.KdV

/-- The exact quartic coefficient on every sufficiently large centered circle for a physical smooth real finite-gap potential. -/
theorem exists_hillL2FiniteGap_physical_quartic_identity
    (Q : C(AddCircle (2 : ℝ), ℂ))
    (hreal : ∀ x : AddCircle (2 : ℝ), (Q x).im = 0)
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2 : ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) 1)
    (hmean : (∫ x in (0 : ℝ)..1, Q (x : AddCircle (2 : ℝ))) = 0)
    (hfg : HillFiniteGap (hillContinuousCoefficients Q) (hillContinuousCoefficients_mem_even Q hp)
      (isRealHillPotential_hillContinuousCoefficients Q hreal)) :
    ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, R < r →
      (2*Real.pi*I : ℂ)⁻¹ * (∮ z in C((0 : ℂ),r),
        hillL2RealCutPrimitive (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) z ^ 4) =
          -classicalHamiltonian (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) / 4 := by
  obtain ⟨R,hR,_,hi⟩ := HillFiniteGap.exists_analytic_even_exterior_and_periods (hillContinuousCoefficients Q)
    (hillContinuousCoefficients_mem_even Q hp) (isRealHillPotential_hillContinuousCoefficients Q hreal) hfg
  refine ⟨R,hR,?_⟩
  intro r hr
  have hlarge : ∀ᶠ N : ℕ in atTop, R < (hillFreeBandFrequency N)^2 := by
    filter_upwards [tendsto_hillFreeBandFrequency.eventually_gt_atTop (max R 1)] with N hN
    have hNR : R < hillFreeBandFrequency N := (le_max_left _ _).trans_lt hN
    have hN1 : 1 < hillFreeBandFrequency N := (le_max_right _ _).trans_lt hN
    nlinarith
  have heq : hillL2QuarticPeriod (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) =ᶠ[atTop]
      (fun _ : ℕ => (2*Real.pi*I : ℂ)⁻¹ * (∮ z in C((0 : ℂ),r),
        hillL2RealCutPrimitive (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) z ^ 4)) := by
    filter_upwards [hlarge] with N hN
    unfold hillL2QuarticPeriod
    congr 1
    simpa only [show 2*2 = (4 : ℕ) by norm_num] using hi 2 ((hillFreeBandFrequency N)^2) hN r hr
  have hc := (tendsto_hillL2QuarticPeriod_physical_energy Q hreal hf hp hmean).congr' heq
  exact tendsto_nhds_unique tendsto_const_nhds hc

/-- The actual finite-gap quartic contour recovers the physical KdV Hamiltonian with the source factor -4. -/
theorem exists_hillL2FiniteGap_physical_hamiltonian_identity
    (Q : C(AddCircle (2 : ℝ), ℂ))
    (hreal : ∀ x : AddCircle (2 : ℝ), (Q x).im = 0)
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2 : ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) 1)
    (hmean : (∫ x in (0 : ℝ)..1, Q (x : AddCircle (2 : ℝ))) = 0)
    (hfg : HillFiniteGap (hillContinuousCoefficients Q) (hillContinuousCoefficients_mem_even Q hp)
      (isRealHillPotential_hillContinuousCoefficients Q hreal)) :
    ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, R < r →
      classicalHamiltonian (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) =
        (-4 : ℂ)*(2*Real.pi*I : ℂ)⁻¹ * (∮ z in C((0 : ℂ),r),
          hillL2RealCutPrimitive (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) z ^ 4) := by
  obtain ⟨R,hR,hid⟩ := exists_hillL2FiniteGap_physical_quartic_identity Q hreal hf hp hmean hfg
  refine ⟨R,hR,?_⟩
  intro r hr
  have he := hid r hr
  linear_combination 4*he

end NLS.KdV
