import NLS.KdV.HillHminusFiniteGapDiscriminantPhase
import NLS.KdV.HillHminusOriginalSheets
import NLS.KdV.ClassicalHillPhaseCoefficients
import NLS.ComplexAnalysis.CosineFourierIntegral

/-! # Physical Hamiltonian coefficients of the constructed finite-gap phase -/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.ZakharovShabat
open scoped ContDiff
namespace NLS.KdV

/-- The actual smooth periodic finite-gap Hill trace has an analytic phase
whose first five coefficients are the original physical integrals.
Neither the phase nor any asymptotic coefficient is a hypothesis. -/
theorem exists_hill_finiteGap_physical_phase
    (Q : C(AddCircle (2 : ℝ), ℂ))
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)))
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2 : ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) 1)
    (hmean : (∫ x in (0 : ℝ)..1, Q (x : AddCircle (2 : ℝ))) = 0)
    (N : ℕ) (hN : 1 ≤ N)
    (hclosed : ∀ n : ℕ, N ≤ n →
      hillHminusRealLabels (hillOriginalHminusSource (hillContinuousCoefficients Q))
          (hillOriginalHminusSource_real _ hr) (2*n) =
        hillHminusRealLabels (hillOriginalHminusSource (hillContinuousCoefficients Q))
          (hillOriginalHminusSource_real _ hr) (2*n-1)) :
    ∃ T : ℝ, 0 < T ∧ ∃ B : ℂ → ℂ, AnalyticAt ℂ B 0 ∧ B 0 = 0 ∧
      (∀ z : ℂ, T < ‖z‖ → 2*cosh (-I*z+B z⁻¹) =
        classicalHillDiscriminant (hillUnitPotentialCurve Q) (z^2)) ∧
      iteratedDeriv 1 B 0 = 0 ∧ iteratedDeriv 2 B 0 = 0 ∧
      iteratedDeriv 3 B 0 = 3*I*classicalQuadraticInvariant (fun x => Q (x : AddCircle (2 : ℝ)))/2 ∧
      iteratedDeriv 4 B 0 = 0 ∧
      iteratedDeriv 5 B 0 = 15*I*classicalHamiltonian (fun x => Q (x : AddCircle (2 : ℝ)))/2 := by
  let q := hillContinuousCoefficients Q
  let p := hillOriginalHminusSource q
  have hreal : IsRealPeriodOneHminusOne p := hillOriginalHminusSource_real q hr
  have hm : p.val 0 = 0 := by
    change (hillOriginalHminusSource (hillContinuousCoefficients Q)).val 0 = 0
    rw [hillOriginalHminusSource_apply,mul_zero,hillContinuousCoefficients_apply,
      ←Fourier.periodTwoCoefficient_circle]
    have he := Fourier.periodTwoCoefficient_periodic_even
      (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) hp
      ((Q.continuous.comp (by fun_prop)).intervalIntegrable 0 1) 0
    rw [mul_zero] at he
    rw [he,←NLS.ComplexAnalysis.integral_eq_periodOneCoefficient_zero,hmean]
  obtain ⟨T,hT,B,hB,hB0,hrep⟩ :=
    exists_hillHminus_finiteGap_discriminant_phase p hreal hm N hN hclosed
  have hphys (z : ℂ) (hz : T < ‖z‖) :
      2*cosh (-I*z+B z⁻¹) = classicalHillDiscriminant (hillUnitPotentialCurve Q) (z^2) := by
    rw [hrep z hz]
    change hillHminusDiscriminant (hillOriginalHminusSource q) (z^2) = _
    rw [hillHminusDiscriminant_original_source_agreement q (hillContinuousCoefficients_mem_even Q hp),
      hillL2Discriminant_eq_classical]
  refine ⟨T,hT,B,hB,hB0,hphys,?_⟩
  apply classicalHill_phase_first_five (fun x => Q (x : AddCircle (2 : ℝ))) hf hp hmean B hB hB0 T
  exact hphys

end NLS.KdV
