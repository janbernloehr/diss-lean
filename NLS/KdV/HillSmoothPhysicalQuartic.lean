import NLS.KdV.HillSmoothQuarticEnergyCoefficient

/-! # The physical quartic Hill coefficient with only physical hypotheses

Reality of the actual function gives conjugate-reflected Fourier reality;
period-one periodicity gives even coefficient support. The actual smooth
quartic contour estimates and Hamiltonian recovery therefore apply to every
real smooth period-one mean-zero physical potential without independent
spectral parity or reality assumptions.
-/
noncomputable section
open Set Metric Complex Filter Topology
open scoped ContDiff ComplexConjugate
namespace NLS.KdV

/-- Physical reality gives the actual conjugate-reflected Hill coefficient condition. -/
theorem isRealHillPotential_hillContinuousCoefficients (Q : C(AddCircle (2 : ℝ), ℂ))
    (hreal : ∀ x : AddCircle (2 : ℝ), (Q x).im = 0) :
    IsRealHillPotential (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) := by
  rw [toCoeff_hillContinuousCoefficients]
  have hs : star Q = Q := by
    ext x
    change conj (Q x) = Q x
    apply Complex.ext <;> simp [hreal x]
  have he := Fourier.continuousFourierCLM_star Q
  rw [hs] at he
  intro k
  have hk := congrArg (fun a : Coeff 2 => a (-k)) he
  simpa only [lp.star_apply,Coeff.reflection_apply,neg_neg,starRingEnd_apply] using hk

theorem tendsto_hillL2QuarticPeriod_physicalHamiltonian
    (Q : C(AddCircle (2 : ℝ), ℂ))
    (hreal : ∀ x : AddCircle (2 : ℝ), (Q x).im = 0)
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2 : ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) 1)
    (hmean : (∫ x in (0 : ℝ)..1, Q (x : AddCircle (2 : ℝ))) = 0) :
    Tendsto (fun N => (-4 : ℂ)*hillL2QuarticPeriod (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) N) atTop
      (𝓝 (classicalHamiltonian (fun x : ℝ => Q (x : AddCircle (2 : ℝ))))) := by
  exact tendsto_hillL2QuarticPeriod_physicalHamiltonian_smooth Q
    (hillContinuousCoefficients_mem_even Q hp) (isRealHillPotential_hillContinuousCoefficients Q hreal) hreal hf hp hmean

theorem exists_hillL2Quartic_circle_physical_energy_remainder
    (Q : C(AddCircle (2 : ℝ), ℂ))
    (hreal : ∀ x : AddCircle (2 : ℝ), (Q x).im = 0)
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2 : ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) 1)
    (hmean : (∫ x in (0 : ℝ)..1, Q (x : AddCircle (2 : ℝ))) = 0) :
    ∃ C : ℝ, 0 < C ∧ ∃ K : ℕ, ∀ N : ℕ, K ≤ N →
      ∀ z ∈ sphere (0 : ℂ) ((hillFreeBandFrequency N)^2),
        (hillFreeBandFrequency N)^3 *
          ‖hillL2RealCutPrimitive (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) z ^ 4 - z^2 +
            classicalQuadraticInvariant (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) +
            classicalHamiltonian (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) / (4*z)‖ ≤ C := by
  exact exists_hillL2Quartic_circle_energy_remainder Q
    (hillContinuousCoefficients_mem_even Q hp) (isRealHillPotential_hillContinuousCoefficients Q hreal) hreal hf hp hmean

theorem exists_hillL2QuarticPeriod_physical_energy_error
    (Q : C(AddCircle (2 : ℝ), ℂ))
    (hreal : ∀ x : AddCircle (2 : ℝ), (Q x).im = 0)
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2 : ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) 1)
    (hmean : (∫ x in (0 : ℝ)..1, Q (x : AddCircle (2 : ℝ))) = 0) :
    ∃ C : ℝ, 0 < C ∧ ∃ K : ℕ, ∀ N : ℕ, K ≤ N →
      ‖hillL2QuarticPeriod (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) N +
        classicalHamiltonian (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) / 4‖ ≤ C / hillFreeBandFrequency N := by
  exact exists_hillL2QuarticPeriod_energy_error Q
    (hillContinuousCoefficients_mem_even Q hp) (isRealHillPotential_hillContinuousCoefficients Q hreal) hreal hf hp hmean

theorem tendsto_hillL2QuarticPeriod_physical_energy
    (Q : C(AddCircle (2 : ℝ), ℂ))
    (hreal : ∀ x : AddCircle (2 : ℝ), (Q x).im = 0)
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2 : ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) 1)
    (hmean : (∫ x in (0 : ℝ)..1, Q (x : AddCircle (2 : ℝ))) = 0) :
    Tendsto (hillL2QuarticPeriod (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q))) atTop
      (𝓝 (-classicalHamiltonian (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) / 4)) := by
  exact tendsto_hillL2QuarticPeriod_energy_smooth Q
    (hillContinuousCoefficients_mem_even Q hp) (isRealHillPotential_hillContinuousCoefficients Q hreal) hreal hf hp hmean

end NLS.KdV
