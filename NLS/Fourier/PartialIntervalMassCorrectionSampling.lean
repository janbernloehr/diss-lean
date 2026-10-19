import NLS.Fourier.IntervalL2BoundedMultiplier
import NLS.Fourier.PartialIntervalOscillatorySampling

/-! # L2 sampling of the primitive-difference correction

Partial-interval oscillatory sampling controls the mass correction uniformly over the physical period and bounded complex lattice shifts.
-/

noncomputable section
open Set Complex MeasureTheory
open scoped ENNReal
namespace NLS.Fourier

/-- The explicit primitive-difference correction to the oscillatory
response has an L2 realization with a uniform bound over the physical
period and all bounded complex lattice displacements. -/
theorem exists_partial_interval_massCorrection_lattice_coefficients
    (r P : ℝ → ℂ) (hr : MemLp r 2 (volume.restrict (Ioc 0 1))) (hP : Continuous P)
    (K : ℝ) (hK : 0 ≤ K) (hbound : ∀ x ∈ Icc (0:ℝ) 1, ‖P x‖ ≤ K)
    (δ : NLS.Coeff ⊤) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
    ∃ q : NLS.Coeff 2,
      (∀ n, q n = exp (I*((Real.pi:ℂ)*n+δ n)*t)*
        (P t*(∫ x in (0:ℝ)..t, r x*exp (-2*I*((Real.pi:ℂ)*n+δ n)*x))-
          (∫ x in (0:ℝ)..t, P x*r x*exp (-2*I*((Real.pi:ℂ)*n+δ n)*x)))) ∧
      ‖q‖ ≤ 2*K*Real.exp (3*‖δ‖)*‖unitIntervalMemLpCoefficients r hr‖ := by
  let hp := memLp_unitInterval_bounded_mul r P hr hP K hbound
  obtain ⟨a,ha,han⟩ := exists_partial_interval_oscillatory_lattice_coefficients r hr δ t ht
  obtain ⟨b,hb,hbn⟩ := exists_partial_interval_oscillatory_lattice_coefficients
    (fun x => P x*r x) hp δ t ht
  have hpbound := norm_unitIntervalMemLpCoefficients_bounded_mul_le r P hr hP K hK hbound
  refine ⟨(P t) • a-b,?_,?_⟩
  · intro n
    change (P t)*a n-b n = _
    rw [ha n,hb n]
    ring
  · calc
      ‖(P t) • a-b‖ ≤ ‖(P t) • a‖+‖b‖ := norm_sub_le _ _
      _ = ‖P t‖*‖a‖+‖b‖ := by rw [norm_smul]
      _ ≤ K*(Real.exp (3*‖δ‖)*‖unitIntervalMemLpCoefficients r hr‖)+
          Real.exp (3*‖δ‖)*(K*‖unitIntervalMemLpCoefficients r hr‖) :=
        add_le_add (mul_le_mul (hbound t ht) han (norm_nonneg _) hK)
          (hbn.trans (mul_le_mul_of_nonneg_left hpbound (Real.exp_pos _).le))
      _ = _ := by ring

end NLS.Fourier
