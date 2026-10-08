import NLS.Fourier.FourierNLSSpatialDerivatives
import NLS.Fourier.LocalSmoothFourierNLS

/-! # Strong original-variable derivatives at higher Sobolev orders -/
noncomputable section
open Set Complex
namespace NLS.Fourier

/-- The original Schrödinger generator loses two weighted orders. -/
def nlsSobolevLinearCLM (s : ℝ) (hs : 0 ≤ s) :
    WeightedCoeff (SpectralWeight.sobolev (s+2) (by linarith)).toWeight 1 →L[ℂ]
      WeightedCoeff (SpectralWeight.sobolev s hs).toWeight 1 :=
  I • WeightedCoeff.weightedMultiplierCLM _ _ (fun n => (nlsSpatialSymbol n)^2)
    ((2*Real.pi)^2) (by positivity) (by
      intro n
      simp only [SpectralWeight.sobolev_apply]
      rw [Weight.sobolev_add]
      simp only [norm_pow,norm_nlsSpatialSymbol,Weight.sobolev_apply,Real.rpow_two,mul_pow]
      have hn : |(n : ℝ)|^2 ≤ (1+|(n : ℝ)|)^2 := by nlinarith [abs_nonneg (n : ℝ)]
      calc
        _ = ((2*Real.pi)^2*(1+|(n : ℝ)|)^s)*|(n : ℝ)|^2 := by ring
        _ ≤ ((2*Real.pi)^2*(1+|(n : ℝ)|)^s)*(1+|(n : ℝ)|)^2 :=
          mul_le_mul_of_nonneg_left hn (by positivity)
        _ = _ := by ring)

@[simp] theorem nlsSobolevLinearCLM_apply (s : ℝ) (hs : 0 ≤ s)
    (a : WeightedCoeff (SpectralWeight.sobolev (s+2) (by linarith)).toWeight 1) (n : ℤ) :
    (nlsSobolevLinearCLM s hs a).val n = nlsLinearSymbol n*a.val n := by
  change I*((nlsSpatialSymbol n)^2*a.val n) = _
  simp only [nlsSpatialSymbol,nlsLinearSymbol]
  push_cast
  simp only [mul_pow,I_sq]
  ring

/-- A continuous lift two orders higher supplies the strong weighted derivative
of the original NLS trajectory, including derivatives within endpoints. -/
theorem IsFourierNLSTrajectoryOn.hasDerivWithinAt_sobolev
    (s : ℝ) (hs : 0 ≤ s) {a b : ℝ}
    {z : ℝ → WeightedCoeff (SpectralWeight.sobolev s hs).toWeight 1}
    (hz : IsFourierNLSTrajectoryOn (SpectralWeight.sobolev s hs) a b z)
    (v : ℝ → WeightedCoeff (SpectralWeight.sobolev (s+2) (by linarith)).toWeight 1)
    (hv : ContinuousOn v (Icc a b))
    (he : ∀ time ∈ Icc a b, ∀ n : ℤ, (v time).val n = (z time).val n)
    (time : ℝ) (ht : time ∈ Icc a b) :
    HasDerivWithinAt z
      (nlsSobolevLinearCLM s hs (v time) + cubicNLS (SpectralWeight.sobolev s hs) (z time)) (Icc a b) time := by
  apply (SpectralWeight.sobolev s hs).hasDerivWithinAt_of_coordinate_derivatives a b z _ hz.continuous
    (((nlsSobolevLinearCLM s hs).continuous.comp_continuousOn hv).add
      ((continuous_cubicNLS _).comp_continuousOn hz.continuous)) _ time ht
  intro r hr n
  have hd := (hz.equation r ⟨hr.1.le,hr.2.le⟩ n).hasDerivAt (Icc_mem_nhds hr.1 hr.2)
  simpa only [Pi.add_apply,Function.comp_apply,WeightedCoeff.add_val,nlsSobolevLinearCLM_apply,he r ⟨hr.1.le,hr.2.le⟩ n] using hd

/-- Initial membership two orders higher implies strong time differentiability
in the original weighted norm throughout the reference interval's interior. -/
theorem IsFourierNLSTrajectoryOn.differentiableAt_sobolev
    (s : ℝ) (hs : 0 ≤ s) {a b : ℝ}
    {z : ℝ → WeightedCoeff (SpectralWeight.sobolev s hs).toWeight 1}
    (hz : IsFourierNLSTrajectoryOn (SpectralWeight.sobolev s hs) a b z)
    (initial : ℝ) (hi : initial ∈ Icc a b)
    (hm : Memℓp (fun n => (Weight.sobolev (s+2) n : ℂ)*(z initial).val n) 1)
    (time : ℝ) (ht : time ∈ Ioo a b) : DifferentiableAt ℝ z time := by
  obtain ⟨v,hv,he⟩ := hz.exists_sobolev_lift initial hi (s+2) (by linarith) hm
  exact ((hz.hasDerivWithinAt_sobolev s hs v hv.continuous he time ⟨ht.1.le,ht.2.le⟩).hasDerivAt
    (Icc_mem_nhds ht.1 ht.2)).differentiableAt

end NLS.Fourier
