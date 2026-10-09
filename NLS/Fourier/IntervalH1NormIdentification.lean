import NLS.Fourier.SobolevEnergy
import NLS.ComplexAnalysis.IntervalH1Variation

/-! # The integral H1 norm and the existing physical squared energy -/
noncomputable section
open Set MeasureTheory
namespace NLS.Fourier

/-- The scalar norm used in the G.2 estimates is precisely the square root
of the existing physical energy, with the same unnormalized measure. -/
theorem intervalH1Norm_eq_sqrt_energy (f : ℝ → ℂ) (t : ℝ) (ht : 0 ≤ t)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 t)))
    (hd : MemLp (deriv f) 2 (volume.restrict (Ioc 0 t))) :
    NLS.ComplexAnalysis.intervalH1Norm f t = Real.sqrt (intervalH1Energy f 0 t) := by
  have hfi : IntervalIntegrable (fun s => ‖f s‖^2) volume 0 t :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).mpr
      ((memLp_two_iff_integrable_sq hf.norm.aestronglyMeasurable).mp hf.norm)
  have hdi : IntervalIntegrable (fun s => ‖deriv f s‖^2) volume 0 t :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).mpr
      ((memLp_two_iff_integrable_sq hd.norm.aestronglyMeasurable).mp hd.norm)
  rw [NLS.ComplexAnalysis.intervalH1Norm,intervalH1Energy,intervalIntegral.integral_add hfi hdi]

end NLS.Fourier
