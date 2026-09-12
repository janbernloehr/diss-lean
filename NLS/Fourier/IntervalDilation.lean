import NLS.Fourier.IntrinsicIntervalEnergy

/-!
# Dilation of physical interval data

A positive dilation transports the interval and scales its Lebesgue measure.
Nonnegative integral identities hold for arbitrary representatives; square
integrability is transported with the actual restricted measure.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace NLS.Fourier

/-- Pull interval data back by a real dilation. -/
def intervalDilation (c : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ := f (c * x)

@[simp] theorem intervalDilation_one (f : ℝ → ℂ) : intervalDilation 1 f = f := by
  funext x
  simp [intervalDilation]

/-- Positive dilation transports restricted Lebesgue measure with its exact inverse Jacobian. -/
theorem measurePreserving_interval_dilation {c : ℝ} (hc : 0 < c) (L : ℝ) :
    MeasurePreserving (fun x : ℝ => c * x) (volume.restrict (Ioo 0 L))
      (ENNReal.ofReal c⁻¹ • volume.restrict (Ioo 0 (c * L))) := by
  have hm : MeasurePreserving (fun x : ℝ => c * x) volume (ENNReal.ofReal c⁻¹ • volume) := by
    refine ⟨by fun_prop, ?_⟩
    simpa only [abs_of_pos (inv_pos.mpr hc)] using Real.map_volume_mul_left hc.ne'
  have he : (fun x : ℝ => c * x) ⁻¹' Ioo 0 (c * L) = Ioo 0 L := by
    ext x
    simp only [mem_preimage, mem_Ioo, mul_pos_iff_of_pos_left hc, mul_lt_mul_iff_right₀ hc]
  simpa only [he, Measure.restrict_smul] using hm.restrict_preimage (s := Ioo 0 (c * L)) measurableSet_Ioo

/-- Dilation of a nonnegative interval integral without a measurability requirement on its integrand. -/
theorem lintegral_interval_dilation {c : ℝ} (hc : 0 < c) (L : ℝ) (F : ℝ → ℝ≥0∞) :
    (∫⁻ x : ℝ in Ioo 0 L, F (c * x)) = ENNReal.ofReal c⁻¹ * ∫⁻ x : ℝ in Ioo 0 (c * L), F x := by
  have he : MeasurableEmbedding (fun x : ℝ => c * x) :=
    (Homeomorph.mulLeft₀ c hc.ne').isClosedEmbedding.measurableEmbedding
  simpa only [lintegral_smul_measure, smul_eq_mul] using
    (measurePreserving_interval_dilation hc L).lintegral_comp_emb he F

/-- Interval `MemLp` pulls back under every positive dilation. -/
theorem memLp_intervalDilation {c : ℝ} (hc : 0 < c) (L : ℝ) (f : ℝ → ℂ) {p : ℝ≥0∞}
    (hf : MemLp f p (volume.restrict (Ioo 0 (c * L)))) :
    MemLp (intervalDilation c f) p (volume.restrict (Ioo 0 L)) :=
  (hf.smul_measure ENNReal.ofReal_ne_top).comp_measurePreserving (measurePreserving_interval_dilation hc L)

/-- The same transport with the half-open intervals used by Fourier coefficients. -/
theorem memLp_intervalDilation_Ioc {c : ℝ} (hc : 0 < c) (L : ℝ) (f : ℝ → ℂ) {p : ℝ≥0∞}
    (hf : MemLp f p (volume.restrict (Ioc 0 (c * L)))) :
    MemLp (intervalDilation c f) p (volume.restrict (Ioc 0 L)) := by
  have hf' : MemLp f p (volume.restrict (Ioo 0 (c * L))) := by
    simpa only [Measure.restrict_congr_set Ioo_ae_eq_Ioc] using hf
  simpa only [Measure.restrict_congr_set Ioo_ae_eq_Ioc] using memLp_intervalDilation hc L f hf'

/-- The physical square integral scales by the inverse dilation. -/
theorem intervalSquareEnergy_dilation {c : ℝ} (hc : 0 < c) (L : ℝ) (f : ℝ → ℂ) :
    intervalSquareEnergy L (intervalDilation c f) = ENNReal.ofReal c⁻¹ * intervalSquareEnergy (c * L) f :=
  lintegral_interval_dilation hc L (fun x => ENNReal.ofReal (‖f x‖ ^ 2))

end NLS.Fourier
