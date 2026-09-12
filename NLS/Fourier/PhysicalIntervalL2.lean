import NLS.Fourier.FractionalDifferenceQuotient

/-!
# Physical interval representatives of the `L²` quotient

A period-two `L²` class represents data on `[0,L]` by the coordinate change
`x ↦ 2x/L`. Every square-integrable interval function is recovered almost
everywhere. The square-energy normalization is `L`, and the normalized
Fourier coefficients are unchanged.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace NLS.Fourier

/-- Physical data on an interval of length `L`, represented by an actual `L²` quotient class. -/
def intervalPullback (L : ℝ) (f : CircleL2) : ℝ → ℂ := intervalDilation (2 / L) (circlePullback f)

@[fun_prop] theorem measurable_intervalPullback (L : ℝ) (f : CircleL2) : Measurable (intervalPullback L f) := by
  unfold intervalPullback intervalDilation
  exact (measurable_circlePullback f).comp (by fun_prop)

@[simp] theorem intervalPullback_two (f : CircleL2) : intervalPullback 2 f = circlePullback f := by
  simp [intervalPullback]

/-- Positive interval dilation transports almost-everywhere equality. -/
theorem ae_intervalDilation {c : ℝ} (hc : 0 < c) (L : ℝ) {f g : ℝ → ℂ}
    (h : f =ᵐ[volume.restrict (Ioo 0 (c * L))] g) :
    intervalDilation c f =ᵐ[volume.restrict (Ioo 0 L)] intervalDilation c g :=
  (measurePreserving_interval_dilation hc L).quasiMeasurePreserving.ae_eq
    (Measure.ae_smul_measure h (ENNReal.ofReal c⁻¹))

/-- Circle almost-everywhere equality pulls back to the whole physical interval. -/
theorem interval_ae_pullback {L : ℝ} (hL : 0 < L) {f g : AddCircle (2 : ℝ) → ℂ}
    (h : f =ᵐ[AddCircle.haarAddCircle] g) :
    (fun x : ℝ => f ((2 / L * x : ℝ) : AddCircle (2 : ℝ))) =ᵐ[volume.restrict (Ioo 0 L)]
      fun x : ℝ => g ((2 / L * x : ℝ) : AddCircle (2 : ℝ)) := by
  have hh : (fun x : ℝ => f (x : AddCircle (2 : ℝ))) =ᵐ[volume.restrict (Ioo 0 ((2 / L) * L))]
      fun x : ℝ => g (x : AddCircle (2 : ℝ)) := by
    simpa only [div_mul_cancel₀ 2 hL.ne', Measure.restrict_congr_set Ioo_ae_eq_Ioc] using circle_ae_pullback h
  exact ae_intervalDilation (by positivity : 0 < 2 / L) L hh

theorem intervalPullback_zero {L : ℝ} (hL : 0 < L) :
    intervalPullback L (0 : CircleL2) =ᵐ[volume.restrict (Ioo 0 L)] 0 := by
  simpa only [intervalPullback, intervalDilation, circlePullback] using!
    interval_ae_pullback hL (Lp.coeFn_zero ℂ 2 AddCircle.haarAddCircle)

theorem intervalPullback_add {L : ℝ} (hL : 0 < L) (f g : CircleL2) :
    intervalPullback L (f + g) =ᵐ[volume.restrict (Ioo 0 L)] intervalPullback L f + intervalPullback L g := by
  simpa only [intervalPullback, intervalDilation, circlePullback, Pi.add_apply] using!
    interval_ae_pullback hL (Lp.coeFn_add f g)

theorem intervalPullback_smul {L : ℝ} (hL : 0 < L) (c : ℂ) (f : CircleL2) :
    intervalPullback L (c • f) =ᵐ[volume.restrict (Ioo 0 L)] c • intervalPullback L f := by
  simpa only [intervalPullback, intervalDilation, circlePullback, Pi.smul_apply] using!
    interval_ae_pullback hL (Lp.coeFn_smul c f)

/-- These representatives are square integrable on the original length interval. -/
theorem memLp_intervalPullback {L : ℝ} (hL : 0 < L) (f : CircleL2) :
    MemLp (intervalPullback L f) 2 (volume.restrict (Ioc 0 L)) := by
  apply memLp_intervalDilation_Ioc (by positivity) L (circlePullback f)
  simpa only [div_mul_cancel₀ 2 hL.ne'] using memLp_circlePullback f

/-- Rescaling the physical interval back to period two recovers its circle representative pointwise. -/
theorem intervalDilation_intervalPullback {L : ℝ} (hL : 0 < L) (f : CircleL2) :
    intervalDilation (L / 2) (intervalPullback L f) = circlePullback f := by
  funext x
  simp only [intervalPullback, intervalDilation]
  congr 1
  field_simp

/-- Normalized physical interval coefficients are the coefficients of the stored `L²` class. -/
theorem intervalFourierCoefficient_intervalPullback {L : ℝ} (hL : 0 < L) (f : CircleL2) (n : ℤ) :
    intervalFourierCoefficient L (intervalPullback L f) n = fourierCoeff f n := by
  rw [← periodTwoCoefficient_intervalDilation hL, intervalDilation_intervalPullback hL,
    periodTwoCoefficient_circlePullback]

/-- The unnormalized physical square energy is exactly length times the normalized circle norm squared. -/
theorem intervalSquareEnergy_intervalPullback {L : ℝ} (hL : 0 < L) (f : CircleL2) :
    intervalSquareEnergy L (intervalPullback L f) = ENNReal.ofReal L * ENNReal.ofReal (‖f‖ ^ 2) := by
  rw [intervalPullback, intervalSquareEnergy_dilation (by positivity : 0 < 2 / L),
    div_mul_cancel₀ 2 hL.ne', intervalSquareEnergy_circlePullback, ← mul_assoc]
  congr 1
  rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by positivity : 0 ≤ (2 / L)⁻¹)]
  congr 1
  field_simp

/-- The quotient class associated with arbitrary square-integrable original interval data. -/
def intervalL2Class {L : ℝ} (hL : 0 < L) (f : ℝ → ℂ) (hf : MemLp f 2 (volume.restrict (Ioc 0 L))) : CircleL2 :=
  l2Synthesis (periodTwoL2Coefficients (intervalDilation (L / 2) f) (memLp_periodTwoDilation hL f hf))

@[simp] theorem fourierCoeff_intervalL2Class {L : ℝ} (hL : 0 < L) (f : ℝ → ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 L))) (n : ℤ) :
    fourierCoeff (intervalL2Class hL f hf) n = intervalFourierCoefficient L f n := by
  rw [intervalL2Class, fourierCoeff_l2Synthesis, periodTwoL2Coefficients_apply,
    periodTwoCoefficient_intervalDilation hL]

/-- The quotient reconstructs arbitrary interval data almost everywhere, without endpoint matching. -/
theorem intervalPullback_intervalL2Class {L : ℝ} (hL : 0 < L) (f : ℝ → ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 L))) :
    intervalPullback L (intervalL2Class hL f hf) =ᵐ[volume.restrict (Ioo 0 L)] f := by
  have he : circlePullback (intervalL2Class hL f hf) =ᵐ[volume.restrict (Ioo 0 ((2 / L) * L))]
      intervalDilation (L / 2) f := by
    simpa only [div_mul_cancel₀ 2 hL.ne', Measure.restrict_congr_set Ioo_ae_eq_Ioc, intervalL2Class] using!
      circlePullback_periodTwoL2Coefficients (intervalDilation (L / 2) f) (memLp_periodTwoDilation hL f hf)
  have hh := ae_intervalDilation (by positivity : 0 < 2 / L) L he
  have hf' : intervalDilation (2 / L) (intervalDilation (L / 2) f) = f := by
    funext x
    unfold intervalDilation
    congr 1
    field_simp
  simpa only [intervalPullback, hf'] using! hh

@[simp] theorem intervalL2Class_intervalPullback {L : ℝ} (hL : 0 < L) (f : CircleL2) :
    intervalL2Class hL (intervalPullback L f) (memLp_intervalPullback hL f) = f := by
  apply fourierBasis.repr.injective
  ext n
  simp only [fourierBasis_repr, fourierCoeff_intervalL2Class, intervalFourierCoefficient_intervalPullback hL]

/-- Arbitrary representatives yield the same quotient whenever they agree on the interval almost everywhere. -/
theorem intervalL2Class_congr {L : ℝ} (hL : 0 < L) (f g : ℝ → ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 L))) (hg : MemLp g 2 (volume.restrict (Ioc 0 L)))
    (h : f =ᵐ[volume.restrict (Ioo 0 L)] g) : intervalL2Class hL f hf = intervalL2Class hL g hg := by
  have he : f =ᵐ[volume.restrict (Ioo 0 ((L / 2) * 2))] g := by
    simpa only [div_mul_cancel₀ L (by norm_num : (2 : ℝ) ≠ 0)] using h
  have hd := ae_intervalDilation (by positivity : 0 < L / 2) 2 he
  unfold intervalL2Class
  congr 1
  apply periodTwoL2Coefficients_congr
  simpa only [Measure.restrict_congr_set Ioo_ae_eq_Ioc] using hd

/-- The physical representative is faithful precisely modulo interval almost-everywhere equality. -/
theorem intervalPullback_eq_iff {L : ℝ} (hL : 0 < L) (f g : CircleL2) :
    intervalPullback L f =ᵐ[volume.restrict (Ioo 0 L)] intervalPullback L g ↔ f = g := by
  constructor
  · intro h
    simpa only [intervalL2Class_intervalPullback] using
      intervalL2Class_congr hL _ _ (memLp_intervalPullback hL f) (memLp_intervalPullback hL g) h
  · rintro rfl
    rfl

end NLS.Fourier
