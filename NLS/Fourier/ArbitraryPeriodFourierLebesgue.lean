import NLS.Fourier.FractionalDilation
import NLS.Fourier.IntervalCoefficientScaling
import NLS.Fourier.IntervalFourierLebesgueBound

/-!
# Appendix A.9 on every positive period

Actual normalized Fourier integrals on `[0,L]` are transported to period two.
The source's positive subcritical, zero, and half-regularity conclusions follow
with their original interval hypotheses. Uniform bounds retain the exact
physical dilation factors.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace NLS.Fourier

/-- The exact fractional scaling from an interval of length `L` to period two. -/
theorem fractionalIntervalEnergy_periodTwoDilation {L : ℝ} (hL : 0 < L) (s : ℝ) (f : ℝ → ℂ) :
    fractionalIntervalEnergy s 2 (intervalDilation (L / 2) f) =
      ENNReal.ofReal ((L / 2) ^ (2 * s - 1)) * fractionalIntervalEnergy s L f := by
  simpa only [div_mul_cancel₀ L (by norm_num : (2 : ℝ) ≠ 0)] using
    fractionalIntervalEnergy_dilation (by positivity : 0 < L / 2) s 2 f

theorem fractionalIntervalEnergy_periodTwoDilation_lt_top {L : ℝ} (hL : 0 < L) {s : ℝ} (f : ℝ → ℂ)
    (hE : fractionalIntervalEnergy s L f < ⊤) :
    fractionalIntervalEnergy s 2 (intervalDilation (L / 2) f) < ⊤ := by
  rw [fractionalIntervalEnergy_periodTwoDilation hL]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hE

/-- Uniform scaling of the intrinsic size in the original interval data. -/
theorem intrinsicIntervalSize_periodTwoDilation_le {L : ℝ} (hL : 0 < L) (s : ℝ) (f : ℝ → ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 L))) (hE : fractionalIntervalEnergy s L f < ⊤) :
    intrinsicIntervalSize s 2 (intervalDilation (L / 2) f) ≤
      Real.sqrt (intrinsicDilationConstant s (L / 2)).toReal * intrinsicIntervalSize s L f := by
  have hf' : MemLp f 2 (volume.restrict (Ioo 0 ((L / 2) * 2))) := by
    simpa only [div_mul_cancel₀ L (by norm_num : (2 : ℝ) ≠ 0), Measure.restrict_congr_set Ioo_ae_eq_Ioc] using hf
  have hE' : fractionalIntervalEnergy s ((L / 2) * 2) f < ⊤ := by simpa only [div_mul_cancel₀ L (by norm_num : (2 : ℝ) ≠ 0)] using hE
  simpa only [div_mul_cancel₀ L (by norm_num : (2 : ℝ) ≠ 0)] using
    intrinsicIntervalSize_dilation_le (by positivity : 0 < L / 2) s 2 f hf' hE'

/-- Weighted square summability of actual Fourier integrals on any positive interval below half. -/
theorem memlp_sobolev_intervalFourierCoefficient {L s : ℝ} (hL : 0 < L) (hs : 0 < s) (hs₁ : s < 1 / 2)
    (f : ℝ → ℂ) (hf : MemLp f 2 (volume.restrict (Ioc 0 L))) (hE : fractionalIntervalEnergy s L f < ⊤) :
    Memℓp (fun n => (Weight.sobolev s n : ℂ) * intervalFourierCoefficient L f n) 2 := by
  simpa only [periodTwoCoefficient_intervalDilation hL] using
    memlp_sobolev_periodTwoCoefficient_of_interval hs hs₁ (intervalDilation (L / 2) f)
      (memLp_periodTwoDilation hL f hf) (fractionalIntervalEnergy_periodTwoDilation_lt_top hL f hE)

/-- Appendix A.9's strict finite target range on every positive period. -/
theorem memlp_intervalFourierCoefficient {L s q : ℝ} (hL : 0 < L) (hs : 0 < s) (hs₁ : s < 1 / 2)
    (hq : 1 / (s + 1 / 2) < q) (f : ℝ → ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 L))) (hE : fractionalIntervalEnergy s L f < ⊤) :
    Memℓp (intervalFourierCoefficient L f) (ENNReal.ofReal q) := by
  simpa only [periodTwoCoefficient_intervalDilation_eq hL] using!
    memlp_periodTwoCoefficient_of_interval hs hs₁ hq (intervalDilation (L / 2) f)
      (memLp_periodTwoDilation hL f hf) (fractionalIntervalEnergy_periodTwoDilation_lt_top hL f hE)

/-- At zero regularity, arbitrary-period `L²` suffices for every extended target at least two. -/
theorem memlp_intervalFourierCoefficient_of_memLp {L : ℝ} {q : ℝ≥0∞} (hL : 0 < L) (hq : 2 ≤ q)
    (f : ℝ → ℂ) (hf : MemLp f 2 (volume.restrict (Ioc 0 L))) : Memℓp (intervalFourierCoefficient L f) q := by
  simpa only [periodTwoCoefficient_intervalDilation_eq hL] using!
    memlp_periodTwoCoefficient_of_memLp hq (intervalDilation (L / 2) f) (memLp_periodTwoDilation hL f hf)

/-- The unified source range including zero, with a vacuous fractional hypothesis at zero. -/
theorem memlp_intervalFourierCoefficient_of_nonneg {L s q : ℝ} (hL : 0 < L) (hs : 0 ≤ s) (hs₁ : s < 1 / 2)
    (hq : 1 / (s + 1 / 2) < q) (f : ℝ → ℂ) (hf : MemLp f 2 (volume.restrict (Ioc 0 L)))
    (hE : 0 < s → fractionalIntervalEnergy s L f < ⊤) : Memℓp (intervalFourierCoefficient L f) (ENNReal.ofReal q) := by
  simpa only [periodTwoCoefficient_intervalDilation_eq hL] using!
    memlp_periodTwoCoefficient_of_nonneg_interval hs hs₁ hq (intervalDilation (L / 2) f)
      (memLp_periodTwoDilation hL f hf) (fun hs => fractionalIntervalEnergy_periodTwoDilation_lt_top hL f (hE hs))

/-- The separate half-regularity conclusion for every positive interval length. -/
theorem memlp_intervalFourierCoefficient_of_half {L q : ℝ} (hL : 0 < L) (hq : 1 < q)
    (f : ℝ → ℂ) (hf : MemLp f 2 (volume.restrict (Ioc 0 L))) (hE : fractionalIntervalEnergy (1 / 2) L f < ⊤) :
    Memℓp (intervalFourierCoefficient L f) (ENNReal.ofReal q) := by
  simpa only [periodTwoCoefficient_intervalDilation_eq hL] using!
    memlp_periodTwoCoefficient_of_half_interval hq (intervalDilation (L / 2) f)
      (memLp_periodTwoDilation hL f hf) (fractionalIntervalEnergy_periodTwoDilation_lt_top hL f hE)

/-- Package actual arbitrary-period Fourier coefficients with any proved sequence membership. -/
def intervalFourierCoefficients {p : ℝ≥0∞} (L : ℝ) (f : ℝ → ℂ)
    (h : Memℓp (intervalFourierCoefficient L f) p) : Coeff p := ⟨intervalFourierCoefficient L f, h⟩

@[simp] theorem intervalFourierCoefficients_apply {p : ℝ≥0∞} (L : ℝ) (f : ℝ → ℂ)
    (h : Memℓp (intervalFourierCoefficient L f) p) (n : ℤ) :
    intervalFourierCoefficients L f h n = intervalFourierCoefficient L f n := rfl

/-- A uniform arbitrary-period constant in the positive subcritical source range. -/
def arbitraryPeriodFourierBoundConstant {s q : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (L : ℝ) (hs : 0 < s) (hs₁ : s < 1 / 2) (hq : 1 / (s + 1 / 2) < q) : ℝ :=
  intervalFourierLebesgueBoundConstant hs.le (intervalFourierLebesgue_threshold hs.le hs₁ hq).1.le
    (intervalFourierLebesgue_threshold hs.le hs₁ hq).2 * Real.sqrt (intrinsicDilationConstant s (L / 2)).toReal

/-- Uniform A.9 norm bound for actual arbitrary-period Fourier coefficients. -/
theorem norm_intervalFourierCoefficients_le {L s q : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hL : 0 < L) (hs : 0 < s) (hs₁ : s < 1 / 2) (hq : 1 / (s + 1 / 2) < q)
    (f : ℝ → ℂ) (hf : MemLp f 2 (volume.restrict (Ioc 0 L))) (hE : fractionalIntervalEnergy s L f < ⊤)
    (hm : Memℓp (intervalFourierCoefficient L f) (ENNReal.ofReal q)) :
    ‖intervalFourierCoefficients L f hm‖ ≤ arbitraryPeriodFourierBoundConstant L hs hs₁ hq * intrinsicIntervalSize s L f := by
  obtain ⟨hq₁, hqr⟩ := intervalFourierLebesgue_threshold hs.le hs₁ hq
  let g := intervalDilation (L / 2) f
  have hg := memLp_periodTwoDilation hL f hf
  have hgE := fractionalIntervalEnergy_periodTwoDilation_lt_top hL f hE
  have he : intervalFourierCoefficients L f hm = intervalFourierLebesgueCoefficients hs hs₁ hq₁.le hqr g hg hgE := by
    ext n
    simp only [intervalFourierCoefficients_apply, intervalFourierLebesgueCoefficients_apply, g,
      periodTwoCoefficient_intervalDilation hL]
  have hb := intrinsicIntervalSize_periodTwoDilation_le hL s f hf hE
  have hC : 0 ≤ intervalFourierLebesgueBoundConstant hs.le hq₁.le hqr := by
    unfold intervalFourierLebesgueBoundConstant
    positivity
  rw [he]
  exact (norm_intervalFourierLebesgueCoefficients_le hs hs₁ hq₁.le hqr g hg hgE).trans
    ((mul_le_mul_of_nonneg_left hb hC).trans_eq (by simp only [arbitraryPeriodFourierBoundConstant, mul_assoc]))

/-- Uniform half-regularity bound in the original arbitrary-period intrinsic size. -/
theorem norm_intervalFourierCoefficients_half_le {L q : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hL : 0 < L) (hq : 1 < q) (f : ℝ → ℂ) (hf : MemLp f 2 (volume.restrict (Ioc 0 L)))
    (hE : fractionalIntervalEnergy (1 / 2) L f < ⊤)
    (hm : Memℓp (intervalFourierCoefficient L f) (ENNReal.ofReal q)) :
    ‖intervalFourierCoefficients L f hm‖ ≤
      (halfIntervalFourierLebesgueBoundConstant hq * Real.sqrt (intrinsicDilationConstant (1 / 2) (L / 2)).toReal) *
        intrinsicIntervalSize (1 / 2) L f := by
  let g := intervalDilation (L / 2) f
  have hg := memLp_periodTwoDilation hL f hf
  have hgE := fractionalIntervalEnergy_periodTwoDilation_lt_top hL f hE
  have he : intervalFourierCoefficients L f hm = halfIntervalFourierLebesgueCoefficients hq g hg hgE := by
    ext n
    simp only [intervalFourierCoefficients_apply, halfIntervalFourierLebesgueCoefficients_apply, g,
      periodTwoCoefficient_intervalDilation hL]
  have hC : 0 ≤ halfIntervalFourierLebesgueBoundConstant hq := by
    unfold halfIntervalFourierLebesgueBoundConstant intervalFourierLebesgueBoundConstant
    positivity
  rw [he]
  exact (norm_halfIntervalFourierLebesgueCoefficients_le hq g hg hgE).trans
    ((mul_le_mul_of_nonneg_left (intrinsicIntervalSize_periodTwoDilation_le hL (1 / 2) f hf hE) hC).trans_eq
      (mul_assoc _ _ _).symm)

/-- The zero-regularity constant on length `L` is exactly `L^(-1/2)`, including infinity targets. -/
theorem norm_intervalFourierCoefficients_of_memLp_le {L : ℝ} {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (hL : 0 < L) (hq : 2 ≤ q) (f : ℝ → ℂ) (hf : MemLp f 2 (volume.restrict (Ioc 0 L)))
    (hm : Memℓp (intervalFourierCoefficient L f) q) :
    ‖intervalFourierCoefficients L f hm‖ ≤ Real.sqrt (1 / L) * Real.sqrt (intervalSquareEnergy L f).toReal := by
  have hg := memLp_periodTwoDilation hL f hf
  have he : intervalFourierCoefficients L f hm = intervalL2TargetCoefficients hq (intervalDilation (L / 2) f) hg := by
    ext n
    simp only [intervalFourierCoefficients_apply, intervalL2TargetCoefficients_apply, periodTwoCoefficient_intervalDilation hL]
  have hb := norm_intervalL2TargetCoefficients_le hq (intervalDilation (L / 2) f) hg
  rw [intervalSquareEnergy_dilation (by positivity : 0 < L / 2),
    div_mul_cancel₀ L (by norm_num : (2 : ℝ) ≠ 0), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ (L / 2)⁻¹),
    Real.sqrt_mul (by positivity : 0 ≤ (L / 2)⁻¹), ← mul_assoc,
    ← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hb
  rw [show (1 / 2 : ℝ) * (L / 2)⁻¹ = 1 / L by field_simp] at hb
  rw [he]
  exact hb

end NLS.Fourier
