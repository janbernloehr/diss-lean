import NLS.Fourier.IntervalSobolevBound

/-!
# Appendix A.9: uniform Fourier–Lebesgue bounds in intrinsic interval size

The constants depend only on the regularity and target exponent. The positive
subcritical and half-regularity bounds use the original interval's intrinsic
Gagliardo size. At zero, only the physical square integral is needed, including
both the Hilbert equality target and the infinity target.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace NLS.Fourier

/-- Actual interval Fourier coefficients in a finite target at the reciprocal threshold. -/
def intervalFourierLebesgueCoefficients {s q : ℝ} (hs : 0 < s) (hs₁ : s < 1 / 2)
    (hq : 1 ≤ q) (h : 1 / q < s + 1 / 2) (f : ℝ → ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 2))) (hE : fractionalIntervalEnergy s 2 f < ⊤) :
    Coeff (ENNReal.ofReal q) :=
  ⟨periodTwoCoefficient f, memlp_periodTwoCoefficient_of_interval_reciprocal hs hs₁ hq h f hf hE⟩

@[simp] theorem intervalFourierLebesgueCoefficients_apply {s q : ℝ}
    (hs : 0 < s) (hs₁ : s < 1 / 2) (hq : 1 ≤ q) (h : 1 / q < s + 1 / 2)
    (f : ℝ → ℂ) (hf : MemLp f 2 (volume.restrict (Ioc 0 2)))
    (hE : fractionalIntervalEnergy s 2 f < ⊤) (n : ℤ) :
    intervalFourierLebesgueCoefficients hs hs₁ hq h f hf hE n = periodTwoCoefficient f n := rfl

/-- A real uniform Fourier–Lebesgue constant obtained from the continuous Hölder inclusion. -/
def intervalFourierLebesgueBoundConstant {s q : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hs : 0 ≤ s) (hq : 1 ≤ q) (h : 1 / q < s + 1 / 2) : ℝ :=
  ‖WeightedCoeff.hilbertSobolevInclusion s q hs hq h‖ * Real.sqrt (intervalSobolevBoundConstant s).toReal

/-- The complete Appendix A.9 bound at positive subcritical regularity for period two. -/
theorem norm_intervalFourierLebesgueCoefficients_le {s q : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hs : 0 < s) (hs₁ : s < 1 / 2) (hq : 1 ≤ q) (h : 1 / q < s + 1 / 2)
    (f : ℝ → ℂ) (hf : MemLp f 2 (volume.restrict (Ioc 0 2)))
    (hE : fractionalIntervalEnergy s 2 f < ⊤) :
    ‖intervalFourierLebesgueCoefficients hs hs₁ hq h f hf hE‖ ≤
      intervalFourierLebesgueBoundConstant hs.le hq h * intrinsicIntervalSize s 2 f := by
  have he : intervalFourierLebesgueCoefficients hs hs₁ hq h f hf hE =
      WeightedCoeff.hilbertSobolevInclusion s q hs.le hq h (intervalSobolevCoefficients hs hs₁ f hf hE) := by
    ext n
    simp only [intervalFourierLebesgueCoefficients_apply,
      WeightedCoeff.hilbertSobolevInclusion_apply, intervalSobolevCoefficients_apply]
  rw [he]
  exact ((WeightedCoeff.hilbertSobolevInclusion s q hs.le hq h).le_opNorm _).trans
    ((mul_le_mul_of_nonneg_left (norm_intervalSobolevCoefficients_le hs hs₁ f hf hE) (norm_nonneg _)).trans_eq
      (by simp only [intervalFourierLebesgueBoundConstant, mul_assoc]))

/-- Explicit intermediate regularity used for the half-regularity consequence. -/
def halfIntervalRegularity (q : ℝ) : ℝ := (max 0 (1 / q - 1 / 2) + 1 / 2) / 2

theorem halfIntervalRegularity_spec {q : ℝ} (hq : 1 < q) :
    0 < halfIntervalRegularity q ∧ halfIntervalRegularity q < 1 / 2 ∧
      1 / q < halfIntervalRegularity q + 1 / 2 := by
  have hi : 1 / q < 1 := (div_lt_one (by linarith : 0 < q)).mpr hq
  have hm : max 0 (1 / q - 1 / 2) < (1 / 2 : ℝ) := max_lt (by norm_num) (by linarith)
  have h0 := le_max_left (0 : ℝ) (1 / q - 1 / 2)
  have h1 := le_max_right (0 : ℝ) (1 / q - 1 / 2)
  unfold halfIntervalRegularity
  exact ⟨by linarith, by linarith, by linarith⟩

/-- A real constant for the intrinsic half-regularity bound, using an explicit lower index. -/
def halfIntervalFourierLebesgueBoundConstant {q : ℝ} [Fact (1 ≤ ENNReal.ofReal q)] (hq : 1 < q) : ℝ :=
  intervalFourierLebesgueBoundConstant (halfIntervalRegularity_spec hq).1.le hq.le
    (halfIntervalRegularity_spec hq).2.2 *
      Real.sqrt (1 + ENNReal.ofReal ((2 : ℝ) ^ (2 * (1 / 2 - halfIntervalRegularity q)))).toReal

/-- Actual half-regular interval data as a Fourier–Lebesgue coefficient sequence. -/
def halfIntervalFourierLebesgueCoefficients {q : ℝ} (hq : 1 < q)
    (f : ℝ → ℂ) (hf : MemLp f 2 (volume.restrict (Ioc 0 2)))
    (hE : fractionalIntervalEnergy (1 / 2) 2 f < ⊤) : Coeff (ENNReal.ofReal q) :=
  ⟨periodTwoCoefficient f, memlp_periodTwoCoefficient_of_half_interval hq f hf hE⟩

@[simp] theorem halfIntervalFourierLebesgueCoefficients_apply {q : ℝ} (hq : 1 < q)
    (f : ℝ → ℂ) (hf : MemLp f 2 (volume.restrict (Ioc 0 2)))
    (hE : fractionalIntervalEnergy (1 / 2) 2 f < ⊤) (n : ℤ) :
    halfIntervalFourierLebesgueCoefficients hq f hf hE n = periodTwoCoefficient f n := rfl

/-- The separate half-regularity conclusion with a uniform intrinsic bound for every finite `q>1`. -/
theorem norm_halfIntervalFourierLebesgueCoefficients_le {q : ℝ} [Fact (1 ≤ ENNReal.ofReal q)] (hq : 1 < q)
    (f : ℝ → ℂ) (hf : MemLp f 2 (volume.restrict (Ioc 0 2)))
    (hE : fractionalIntervalEnergy (1 / 2) 2 f < ⊤) :
    ‖halfIntervalFourierLebesgueCoefficients hq f hf hE‖ ≤
      halfIntervalFourierLebesgueBoundConstant hq * intrinsicIntervalSize (1 / 2) 2 f := by
  obtain ⟨ht, ht₁, htq⟩ := halfIntervalRegularity_spec hq
  have htE := fractionalIntervalEnergy_lt_top_of_regularity ht.le ht₁.le (by norm_num : (0 : ℝ) < 2) f hE
  have he : halfIntervalFourierLebesgueCoefficients hq f hf hE =
      intervalFourierLebesgueCoefficients ht ht₁ hq.le htq f hf htE := by ext n; rfl
  have hf' : MemLp f 2 (volume.restrict (Ioo 0 2)) := by
    simpa only [Measure.restrict_congr_set Ioo_ae_eq_Ioc] using hf
  have hb := intrinsicIntervalSize_le_of_regularity ht.le ht₁.le (by norm_num) f hf' hE
  have hC : 0 ≤ intervalFourierLebesgueBoundConstant ht.le hq.le htq := by
    unfold intervalFourierLebesgueBoundConstant
    positivity
  rw [he]
  exact (norm_intervalFourierLebesgueCoefficients_le ht ht₁ hq.le htq f hf htE).trans
    ((mul_le_mul_of_nonneg_left hb hC).trans_eq (by
      simp only [halfIntervalFourierLebesgueBoundConstant, mul_assoc]))

/-- The coefficient sequence from interval `L²` into any larger extended exponent. -/
def intervalL2TargetCoefficients {q : ℝ≥0∞} (hq : 2 ≤ q)
    (f : ℝ → ℂ) (hf : MemLp f 2 (volume.restrict (Ioc 0 2))) : Coeff q :=
  ⟨periodTwoCoefficient f, memlp_periodTwoCoefficient_of_memLp hq f hf⟩

@[simp] theorem intervalL2TargetCoefficients_apply {q : ℝ≥0∞} (hq : 2 ≤ q)
    (f : ℝ → ℂ) (hf : MemLp f 2 (volume.restrict (Ioc 0 2))) (n : ℤ) :
    intervalL2TargetCoefficients hq f hf n = periodTwoCoefficient f n := rfl

/-- The zero-regularity bound uses only the physical square integral, including `q=2` and infinity. -/
theorem norm_intervalL2TargetCoefficients_le {q : ℝ≥0∞} [Fact (1 ≤ q)] (hq : 2 ≤ q)
    (f : ℝ → ℂ) (hf : MemLp f 2 (volume.restrict (Ioc 0 2))) :
    ‖intervalL2TargetCoefficients hq f hf‖ ≤
      Real.sqrt (1 / 2 : ℝ) * Real.sqrt (intervalSquareEnergy 2 f).toReal := by
  have he : intervalL2TargetCoefficients hq f hf = Coeff.exponentInclusion hq (periodTwoL2Coefficients f hf) := by
    ext n
    rfl
  have hf' : MemLp f 2 (volume.restrict (Ioo 0 2)) := by
    simpa only [Measure.restrict_congr_set Ioo_ae_eq_Ioc] using hf
  have hb := norm_le_sqrt_energy _ ENNReal.ofReal_lt_top (intervalSquareEnergy_lt_top f hf')
    (ofReal_norm_sq_periodTwoL2Coefficients f hf).le
  rw [he]
  exact (Coeff.norm_exponentInclusion_le hq _).trans (by simpa only [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 2)] using hb)

end NLS.Fourier
