import NLS.Fourier.FractionalIntervalEmbedding

/-!
# Intrinsic interval square energy and fractional size

The inhomogeneous energy retains the square-integral term controlling constants.
For positive fractional regularity its square root is the intrinsic Gagliardo
size. At zero regularity, use the square-integral term alone instead.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace NLS.Fourier

/-- Unnormalized physical square energy on an interval. -/
def intervalSquareEnergy (L : ℝ) (f : ℝ → ℂ) : ℝ≥0∞ :=
  ∫⁻ x : ℝ in Ioo 0 L, ENNReal.ofReal (‖f x‖ ^ 2)

/-- Intrinsic inhomogeneous fractional energy, intended for positive regularity. -/
def intrinsicIntervalEnergy (s L : ℝ) (f : ℝ → ℂ) : ℝ≥0∞ :=
  intervalSquareEnergy L f + fractionalIntervalEnergy s L f

/-- The square root of finite intrinsic interval energy; finiteness is required in norm estimates. -/
def intrinsicIntervalSize (s L : ℝ) (f : ℝ → ℂ) : ℝ :=
  Real.sqrt (intrinsicIntervalEnergy s L f).toReal

theorem intervalSquareEnergy_congr {L : ℝ} {f g : ℝ → ℂ}
    (h : f =ᵐ[volume.restrict (Ioo 0 L)] g) : intervalSquareEnergy L f = intervalSquareEnergy L g := by
  apply lintegral_congr_ae
  filter_upwards [h] with x hx
  rw [hx]

theorem intrinsicIntervalEnergy_congr {s L : ℝ} {f g : ℝ → ℂ}
    (h : f =ᵐ[volume.restrict (Ioo 0 L)] g) : intrinsicIntervalEnergy s L f = intrinsicIntervalEnergy s L g := by
  rw [intrinsicIntervalEnergy, intrinsicIntervalEnergy, intervalSquareEnergy_congr h,
    fractionalIntervalEnergy_congr h]

theorem intervalSquareEnergy_lt_top {L : ℝ} (f : ℝ → ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioo 0 L))) : intervalSquareEnergy L f < ⊤ := by
  have hi := hf.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  exact (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (fun _ => sq_nonneg _))).mp hi.2

theorem intrinsicIntervalEnergy_lt_top {s L : ℝ} (f : ℝ → ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioo 0 L))) (hE : fractionalIntervalEnergy s L f < ⊤) :
    intrinsicIntervalEnergy s L f < ⊤ := ENNReal.add_lt_top.mpr ⟨intervalSquareEnergy_lt_top f hf, hE⟩

@[simp] theorem intrinsicIntervalSize_sq (s L : ℝ) (f : ℝ → ℂ) :
    intrinsicIntervalSize s L f ^ 2 = (intrinsicIntervalEnergy s L f).toReal :=
  Real.sq_sqrt ENNReal.toReal_nonneg

theorem intrinsicIntervalSize_nonneg (s L : ℝ) (f : ℝ → ℂ) : 0 ≤ intrinsicIntervalSize s L f :=
  Real.sqrt_nonneg _

/-- A finite energy estimate gives the corresponding real square-root estimate. -/
theorem norm_le_sqrt_energy {A : Type*} [SeminormedAddCommGroup A]
    (a : A) {C E : ℝ≥0∞} (hC : C < ⊤) (hE : E < ⊤)
    (h : ENNReal.ofReal (‖a‖ ^ 2) ≤ C * E) :
    ‖a‖ ≤ Real.sqrt C.toReal * Real.sqrt E.toReal := by
  have hr := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top (ENNReal.mul_lt_top hC hE).ne).mpr h
  rw [ENNReal.toReal_ofReal (sq_nonneg _), ENNReal.toReal_mul] at hr
  calc
    _ ≤ Real.sqrt (C.toReal * E.toReal) := (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr hr
    _ = _ := Real.sqrt_mul ENNReal.toReal_nonneg _

/-- A diameter bound for the full inhomogeneous energy on any positive interval. -/
theorem intrinsicIntervalEnergy_le_of_regularity {t s L : ℝ}
    (ht : 0 ≤ t) (hts : t ≤ s) (hL : 0 < L) (f : ℝ → ℂ) :
    intrinsicIntervalEnergy t L f ≤
      (1 + ENNReal.ofReal (L ^ (2 * (s - t)))) * intrinsicIntervalEnergy s L f := by
  have hN : intervalSquareEnergy L f ≤ intrinsicIntervalEnergy s L f := le_add_right le_rfl
  have hE : fractionalIntervalEnergy s L f ≤ intrinsicIntervalEnergy s L f := le_add_left le_rfl
  calc
    _ ≤ intrinsicIntervalEnergy s L f +
        ENNReal.ofReal (L ^ (2 * (s - t))) * intrinsicIntervalEnergy s L f :=
      add_le_add hN ((fractionalIntervalEnergy_le_of_regularity ht hts hL f).trans (mul_le_mul' le_rfl hE))
    _ = _ := by rw [add_mul, one_mul]

/-- Quantitative lowering of intrinsic size, with the energy finiteness needed by `toReal`. -/
theorem intrinsicIntervalSize_le_of_regularity {t s L : ℝ}
    (ht : 0 ≤ t) (hts : t ≤ s) (hL : 0 < L) (f : ℝ → ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioo 0 L))) (hE : fractionalIntervalEnergy s L f < ⊤) :
    intrinsicIntervalSize t L f ≤
      Real.sqrt (1 + ENNReal.ofReal (L ^ (2 * (s - t)))).toReal * intrinsicIntervalSize s L f := by
  have htE := fractionalIntervalEnergy_lt_top_of_regularity ht hts hL f hE
  have hbound : ENNReal.ofReal (‖intrinsicIntervalSize t L f‖ ^ 2) ≤
      (1 + ENNReal.ofReal (L ^ (2 * (s - t)))) * intrinsicIntervalEnergy s L f := by
    rw [Real.norm_of_nonneg (intrinsicIntervalSize_nonneg t L f), intrinsicIntervalSize_sq,
      ENNReal.ofReal_toReal (intrinsicIntervalEnergy_lt_top f hf htE).ne]
    exact intrinsicIntervalEnergy_le_of_regularity ht hts hL f
  simpa only [Real.norm_of_nonneg (intrinsicIntervalSize_nonneg t L f)] using!
    norm_le_sqrt_energy (intrinsicIntervalSize t L f)
      (ENNReal.add_lt_top.mpr ⟨by norm_num, ENNReal.ofReal_lt_top⟩)
      (intrinsicIntervalEnergy_lt_top f hf hE) hbound

end NLS.Fourier
