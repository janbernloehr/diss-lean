import NLS.ZakharovShabat.FiniteIntervalExtension
import NLS.Fourier.IntervalParseval
import NLS.SequenceSpaces.FiniteCoefficients

/-!
# The bounded interval extension at the Hilbert exponent

Parseval gives an exact energy identity for finite input, hence a uniform bound.
Density extends the actual finite Fourier construction to all period-one `ℓ2`
pairs, with range in the chosen boundary space. Other exponents remain separate.
-/

noncomputable section
open Complex MeasureTheory
open scoped ENNReal
namespace NLS.ZakharovShabat.BoundaryCondition
open NLS.Fourier

/-- The raw finite input pair inside its period-one coefficient norm. -/
def finitePairCoeffs {p : ℝ≥0∞} : ((ℤ →₀ ℂ) × (ℤ →₀ ℂ)) →ₗ[ℂ] PairSpace p :=
  Coeff.ofFinsupp.prodMap Coeff.ofFinsupp

@[simp] theorem finitePairCoeffs_apply {p : ℝ≥0∞} (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) :
    finitePairCoeffs (p := p) a = (Coeff.ofFinsupp a.1, Coeff.ofFinsupp a.2) := rfl

theorem denseRange_finitePairCoeffs {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) :
    DenseRange (finitePairCoeffs (p := p)) :=
  (Coeff.denseRange_ofFinsupp hp).prodMap (Coeff.denseRange_ofFinsupp hp)

variable (b : BoundaryCondition)

/-- Both boundary embeddings have exactly the amplitude norm. -/
theorem norm_finiteIntervalExtension {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p)
    (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) :
    ‖finiteIntervalExtension b hp a‖ = ‖finiteIntervalAmplitude b hp a‖ := by
  change ‖(extensionSign b • Coeff.reflection (finiteIntervalAmplitude b hp a),
    finiteIntervalAmplitude b hp a)‖ = _
  cases b <;> simp [extensionSign, Prod.norm_def]

/-- The reflected halves give the mean of the two input energies, with no cross term. -/
theorem norm_finiteIntervalAmplitude_sq (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) :
    ‖finiteIntervalAmplitude b (p := 2) (by norm_num) a‖ ^ 2 =
      (‖Coeff.ofFinsupp (p := 2) a.1‖ ^ 2 + ‖Coeff.ofFinsupp (p := 2) a.2‖ ^ 2) / 2 := by
  let f := folded (extensionSign b) (polynomial a.2) (polynomial a.1)
  have hc (n : ℤ) : periodTwoCoefficient f n = finiteIntervalAmplitude b (p := 2) (by norm_num) a n := by
    rw [finiteIntervalAmplitude_apply]
    exact periodTwoCoefficient_folded _ _ _ (continuous_polynomial a.2) (continuous_polynomial a.1) n
  have h := (hasSum_sq_periodTwoCoefficient
    (memLp_two_folded (extensionSign b) (continuous_polynomial a.2) (continuous_polynomial a.1))).tsum_eq
  have hn := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    (finiteIntervalAmplitude b (p := 2) (by norm_num) a)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hn
  change (∑' n, ‖periodTwoCoefficient f n‖ ^ 2) = _ at h
  simp only [hc] at h
  rw [hn, h, integral_sq_folded _ (by cases b <;> simp [extensionSign])
    (continuous_polynomial a.2) (continuous_polynomial a.1),
    integral_sq_polynomial, integral_sq_polynomial,
    Coeff.norm_ofFinsupp_sq, Coeff.norm_ofFinsupp_sq]
  ring

/-- A uniform norm-one bound in the original maximum pair norm, at `p=2`. -/
theorem norm_finiteIntervalExtension_two_le (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) :
    ‖finiteIntervalExtension b (p := 2) (by norm_num) a‖ ≤ ‖finitePairCoeffs (p := 2) a‖ := by
  rw [norm_finiteIntervalExtension]
  have h := norm_finiteIntervalAmplitude_sq b a
  have h1 := norm_fst_le (finitePairCoeffs (p := 2) a)
  have h2 := norm_snd_le (finitePairCoeffs (p := 2) a)
  have h1' := sq_le_sq₀ (norm_nonneg (Coeff.ofFinsupp (p := 2) a.1))
    (norm_nonneg (finitePairCoeffs (p := 2) a))
  have h2' := sq_le_sq₀ (norm_nonneg (Coeff.ofFinsupp (p := 2) a.2))
    (norm_nonneg (finitePairCoeffs (p := 2) a))
  have hs1 := h1'.mpr h1
  have hs2 := h2'.mpr h2
  nlinarith [norm_nonneg (finiteIntervalAmplitude b (p := 2) (by norm_num) a),
    norm_nonneg (finitePairCoeffs (p := 2) a)]

/-- The extension to arbitrary Hilbert coefficients, obtained from the proved uniform bound. -/
def hilbertIntervalExtension : PairSpace 2 →L[ℂ] PairSpace 2 :=
  (finiteIntervalExtension b (p := 2) (by norm_num)).extendOfNorm finitePairCoeffs

/-- The completed map agrees with physical finite Fourier extension. -/
theorem hilbertIntervalExtension_finite (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) :
    hilbertIntervalExtension b (finitePairCoeffs a) = finiteIntervalExtension b (by norm_num) a :=
  LinearMap.extendOfNorm_eq (f := finiteIntervalExtension b (p := 2) (by norm_num))
    (e := finitePairCoeffs (p := 2)) (denseRange_finitePairCoeffs (by simp))
    ⟨1, fun c => by simpa only [one_mul] using norm_finiteIntervalExtension_two_le b c⟩ a

theorem norm_hilbertIntervalExtension_le : ‖hilbertIntervalExtension b‖ ≤ 1 :=
  LinearMap.opNorm_extendOfNorm_le (f := finiteIntervalExtension b (p := 2) (by norm_num))
    (e := finitePairCoeffs (p := 2)) (denseRange_finitePairCoeffs (by simp)) (by norm_num)
    (fun c => by simpa only [one_mul] using norm_finiteIntervalExtension_two_le b c)

theorem norm_hilbertIntervalExtension_apply_le (a : PairSpace 2) :
    ‖hilbertIntervalExtension b a‖ ≤ ‖a‖ := by
  simpa using (hilbertIntervalExtension b).le_of_opNorm_le (norm_hilbertIntervalExtension_le b) a

/-- The completed extension retains the selected boundary reflection relation. -/
theorem hilbertIntervalExtension_mem (a : PairSpace 2) : hilbertIntervalExtension b a ∈ space b := by
  refine Dense.induction (denseRange_finitePairCoeffs (p := 2) (by simp)) ?_
    ((isClosed_space b).preimage (hilbertIntervalExtension b).continuous) a
  rintro _ ⟨c, rfl⟩
  rw [hilbertIntervalExtension_finite]
  exact finiteIntervalExtension_mem b _ c

/-- The exact finite-input energy identity persists under completion. -/
theorem norm_hilbertIntervalExtension_sq (a : PairSpace 2) :
    ‖hilbertIntervalExtension b a‖ ^ 2 = (‖a.1‖ ^ 2 + ‖a.2‖ ^ 2) / 2 := by
  refine Dense.induction (denseRange_finitePairCoeffs (p := 2) (by simp)) ?_
    (isClosed_eq (by fun_prop) (by fun_prop)) a
  rintro _ ⟨c, rfl⟩
  rw [hilbertIntervalExtension_finite, norm_finiteIntervalExtension]
  exact norm_finiteIntervalAmplitude_sq b c

/-- Completion does not lose any information from the original coefficient pair. -/
theorem hilbertIntervalExtension_injective : Function.Injective (hilbertIntervalExtension b) := by
  intro a c h
  have hz : hilbertIntervalExtension b (a - c) = 0 := by rw [map_sub, h, sub_self]
  have hn := norm_hilbertIntervalExtension_sq b (a - c)
  rw [hz, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hn
  have h1 : ‖(a - c).1‖ = 0 := by nlinarith [norm_nonneg (a - c).1, sq_nonneg ‖(a - c).2‖]
  have h2 : ‖(a - c).2‖ = 0 := by nlinarith [norm_nonneg (a - c).2, sq_nonneg ‖(a - c).1‖]
  exact sub_eq_zero.mp (Prod.ext (norm_eq_zero.mp h1) (norm_eq_zero.mp h2))

/-- The finite Fourier formulas determine the completed continuous map uniquely. -/
theorem hilbertIntervalExtension_unique (F : PairSpace 2 →L[ℂ] PairSpace 2)
    (hF : ∀ c, F (finitePairCoeffs c) = finiteIntervalExtension b (by norm_num) c) :
    F = hilbertIntervalExtension b := by
  have he : (F : PairSpace 2 → PairSpace 2) = hilbertIntervalExtension b := by
    apply (denseRange_finitePairCoeffs (p := 2) (by simp)).equalizer F.continuous
      (hilbertIntervalExtension b).continuous
    funext c
    exact (hF c).trans (hilbertIntervalExtension_finite b c).symm
  exact ContinuousLinearMap.ext (congrFun he)

end NLS.ZakharovShabat.BoundaryCondition
