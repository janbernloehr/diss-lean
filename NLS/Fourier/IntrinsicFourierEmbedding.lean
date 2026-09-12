import NLS.Fourier.IntrinsicIntervalSobolev

/-!
# Continuous Fourier embeddings from the intrinsic interval norm

Appendix A.9 is realized as continuous complex-linear injections on the
physical Sobolev quotient, on every positive interval. Both positive
subcritical regularity and the separate half-regularity case use exactly
the actual normalized Fourier integrals of the original input.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace NLS.Fourier.IntrinsicIntervalSobolev
variable {s L : ℝ} [Fact (0 < L)]

/-- Actual coefficient linear map whenever its target membership has been proved. -/
def coefficientMap (p : ℝ≥0∞)
    (hm : ∀ f : IntrinsicIntervalSobolev s L, Memℓp (intervalFourierCoefficient L (intervalPullback L f.val)) p) :
    IntrinsicIntervalSobolev s L →ₗ[ℂ] Coeff p where
  toFun f := intervalFourierCoefficients L (intervalPullback L f.val) (hm f)
  map_add' f g := by
    ext n
    change intervalFourierCoefficient L (intervalPullback L (f.val + g.val)) n =
      intervalFourierCoefficient L (intervalPullback L f.val) n + intervalFourierCoefficient L (intervalPullback L g.val) n
    simp only [intervalFourierCoefficient_intervalPullback (Fact.out : 0 < L),
      ← fourierBasis_repr, map_add, lp.coeFn_add, Pi.add_apply]
  map_smul' c f := by
    ext n
    change intervalFourierCoefficient L (intervalPullback L (c • f.val)) n =
      c * intervalFourierCoefficient L (intervalPullback L f.val) n
    simp only [intervalFourierCoefficient_intervalPullback (Fact.out : 0 < L),
      ← fourierBasis_repr, map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]

@[simp] theorem coefficientMap_apply {p : ℝ≥0∞}
    (hm : ∀ f : IntrinsicIntervalSobolev s L, Memℓp (intervalFourierCoefficient L (intervalPullback L f.val)) p)
    (f : IntrinsicIntervalSobolev s L) (n : ℤ) :
    coefficientMap p hm f n = intervalFourierCoefficient L (intervalPullback L f.val) n := rfl

/-- Fourier uniqueness makes every such coefficient map injective. -/
theorem coefficientMap_injective {p : ℝ≥0∞}
    (hm : ∀ f : IntrinsicIntervalSobolev s L, Memℓp (intervalFourierCoefficient L (intervalPullback L f.val)) p) :
    Function.Injective (coefficientMap p hm) := by
  intro f g h
  apply Subtype.ext
  apply fourierBasis.repr.injective
  ext n
  have he := congrArg (fun a : Coeff p => a n) h
  simpa only [coefficientMap_apply, intervalFourierCoefficient_intervalPullback (Fact.out : 0 < L),
    fourierBasis_repr] using he

/-- A.9's continuous Fourier injection below half regularity in the exact intrinsic norm. -/
def fourierEmbedding {q : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hs : 0 < s) (hs₁ : s < 1 / 2) (hq : 1 / (s + 1 / 2) < q) :
    IntrinsicIntervalSobolev s L →L[ℂ] Coeff (ENNReal.ofReal q) :=
  (coefficientMap _ (fun f => memlp_intervalFourierCoefficient (Fact.out : 0 < L) hs hs₁ hq _
    (memLp_intervalPullback (Fact.out : 0 < L) f.val) f.energy_lt_top)).mkContinuous
    (arbitraryPeriodFourierBoundConstant L hs hs₁ hq) (fun f => by
      simpa only [norm_eq_size] using! norm_intervalFourierCoefficients_le (Fact.out : 0 < L) hs hs₁ hq _
        (memLp_intervalPullback (Fact.out : 0 < L) f.val) f.energy_lt_top _)

@[simp] theorem fourierEmbedding_apply {q : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hs : 0 < s) (hs₁ : s < 1 / 2) (hq : 1 / (s + 1 / 2) < q)
    (f : IntrinsicIntervalSobolev s L) (n : ℤ) :
    fourierEmbedding hs hs₁ hq f n = intervalFourierCoefficient L (intervalPullback L f.val) n := rfl

theorem fourierEmbedding_injective {q : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hs : 0 < s) (hs₁ : s < 1 / 2) (hq : 1 / (s + 1 / 2) < q) :
    Function.Injective (fourierEmbedding (L := L) hs hs₁ hq) := coefficientMap_injective _

theorem norm_fourierEmbedding_le {q : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hs : 0 < s) (hs₁ : s < 1 / 2) (hq : 1 / (s + 1 / 2) < q)
    (f : IntrinsicIntervalSobolev s L) :
    ‖fourierEmbedding hs hs₁ hq f‖ ≤ arbitraryPeriodFourierBoundConstant L hs hs₁ hq * ‖f‖ := by
  simpa only [norm_eq_size] using! norm_intervalFourierCoefficients_le (Fact.out : 0 < L) hs hs₁ hq _
    (memLp_intervalPullback (Fact.out : 0 < L) f.val) f.energy_lt_top _

/-- Exact original-input Fourier integral after passing to its intrinsic class. -/
@[simp] theorem fourierEmbedding_ofFunction {q : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hs : 0 < s) (hs₁ : s < 1 / 2) (hq : 1 / (s + 1 / 2) < q)
    (f : ℝ → ℂ) (hf : MemLp f 2 (volume.restrict (Ioc 0 L)))
    (hE : fractionalIntervalEnergy s L f < ⊤) (n : ℤ) :
    fourierEmbedding hs hs₁ hq (ofFunction f hf hE) n = intervalFourierCoefficient L f n := by
  rw [fourierEmbedding_apply, intervalFourierCoefficient_intervalPullback (Fact.out : 0 < L)]
  exact fourierCoeff_intervalL2Class (Fact.out : 0 < L) f hf n

/-- The critical half-regularity map is continuous for every finite target `q>1`. -/
def halfFourierEmbedding {q : ℝ} [Fact (1 ≤ ENNReal.ofReal q)] (hq : 1 < q) :
    IntrinsicIntervalSobolev (1 / 2) L →L[ℂ] Coeff (ENNReal.ofReal q) :=
  (coefficientMap _ (fun f => memlp_intervalFourierCoefficient_of_half (Fact.out : 0 < L) hq _
    (memLp_intervalPullback (Fact.out : 0 < L) f.val) f.energy_lt_top)).mkContinuous
    (halfIntervalFourierLebesgueBoundConstant hq * Real.sqrt (intrinsicDilationConstant (1 / 2) (L / 2)).toReal)
    (fun f => by
      simpa only [norm_eq_size] using! norm_intervalFourierCoefficients_half_le (Fact.out : 0 < L) hq _
        (memLp_intervalPullback (Fact.out : 0 < L) f.val) f.energy_lt_top _)

@[simp] theorem halfFourierEmbedding_apply {q : ℝ} [Fact (1 ≤ ENNReal.ofReal q)] (hq : 1 < q)
    (f : IntrinsicIntervalSobolev (1 / 2) L) (n : ℤ) :
    halfFourierEmbedding hq f n = intervalFourierCoefficient L (intervalPullback L f.val) n := rfl

theorem halfFourierEmbedding_injective {q : ℝ} [Fact (1 ≤ ENNReal.ofReal q)] (hq : 1 < q) :
    Function.Injective (halfFourierEmbedding (L := L) hq) := coefficientMap_injective _

theorem norm_halfFourierEmbedding_le {q : ℝ} [Fact (1 ≤ ENNReal.ofReal q)] (hq : 1 < q)
    (f : IntrinsicIntervalSobolev (1 / 2) L) :
    ‖halfFourierEmbedding hq f‖ ≤
      (halfIntervalFourierLebesgueBoundConstant hq * Real.sqrt (intrinsicDilationConstant (1 / 2) (L / 2)).toReal) * ‖f‖ := by
  simpa only [norm_eq_size] using! norm_intervalFourierCoefficients_half_le (Fact.out : 0 < L) hq _
    (memLp_intervalPullback (Fact.out : 0 < L) f.val) f.energy_lt_top _

@[simp] theorem halfFourierEmbedding_ofFunction {q : ℝ} [Fact (1 ≤ ENNReal.ofReal q)] (hq : 1 < q)
    (f : ℝ → ℂ) (hf : MemLp f 2 (volume.restrict (Ioc 0 L)))
    (hE : fractionalIntervalEnergy (1 / 2) L f < ⊤) (n : ℤ) :
    halfFourierEmbedding hq (ofFunction f hf hE) n = intervalFourierCoefficient L f n := by
  rw [halfFourierEmbedding_apply, intervalFourierCoefficient_intervalPullback (Fact.out : 0 < L)]
  exact fourierCoeff_intervalL2Class (Fact.out : 0 < L) f hf n

end NLS.Fourier.IntrinsicIntervalSobolev
