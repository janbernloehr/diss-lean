import NLS.Fourier.PeriodicDistributionPhysicalOrderZero
import Mathlib.MeasureTheory.Measure.Complex
import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
/-! # Continuous integration against complex measures

The integral is the standard sum of four Bochner integrals against the Jordan
components of the real and imaginary signed measures. Every complex measure
has finite total variation; on the compact metrizable circle it is regular.
The continuous integral determines the actual measure uniquely and evaluates
arbitrary complex point masses with their exact weights.
-/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace NLS.Fourier
variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]

def complexMeasureControl (μ : ComplexMeasure X) : Measure X :=
  (ComplexMeasure.re μ).totalVariation + (ComplexMeasure.im μ).totalVariation

instance (μ : ComplexMeasure X) : IsFiniteMeasure (complexMeasureControl μ) :=
  inferInstanceAs (IsFiniteMeasure ((ComplexMeasure.re μ).totalVariation + (ComplexMeasure.im μ).totalVariation))

omit [TopologicalSpace X] [BorelSpace X] [CompactSpace X] in
theorem complexMeasure_variation_le (μ : ComplexMeasure X) : μ.variation ≤ complexMeasureControl μ := by
  apply VectorMeasure.variation_le_of_forall_enorm_le
  intro s _hs
  have hb : ‖μ s‖ ≤ (complexMeasureControl μ).real s := by
    rw [complexMeasureControl,measureReal_add_apply]
    exact (Complex.norm_le_abs_re_add_abs_im (μ s)).trans
      (add_le_add ((ComplexMeasure.re μ).norm_le_totalVariation s) ((ComplexMeasure.im μ).norm_le_totalVariation s))
  rw [← ofReal_norm]
  exact (ENNReal.ofReal_le_ofReal hb).trans_eq (ENNReal.ofReal_toReal (measure_ne_top _ _))

instance complexMeasure_finite_variation (μ : ComplexMeasure X) : IsFiniteMeasure μ.variation :=
  isFiniteMeasure_of_le (complexMeasureControl μ) (complexMeasure_variation_le μ)

theorem complexMeasure_variation_regular [TopologicalSpace.PseudoMetrizableSpace X] (μ : ComplexMeasure X) :
    μ.variation.Regular := by infer_instance

def finiteMeasureContinuousIntegral (μ : Measure X) [IsFiniteMeasure μ] : C(X,ℂ) →L[ℂ] ℂ :=
  let F : C(X,ℂ) →ₗ[ℂ] ℂ := {
    toFun := fun f => ∫ x, f x ∂μ
    map_add' := fun f g => integral_add
      (f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    map_smul' := fun c f => integral_smul c f }
  F.mkContinuous (μ.real univ) (by
    intro f
    exact (norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall f.norm_coe_le_norm)).trans_eq
      (mul_comm _ _))

def signedMeasureContinuousIntegral (s : SignedMeasure X) : C(X,ℂ) →L[ℂ] ℂ :=
  finiteMeasureContinuousIntegral s.toJordanDecomposition.posPart -
    finiteMeasureContinuousIntegral s.toJordanDecomposition.negPart

def complexMeasureContinuousIntegral (μ : ComplexMeasure X) : C(X,ℂ) →L[ℂ] ℂ :=
  signedMeasureContinuousIntegral (ComplexMeasure.re μ) +
    Complex.I • signedMeasureContinuousIntegral (ComplexMeasure.im μ)

/-- The standard complex integral expressed through the four finite Jordan measures. -/
theorem complexMeasureContinuousIntegral_apply (μ : ComplexMeasure X) (f : C(X,ℂ)) :
    complexMeasureContinuousIntegral μ f =
      ((∫ x, f x ∂(ComplexMeasure.re μ).toJordanDecomposition.posPart) -
        (∫ x, f x ∂(ComplexMeasure.re μ).toJordanDecomposition.negPart)) +
      Complex.I * ((∫ x, f x ∂(ComplexMeasure.im μ).toJordanDecomposition.posPart) -
        (∫ x, f x ∂(ComplexMeasure.im μ).toJordanDecomposition.negPart)) := rfl

theorem complexMeasureContinuousIntegral_const (μ : ComplexMeasure X) (c : ℂ) :
    complexMeasureContinuousIntegral μ (ContinuousMap.const X c) = c * μ univ := by
  rw [complexMeasureContinuousIntegral_apply]
  simp only [ContinuousMap.const_apply,integral_const,Complex.real_smul]
  have hr := (ComplexMeasure.re μ).apply_eq_posPart_real_sub_negPart_real MeasurableSet.univ
  have hi := (ComplexMeasure.im μ).apply_eq_posPart_real_sub_negPart_real MeasurableSet.univ
  change (μ univ).re = _ at hr
  change (μ univ).im = _ at hi
  calc
    _ = c * (((μ univ).re : ℂ) + ((μ univ).im : ℂ) * Complex.I) := by
      rw [hr,hi]
      push_cast
      ring
    _ = _ := by rw [Complex.re_add_im]

theorem signedMeasureContinuousIntegral_eq_of_rep (s : SignedMeasure X)
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hs : s = μ.toSignedMeasure - ν.toSignedMeasure) :
    signedMeasureContinuousIntegral s = finiteMeasureContinuousIntegral μ - finiteMeasureContinuousIntegral ν := by
  have hd : s.toJordanDecomposition.posPart.toSignedMeasure -
      s.toJordanDecomposition.negPart.toSignedMeasure = μ.toSignedMeasure - ν.toSignedMeasure :=
    s.toSignedMeasure_toJordanDecomposition.trans hs
  have hm : s.toJordanDecomposition.posPart + ν = μ + s.toJordanDecomposition.negPart := by
    apply Measure.toSignedMeasure_eq_toSignedMeasure_iff.mp
    simpa only [Measure.toSignedMeasure_add] using sub_eq_sub_iff_add_eq_add.mp hd
  ext f
  have hi := congrArg (fun m : Measure X => ∫ x, f x ∂m) hm
  have hint (m : Measure X) [IsFiniteMeasure m] : Integrable f m :=
    f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [integral_add_measure (hint _) (hint _),integral_add_measure (hint _) (hint _)] at hi
  change (∫ x, f x ∂s.toJordanDecomposition.posPart) - (∫ x, f x ∂s.toJordanDecomposition.negPart) =
    (∫ x, f x ∂μ) - (∫ x, f x ∂ν)
  linear_combination hi

theorem signedMeasure_eq_of_integrals_eq [T2Space X] [TopologicalSpace.PseudoMetrizableSpace X]
    (s t : SignedMeasure X)
    (h : ∀ f : C(X,ℝ),
      (∫ x, f x ∂s.toJordanDecomposition.posPart) - (∫ x, f x ∂s.toJordanDecomposition.negPart) =
      (∫ x, f x ∂t.toJordanDecomposition.posPart) - (∫ x, f x ∂t.toJordanDecomposition.negPart)) : s = t := by
  have hm : s.toJordanDecomposition.posPart + t.toJordanDecomposition.negPart =
      t.toJordanDecomposition.posPart + s.toJordanDecomposition.negPart := by
    apply Measure.ext_of_integral_eq_on_compactlySupported
    intro f
    rw [integral_add_measure f.integrable f.integrable,integral_add_measure f.integrable f.integrable]
    have hf := h f.toContinuousMap
    change (∫ x, f x ∂s.toJordanDecomposition.posPart) - (∫ x, f x ∂s.toJordanDecomposition.negPart) =
      (∫ x, f x ∂t.toJordanDecomposition.posPart) - (∫ x, f x ∂t.toJordanDecomposition.negPart) at hf
    linarith
  have hs := s.toSignedMeasure_toJordanDecomposition
  have ht := t.toSignedMeasure_toJordanDecomposition
  rw [← hs,← ht,JordanDecomposition.toSignedMeasure,JordanDecomposition.toSignedMeasure]
  apply sub_eq_sub_iff_add_eq_add.mpr
  rw [← Measure.toSignedMeasure_add,← Measure.toSignedMeasure_add]
  simp only [hm]

def realContinuousTest (f : C(X,ℝ)) : C(X,ℂ) := ⟨fun x => (f x : ℂ),by fun_prop⟩

theorem complexMeasureContinuousIntegral_realTest (μ : ComplexMeasure X) (f : C(X,ℝ)) :
    complexMeasureContinuousIntegral μ (realContinuousTest f) =
      (((∫ x, f x ∂(ComplexMeasure.re μ).toJordanDecomposition.posPart) -
        (∫ x, f x ∂(ComplexMeasure.re μ).toJordanDecomposition.negPart) : ℝ) : ℂ) +
      Complex.I * (((∫ x, f x ∂(ComplexMeasure.im μ).toJordanDecomposition.posPart) -
        (∫ x, f x ∂(ComplexMeasure.im μ).toJordanDecomposition.negPart) : ℝ) : ℂ) := by
  change ((∫ x, (f x : ℂ) ∂(ComplexMeasure.re μ).toJordanDecomposition.posPart) -
      (∫ x, (f x : ℂ) ∂(ComplexMeasure.re μ).toJordanDecomposition.negPart)) +
    Complex.I * ((∫ x, (f x : ℂ) ∂(ComplexMeasure.im μ).toJordanDecomposition.posPart) -
      (∫ x, (f x : ℂ) ∂(ComplexMeasure.im μ).toJordanDecomposition.negPart)) = _
  simp only [integral_complex_ofReal,Complex.ofReal_sub]

theorem complexMeasureContinuousIntegral_injective [T2Space X] [TopologicalSpace.PseudoMetrizableSpace X] :
    Function.Injective (complexMeasureContinuousIntegral (X := X)) := by
  intro μ ν h
  apply ComplexMeasure.equivSignedMeasure.injective
  apply Prod.ext
  · change ComplexMeasure.re μ = ComplexMeasure.re ν
    apply signedMeasure_eq_of_integrals_eq
    intro f
    have hf := congrArg (fun F : C(X,ℂ) →L[ℂ] ℂ => (F (realContinuousTest f)).re) h
    simpa only [complexMeasureContinuousIntegral_realTest,Complex.add_re,Complex.mul_re,
      Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,zero_mul,mul_zero,
      zero_sub,sub_zero,add_zero] using hf
  · change ComplexMeasure.im μ = ComplexMeasure.im ν
    apply signedMeasure_eq_of_integrals_eq
    intro f
    have hf := congrArg (fun F : C(X,ℂ) →L[ℂ] ℂ => (F (realContinuousTest f)).im) h
    simpa only [complexMeasureContinuousIntegral_realTest,Complex.add_im,Complex.mul_im,
      Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,zero_mul,mul_zero,
      one_mul,zero_add,add_zero] using hf

omit [TopologicalSpace X] [BorelSpace X] [CompactSpace X] in
theorem real_toNNReal_difference (a : ℝ) : (a.toNNReal : ℝ) - ((-a).toNNReal : ℝ) = a := by
  rcases le_total 0 a with ha | ha
  · simp [Real.coe_toNNReal',max_eq_left ha,max_eq_right (neg_nonpos.mpr ha)]
  · simp [Real.coe_toNNReal',max_eq_right ha,max_eq_left (neg_nonneg.mpr ha)]

theorem signedMeasureContinuousIntegral_dirac [T2Space X] (x : X) (a : ℝ) (f : C(X,ℂ)) :
    signedMeasureContinuousIntegral (VectorMeasure.dirac x a) f = (a:ℂ) * f x := by
  let μ : Measure X := a.toNNReal • Measure.dirac x
  let ν : Measure X := (-a).toNNReal • Measure.dirac x
  have hs : VectorMeasure.dirac x a = μ.toSignedMeasure - ν.toSignedMeasure := by
    ext s hs
    by_cases hx : x ∈ s
    · simp [μ,ν,hs,hx,Measure.real,VectorMeasure.dirac,NNReal.smul_def,smul_eq_mul]
    · simp [μ,ν,hs,hx,Measure.real,VectorMeasure.dirac]
  rw [signedMeasureContinuousIntegral_eq_of_rep _ μ ν hs]
  change (∫ y, f y ∂μ) - (∫ y, f y ∂ν) = _
  simp only [μ,ν,integral_smul_nnreal_measure,integral_dirac,NNReal.smul_def,Complex.real_smul]
  rw [← sub_mul,← Complex.ofReal_sub,real_toNNReal_difference]

theorem complexMeasureContinuousIntegral_dirac [T2Space X] (x : X) (z : ℂ) (f : C(X,ℂ)) :
    complexMeasureContinuousIntegral (VectorMeasure.dirac x z) f = z * f x := by
  have hr : ComplexMeasure.re (VectorMeasure.dirac x z) = VectorMeasure.dirac x z.re := by
    ext s hs
    change (VectorMeasure.dirac x z s).re = _
    by_cases hx : x ∈ s <;> simp [VectorMeasure.dirac,hs,hx]
  have hi : ComplexMeasure.im (VectorMeasure.dirac x z) = VectorMeasure.dirac x z.im := by
    ext s hs
    change (VectorMeasure.dirac x z s).im = _
    by_cases hx : x ∈ s <;> simp [VectorMeasure.dirac,hs,hx]
  change signedMeasureContinuousIntegral (ComplexMeasure.re _) f +
    Complex.I * signedMeasureContinuousIntegral (ComplexMeasure.im _) f = _
  rw [hr,hi,signedMeasureContinuousIntegral_dirac,signedMeasureContinuousIntegral_dirac]
  rw [← mul_assoc,← add_mul]
  congr 1
  simpa only [mul_comm] using Complex.re_add_im z

end NLS.Fourier
