import NLS.SequenceSpaces.PositiveNeumannDomination
import NLS.SequenceSpaces.ConvolutionMajorants

/-! A summable positive convolution envelope, chosen once before every
dominated high-frequency correction operator. -/
noncomputable section
open scoped ENNReal
namespace NLS.Coeff

theorem isNonnegative_convolution (a b : Coeff 1) (ha : IsNonnegative a) (hb : IsNonnegative b) :
    IsNonnegative (convolution a b) := by
  intro j
  have he : convolution a b j = ((∑' k : ℤ, ‖a (j-k)‖*‖b k‖):ℝ) := by
    rw [convolution_apply]
    calc
      _ = ∑' k : ℤ, ((‖a (j-k)‖*‖b k‖:ℝ):ℂ) := by
        apply tsum_congr
        intro k
        rw [Complex.ofReal_mul]
        exact congrArg₂ (fun x y : ℂ => x*y) (ha (j-k)) (hb k)
      _ = _ := Complex.ofReal_tsum _ |>.symm
  rw [he, Complex.norm_real,
    Real.norm_of_nonneg (tsum_nonneg (fun k => mul_nonneg (norm_nonneg _) (norm_nonneg _)))]

def positiveConvolutionOperator (a : Coeff 1) (δ : ℝ) : Coeff 1 →L[ℂ] Coeff 1 :=
  (δ:ℂ) • convolutionCLM a

theorem positiveConvolutionOperator_apply (a : Coeff 1) (δ : ℝ) (v : Coeff 1) (j : ℤ) :
    positiveConvolutionOperator a δ v j = (δ:ℂ)*convolution a v j := rfl

theorem norm_positiveConvolutionOperator_le (a : Coeff 1) (δ : ℝ) (hδ : 0 ≤ δ) :
    ‖positiveConvolutionOperator a δ‖ ≤ δ*‖a‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hδ (norm_nonneg _))
  intro v
  change ‖(δ:ℂ) • convolution a v‖ ≤ _
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hδ]
  exact (mul_le_mul_of_nonneg_left (norm_convolution_le a v) hδ).trans_eq (mul_assoc _ _ _).symm

theorem isNonnegative_positiveConvolutionOperator (a : Coeff 1) (ha : IsNonnegative a)
    (δ : ℝ) (hδ : 0 ≤ δ) (v : Coeff 1) (hv : IsNonnegative v) :
    IsNonnegative (positiveConvolutionOperator a δ v) := by
  intro j
  rw [positiveConvolutionOperator_apply, norm_mul, Complex.norm_real, Real.norm_of_nonneg hδ,
    Complex.ofReal_mul]
  exact congrArg (fun z : ℂ => (δ:ℂ)*z) (isNonnegative_convolution a v ha hv j)

theorem norm_positiveConvolutionOperator_apply_of_nonnegative
    (a : Coeff 1) (ha : IsNonnegative a) (δ : ℝ) (hδ : 0 ≤ δ)
    (v : Coeff 1) (hv : IsNonnegative v) (j : ℤ) :
    ‖positiveConvolutionOperator a δ v j‖ = δ*(∑' k : ℤ, ‖a (j-k)‖*‖v k‖) := by
  have h := norm_magnitude_convolution_apply a v j
  rw [magnitude_eq_of_isNonnegative a ha, magnitude_eq_of_isNonnegative v hv] at h
  rw [positiveConvolutionOperator_apply, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg hδ, h]

theorem exists_convolution_neumann_envelope (a : Coeff 1) (ha : IsNonnegative a)
    (δ : ℝ) (hδ : 0 ≤ δ) (hsmall : δ*‖a‖ ≤ 1/2) :
    ∃ H : Coeff 1, ‖H‖ ≤ 2*‖a‖ ∧
      ∀ (T : Coeff ⊤ →L[ℂ] Coeff ⊤) (b g : Coeff ⊤), ‖T‖ ≤ 1/2 →
        (∀ k, ‖b k‖ ≤ ‖a k‖) →
        (∀ (f : Coeff ⊤) (v : Coeff 1), IsNonnegative v →
          (∀ k, ‖f k‖ ≤ ‖v k‖) → ∀ k, ‖T f k‖ ≤ ‖positiveConvolutionOperator a δ v k‖) →
        g-T g=b → ∀ k, ‖g k‖ ≤ ‖H k‖ :=
  exists_uniform_neumann_summable_majorant (positiveConvolutionOperator a δ)
    ((norm_positiveConvolutionOperator_le a δ hδ).trans hsmall)
    (isNonnegative_positiveConvolutionOperator a ha δ hδ) a ha

end NLS.Coeff
