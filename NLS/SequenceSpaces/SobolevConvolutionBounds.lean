import NLS.SequenceSpaces.SobolevConvolution

/-! # Bounded multiplication in the one-derivative coefficient domain

This extends the existing convolution and Leibniz identity to a bounded
bilinear map. In particular H1 is an algebra, as needed to multiply an
H-minus-one distribution by an H1 function using duality.
-/
noncomputable section
open scoped ENNReal
namespace NLS.WeightedCoeff
open NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The exact weighted norm is bounded by the physical derivative graph norm. -/
theorem norm_sobolev_le_base_add_derivative (a : WeightedCoeff (Weight.sobolev 1) p) :
    ‖a‖ ≤ ‖scalarInclusion a‖ + Real.pi⁻¹*‖derivative a‖ := by
  have hp : p ≠ 0 := ne_of_gt (zero_lt_one.trans_le Fact.out)
  let u : lp (fun _ : ℤ => ℝ) p := ⟨fun n => ‖scalarInclusion a n‖,
    (lp.memℓp (scalarInclusion a)).norm⟩
  let v : lp (fun _ : ℤ => ℝ) p := ⟨fun n => ‖derivative a n‖,
    (lp.memℓp (derivative a)).norm⟩
  have hu : ‖u‖ = ‖scalarInclusion a‖ := by
    apply le_antisymm <;> apply lp.norm_mono hp <;> intro n <;> simp [u]
  have hv : ‖v‖ = ‖derivative a‖ := by
    apply le_antisymm <;> apply lp.norm_mono hp <;> intro n <;> simp [v]
  have hw : ‖a‖ ≤ ‖u + Real.pi⁻¹ • v‖ := by
    change ‖weightEquiv (Weight.sobolev 1) p a‖ ≤ _
    apply lp.norm_mono hp
    intro n
    change ‖(Weight.sobolev 1 n:ℂ)*a.val n‖ ≤
      ‖‖scalarInclusion a n‖ + Real.pi⁻¹*‖derivative a n‖‖
    rw [Real.norm_of_nonneg (by positivity)]
    simp only [scalarInclusion_apply, derivative_apply, norm_mul, Complex.norm_I,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, one_mul,
      Weight.sobolev_apply, Real.rpow_one, abs_of_nonneg (by positivity : 0 ≤ 1+|(n:ℝ)|)]
    rw [show ‖(n:ℂ)‖ = |(n:ℝ)| by simp]
    field_simp
    nlinarith
  exact hw.trans ((norm_add_le _ _).trans_eq (by
    rw [norm_smul, Real.norm_of_nonneg (by positivity), hu, hv]))

/-- The existing regular convolution has a uniform bilinear norm bound. -/
theorem norm_sobolevConvolution_le (hp : p ≠ ⊤)
    (a b : WeightedCoeff (Weight.sobolev 1) p) :
    ‖sobolevConvolution hp a b‖ ≤
      (3*sobolevEmbeddingConstant p hp)*‖a‖*‖b‖ := by
  have hC := sobolevEmbeddingConstant_nonneg p hp
  have ha := norm_scalarInclusion_le a
  have hb := norm_scalarInclusion_le b
  have hda := norm_derivative_le a
  have hdb := norm_derivative_le b
  have hla := norm_sobolevToL1CLM_le p hp a
  have hlb := norm_sobolevToL1CLM_le p hp b
  have hbase : ‖scalarInclusion (sobolevConvolution hp a b)‖ ≤
      sobolevEmbeddingConstant p hp*‖a‖*‖b‖ := by
    rw [scalarInclusion_sobolevConvolution]
    apply (Coeff.norm_convolution_le _ _).trans
    calc
      _ ≤ ‖a‖*(sobolevEmbeddingConstant p hp*‖b‖) := by gcongr
      _ = _ := by ring
  have hder : ‖derivative (sobolevConvolution hp a b)‖ ≤
      (2*Real.pi*sobolevEmbeddingConstant p hp)*‖a‖*‖b‖ := by
    rw [derivative_sobolevConvolution]
    apply (norm_add_le _ _).trans
    apply (add_le_add (Coeff.norm_convolution_le _ _)
      (Coeff.norm_youngConvolution_le _ _ _)).trans
    calc
      _ ≤ (Real.pi*‖a‖)*(sobolevEmbeddingConstant p hp*‖b‖) +
          (sobolevEmbeddingConstant p hp*‖a‖)*(Real.pi*‖b‖) := by gcongr
      _ = _ := by ring
  apply (norm_sobolev_le_base_add_derivative _).trans
  apply (add_le_add hbase (mul_le_mul_of_nonneg_left hder (by positivity))).trans_eq
  field_simp
  ring

/-- Additivity in the first factor of the existing H1 convolution. -/
theorem sobolevConvolution_add_left (hp : p ≠ ⊤)
    (a a' b : WeightedCoeff (Weight.sobolev 1) p) :
    sobolevConvolution hp (a+a') b = sobolevConvolution hp a b + sobolevConvolution hp a' b := by
  apply scalarInclusion_injective
  simp only [scalarInclusion_sobolevConvolution, map_add, Coeff.convolution_add_left]

/-- Additivity in the second factor of the existing H1 convolution. -/
theorem sobolevConvolution_add_right (hp : p ≠ ⊤)
    (a b b' : WeightedCoeff (Weight.sobolev 1) p) :
    sobolevConvolution hp a (b+b') = sobolevConvolution hp a b + sobolevConvolution hp a b' := by
  apply scalarInclusion_injective
  simp only [scalarInclusion_sobolevConvolution, map_add, Coeff.convolution_add_right]

/-- Scalar compatibility in the first factor. -/
theorem sobolevConvolution_smul_left (hp : p ≠ ⊤) (c : ℂ)
    (a b : WeightedCoeff (Weight.sobolev 1) p) :
    sobolevConvolution hp (c • a) b = c • sobolevConvolution hp a b := by
  apply scalarInclusion_injective
  simp only [scalarInclusion_sobolevConvolution, map_smul, Coeff.convolution_smul_left]

/-- Scalar compatibility in the second factor. -/
theorem sobolevConvolution_smul_right (hp : p ≠ ⊤) (c : ℂ)
    (a b : WeightedCoeff (Weight.sobolev 1) p) :
    sobolevConvolution hp a (c • b) = c • sobolevConvolution hp a b := by
  apply scalarInclusion_injective
  simp only [scalarInclusion_sobolevConvolution, map_smul, Coeff.convolution_smul_right]

/-- Bounded multiplication in every finite one-derivative Banach space. -/
def sobolevConvolutionCLM (hp : p ≠ ⊤) :
    WeightedCoeff (Weight.sobolev 1) p →L[ℂ]
      WeightedCoeff (Weight.sobolev 1) p →L[ℂ] WeightedCoeff (Weight.sobolev 1) p :=
  (LinearMap.mk₂ ℂ (sobolevConvolution hp) (sobolevConvolution_add_left hp)
    (sobolevConvolution_smul_left hp) (sobolevConvolution_add_right hp)
    (sobolevConvolution_smul_right hp)).mkContinuous₂ (3*sobolevEmbeddingConstant p hp)
      (fun a b => by simpa only [LinearMap.mk₂_apply] using norm_sobolevConvolution_le hp a b)

@[simp] theorem sobolevConvolutionCLM_apply (hp : p ≠ ⊤)
    (a b : WeightedCoeff (Weight.sobolev 1) p) :
    sobolevConvolutionCLM hp a b = sobolevConvolution hp a b := rfl

end NLS.WeightedCoeff
