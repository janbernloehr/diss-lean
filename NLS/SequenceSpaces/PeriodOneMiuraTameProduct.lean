import NLS.SequenceSpaces.PeriodOneMiuraQuadratic
import NLS.SequenceSpaces.TameSpectralConvolution
import NLS.SequenceSpaces.ConvolutionMajorants
import NLS.SequenceSpaces.BoundedScalarProducts
import NLS.SequenceSpaces.SobolevHomogeneous

/-! # Tame Miura multiplication on every nonnegative Sobolev order

The literal two-L2 convolution has a bounded weighted row at every
nonnegative order. The inverse bracket gives one derivative of loss,
including negative target orders, with an actual native Hilbert norm bound.
-/

noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal
namespace NLS

/-- A tame weighted bound for every coefficient of the actual distributional product. -/
theorem weighted_miura_product_uniform_bound
    (t : ℝ) (ht : 0 ≤ t) (u v : Coeff 2)
    (hu : Memℓp (fun j => (Weight.sobolev t j : ℂ)*u j) 2)
    (hv : Memℓp (fun j => (Weight.sobolev t j : ℂ)*v j) 2) (k : ℤ) :
    Weight.sobolev t k*‖(periodOneMiuraProduct u v).val k‖ ≤
      (2 : ℝ)^t*(‖(⟨_,hu⟩ : Coeff 2)‖*‖v‖+‖u‖*‖(⟨_,hv⟩ : Coeff 2)‖) := by
  let U : Coeff 2 := ⟨_,hu⟩
  let V : Coeff 2 := ⟨_,hv⟩
  have hU (j : ℤ) : ‖U j‖=Weight.sobolev t j*‖u j‖ := by
    change ‖(Weight.sobolev t j : ℂ)*u j‖=_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Weight.positive _ j)]
  have hV (j : ℤ) : ‖V j‖=Weight.sobolev t j*‖v j‖ := by
    change ‖(Weight.sobolev t j : ℂ)*v j‖=_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Weight.positive _ j)]
  have hsu : Summable (fun j => ‖U (k-j)‖*‖v j‖) := by
    simpa only [norm_mul] using Coeff.summable_norm_youngConvolution_terms youngRelation_two_two_top U v k
  have hsv : Summable (fun j => ‖u (k-j)‖*‖V j‖) := by
    simpa only [norm_mul] using Coeff.summable_norm_youngConvolution_terms youngRelation_two_two_top u V k
  have hs : Summable (fun j => ‖u (k-j)‖*‖v j‖) := by
    simpa only [norm_mul] using Coeff.summable_norm_youngConvolution_terms youngRelation_two_two_top u v k
  have hsumU : (∑' j : ℤ, ‖U (k-j)‖*‖v j‖) ≤ ‖U‖*‖v‖ := by
    rw [← Coeff.norm_magnitude_youngConvolution_apply youngRelation_two_two_top U v k]
    exact (lp.norm_apply_le_norm (by simp : (⊤ : ℝ≥0∞)≠0) _ k).trans
      (Coeff.norm_magnitude_youngConvolution_le youngRelation_two_two_top U v)
  have hsumV : (∑' j : ℤ, ‖u (k-j)‖*‖V j‖) ≤ ‖u‖*‖V‖ := by
    rw [← Coeff.norm_magnitude_youngConvolution_apply youngRelation_two_two_top u V k]
    exact (lp.norm_apply_le_norm (by simp : (⊤ : ℝ≥0∞)≠0) _ k).trans
      (Coeff.norm_magnitude_youngConvolution_le youngRelation_two_two_top u V)
  calc
    _ ≤ Weight.sobolev t k*(∑' j : ℤ, ‖u (k-j)‖*‖v j‖) := by
      rw [periodOneMiuraProduct_apply]
      exact mul_le_mul_of_nonneg_left
        (by simpa only [norm_mul] using
          (norm_tsum_le_tsum_norm
            (Coeff.summable_norm_youngConvolution_terms youngRelation_two_two_top u v k)))
        (Weight.positive _ k).le
    _ = ∑' j : ℤ, Weight.sobolev t k*(‖u (k-j)‖*‖v j‖) := (tsum_mul_left).symm
    _ ≤ ∑' j : ℤ, (2 : ℝ)^t*(‖U (k-j)‖*‖v j‖+‖u (k-j)‖*‖V j‖) := by
      apply (hs.mul_left _).tsum_le_tsum _ ((hsu.add hsv).mul_left _)
      intro j
      have hw := SpectralWeight.sobolev_add_le t ht (k-j) j
      simp only [sub_add_cancel, SpectralWeight.sobolev_apply] at hw
      rw [hU,hV]
      nlinarith [mul_le_mul_of_nonneg_right hw (mul_nonneg (norm_nonneg (u (k-j))) (norm_nonneg (v j)))]
    _ = (2 : ℝ)^t*((∑' j : ℤ, ‖U (k-j)‖*‖v j‖)+(∑' j : ℤ, ‖u (k-j)‖*‖V j‖)) := by
      rw [tsum_mul_left, hsu.tsum_add hsv]
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add hsumU hsumV) (by positivity)

/-- The exact one-derivative weight loss is the original inverse bracket. -/
theorem sobolev_sub_one_eq_inverseBracket_mul (t : ℝ) (n : ℤ) :
    (Weight.sobolev (t-1) n : ℂ)=inverseBracketCoefficients n*(Weight.sobolev t n : ℂ) := by
  change (Weight.sobolev (t-1) n : ℂ)=(Weight.sobolev 1 n : ℂ)⁻¹*(Weight.sobolev t n : ℂ)
  simp only [Weight.sobolev_apply, Real.rpow_one]
  rw [show t-1=(-1)+t by ring, Real.rpow_add (by positivity), Real.rpow_neg_one,
    Complex.ofReal_mul, Complex.ofReal_inv]

/-- Fractional derivative loss is the literal reciprocal Sobolev weight. -/
theorem sobolev_sub_eq_inverse_sobolev_mul (t d : ℝ) (n : ℤ) :
    (Weight.sobolev (t-d) n : ℂ)=(Weight.sobolev d n : ℂ)⁻¹*(Weight.sobolev t n : ℂ) := by
  simp only [Weight.sobolev_apply]
  rw [show t-d=(-d)+t by ring, Real.rpow_add (by positivity), Real.rpow_neg (by positivity),
    Complex.ofReal_mul, Complex.ofReal_inv]

/-- Every loss strictly greater than one half suffices for the actual
H^t times H^t distributional product, at every nonnegative input order. -/
theorem periodOneMiuraProduct_mem_sobolev_sub
    (t : ℝ) (ht : 0 ≤ t) (d : ℝ) (hd : 1/2 < d) (u v : Coeff 2)
    (hu : Memℓp (fun j => (Weight.sobolev t j : ℂ)*u j) 2)
    (hv : Memℓp (fun j => (Weight.sobolev t j : ℂ)*v j) 2) :
    Memℓp (fun j => (Weight.sobolev (t-d) j : ℂ)*(periodOneMiuraProduct u v).val j) 2 := by
  have hi : Memℓp (fun n : ℤ => (Weight.sobolev d n : ℂ)⁻¹) 2 :=
    Weight.inverse_sobolev_memlp (by norm_num) (by norm_num; linarith)
  have hf := memlp_smul_of_bounded_vector (fun n => (Weight.sobolev d n : ℂ)⁻¹)
    (fun n => (Weight.sobolev t n : ℂ)*(periodOneMiuraProduct u v).val n) hi
    ((2 : ℝ)^t*(‖(⟨_,hu⟩ : Coeff 2)‖*‖v‖+‖u‖*‖(⟨_,hv⟩ : Coeff 2)‖)) (by
      intro n
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Weight.positive _ n)]
      exact weighted_miura_product_uniform_bound t ht u v hu hv n)
  convert hf using 1
  funext n
  rw [sobolev_sub_eq_inverse_sobolev_mul, mul_assoc]
  rfl

/-- Two H^t lifts have an actual H^(t-1) distributional product, for every t>=0. -/
theorem periodOneMiuraProduct_mem_sobolev_sub_one
    (t : ℝ) (ht : 0 ≤ t) (u v : Coeff 2)
    (hu : Memℓp (fun j => (Weight.sobolev t j : ℂ)*u j) 2)
    (hv : Memℓp (fun j => (Weight.sobolev t j : ℂ)*v j) 2) :
    Memℓp (fun j => (Weight.sobolev (t-1) j : ℂ)*(periodOneMiuraProduct u v).val j) 2 := by
  have hf := memlp_smul_of_bounded_vector (fun n => inverseBracketCoefficients n)
    (fun n => (Weight.sobolev t n : ℂ)*(periodOneMiuraProduct u v).val n)
    (lp.memℓp inverseBracketCoefficients)
    ((2 : ℝ)^t*(‖(⟨_,hu⟩ : Coeff 2)‖*‖v‖+‖u‖*‖(⟨_,hv⟩ : Coeff 2)‖)) (by
      intro n
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Weight.positive _ n)]
      exact weighted_miura_product_uniform_bound t ht u v hu hv n)
  convert hf using 1
  funext n
  rw [sobolev_sub_one_eq_inverseBracket_mul, mul_assoc]
  rfl

/-- The literal product as a native weighted Hilbert element. -/
def periodOneSobolevMiuraProduct (t : ℝ) (ht : 0 ≤ t)
    (a b : WeightedCoeff (Weight.sobolev t) 2) : WeightedCoeff (Weight.sobolev (t-1)) 2 :=
  ⟨(periodOneMiuraProduct (WeightedCoeff.sobolevToL2 ht a) (WeightedCoeff.sobolevToL2 ht b)).val,
    periodOneMiuraProduct_mem_sobolev_sub_one t ht _ _
      (by simpa only [WeightedCoeff.sobolevToL2_apply] using
        (show Memℓp (fun j => (Weight.sobolev t j : ℂ)*a.val j) 2 from a.property))
      (by simpa only [WeightedCoeff.sobolevToL2_apply] using
        (show Memℓp (fun j => (Weight.sobolev t j : ℂ)*b.val j) 2 from b.property))⟩

@[simp] theorem periodOneSobolevMiuraProduct_apply (t : ℝ) (ht : 0 ≤ t)
    (a b : WeightedCoeff (Weight.sobolev t) 2) (n : ℤ) :
    (periodOneSobolevMiuraProduct t ht a b).val n=∑' j : ℤ, a.val (n-j)*b.val j := by
  simp only [periodOneSobolevMiuraProduct, periodOneMiuraProduct_apply,
    WeightedCoeff.sobolevToL2_apply]

/-- A genuine native Hilbert norm bound, uniform in every Fourier mode. -/
theorem norm_periodOneSobolevMiuraProduct_le (t : ℝ) (ht : 0 ≤ t)
    (a b : WeightedCoeff (Weight.sobolev t) 2) :
    ‖periodOneSobolevMiuraProduct t ht a b‖ ≤
      (2*(2 : ℝ)^t*‖inverseBracketCoefficients‖)*‖a‖*‖b‖ := by
  let u := WeightedCoeff.sobolevToL2 ht a
  let v := WeightedCoeff.sobolevToL2 ht b
  let C : ℝ := 2*(2 : ℝ)^t*‖a‖*‖b‖
  have hC : 0 ≤ C := by positivity
  have hu : Memℓp (fun j => (Weight.sobolev t j : ℂ)*u j) 2 := by
    simpa only [u, WeightedCoeff.sobolevToL2_apply] using
        (show Memℓp (fun j => (Weight.sobolev t j : ℂ)*a.val j) 2 from a.property)
  have hv : Memℓp (fun j => (Weight.sobolev t j : ℂ)*v j) 2 := by
    simpa only [v, WeightedCoeff.sobolevToL2_apply] using
        (show Memℓp (fun j => (Weight.sobolev t j : ℂ)*b.val j) 2 from b.property)
  have hU : (⟨_,hu⟩ : Coeff 2)=WeightedCoeff.weightEquiv (Weight.sobolev t) 2 a := by
    ext n
    exact congrArg (fun z : ℂ => (Weight.sobolev t n : ℂ)*z)
      (WeightedCoeff.sobolevToL2_apply ht a n)
  have hV : (⟨_,hv⟩ : Coeff 2)=WeightedCoeff.weightEquiv (Weight.sobolev t) 2 b := by
    ext n
    exact congrArg (fun z : ℂ => (Weight.sobolev t n : ℂ)*z)
      (WeightedCoeff.sobolevToL2_apply ht b n)
  have hf (n : ℤ) : ‖(Weight.sobolev t n : ℂ)*(periodOneMiuraProduct u v).val n‖ ≤ C := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Weight.positive _ n)]
    have hh := weighted_miura_product_uniform_bound t ht u v hu hv n
    rw [hU,hV] at hh
    change Weight.sobolev t n*‖(periodOneMiuraProduct u v).val n‖ ≤ C
    have hau : ‖u‖ ≤ ‖a‖ := WeightedCoeff.norm_sobolevToL2_le ht a
    have hbv : ‖v‖ ≤ ‖b‖ := WeightedCoeff.norm_sobolevToL2_le ht b
    exact hh.trans (by
      change (2 : ℝ)^t*(‖a‖*‖v‖+‖u‖*‖b‖) ≤ C
      dsimp only [C]
      nlinarith [mul_le_mul_of_nonneg_left hbv (norm_nonneg a),
        mul_le_mul_of_nonneg_right hau (norm_nonneg b),
        Real.rpow_pos_of_pos (by norm_num : (0 : ℝ)<2) t])
  have hn : ‖WeightedCoeff.weightEquiv (Weight.sobolev (t-1)) 2
      (periodOneSobolevMiuraProduct t ht a b)‖ ≤ ‖(C : ℂ) • inverseBracketCoefficients‖ := by
    apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞)≠0)
    intro n
    change ‖(Weight.sobolev (t-1) n : ℂ)*(periodOneMiuraProduct u v).val n‖ ≤
      ‖(C : ℂ)*inverseBracketCoefficients n‖
    rw [sobolev_sub_one_eq_inverseBracket_mul, mul_assoc, norm_mul]
    calc
      _ ≤ ‖inverseBracketCoefficients n‖*C :=
        mul_le_mul_of_nonneg_left (hf n) (norm_nonneg _)
      _ = ‖(C : ℂ)*inverseBracketCoefficients n‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC]
        ring
  calc
    _ ≤ ‖(C : ℂ) • inverseBracketCoefficients‖ := hn
    _ = C*‖inverseBracketCoefficients‖ := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC]
    _ = _ := by dsimp only [C]; ring

end NLS
