import NLS.SequenceSpaces.PeriodOneSobolevMiuraMap

/-! # Bounded Miura multiplication with fractional loss

Every loss d>1/2 gives a continuous bilinear product H^t times H^t
into H^(t-d), in the original weighted Hilbert norms.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS

def inverseSobolevCoefficients (d : ℝ) (hd : 1/2<d) : Coeff 2 :=
  ⟨fun n => (Weight.sobolev d n : ℂ)⁻¹,
    Weight.inverse_sobolev_memlp (by norm_num) (by norm_num;linarith)⟩

/-- The literal product as a native weighted Hilbert element. -/
def periodOneFractionalMiuraProduct (t : ℝ) (ht : 0 ≤ t) (d : ℝ) (hd : 1/2 < d)
    (a b : WeightedCoeff (Weight.sobolev t) 2) : WeightedCoeff (Weight.sobolev (t-d)) 2 :=
  ⟨(periodOneMiuraProduct (WeightedCoeff.sobolevToL2 ht a) (WeightedCoeff.sobolevToL2 ht b)).val,
    periodOneMiuraProduct_mem_sobolev_sub t ht d hd _ _
      (by simpa only [WeightedCoeff.sobolevToL2_apply] using
        (show Memℓp (fun j => (Weight.sobolev t j : ℂ)*a.val j) 2 from a.property))
      (by simpa only [WeightedCoeff.sobolevToL2_apply] using
        (show Memℓp (fun j => (Weight.sobolev t j : ℂ)*b.val j) 2 from b.property))⟩

@[simp] theorem periodOneFractionalMiuraProduct_apply (t : ℝ) (ht : 0 ≤ t) (d : ℝ) (hd : 1/2 < d)
    (a b : WeightedCoeff (Weight.sobolev t) 2) (n : ℤ) :
    (periodOneFractionalMiuraProduct t ht d hd a b).val n=∑' j : ℤ, a.val (n-j)*b.val j := by
  simp only [periodOneFractionalMiuraProduct, periodOneMiuraProduct_apply,
    WeightedCoeff.sobolevToL2_apply]

/-- A genuine native Hilbert norm bound, uniform in every Fourier mode. -/
theorem norm_periodOneFractionalMiuraProduct_le (t : ℝ) (ht : 0 ≤ t) (d : ℝ) (hd : 1/2 < d)
    (a b : WeightedCoeff (Weight.sobolev t) 2) :
    ‖periodOneFractionalMiuraProduct t ht d hd a b‖ ≤
      (2*(2 : ℝ)^t*‖inverseSobolevCoefficients d hd‖)*‖a‖*‖b‖ := by
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
  have hn : ‖WeightedCoeff.weightEquiv (Weight.sobolev (t-d)) 2
      (periodOneFractionalMiuraProduct t ht d hd a b)‖ ≤ ‖(C : ℂ) • inverseSobolevCoefficients d hd‖ := by
    apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞)≠0)
    intro n
    change ‖(Weight.sobolev (t-d) n : ℂ)*(periodOneMiuraProduct u v).val n‖ ≤
      ‖(C : ℂ)*(inverseSobolevCoefficients d hd) n‖
    rw [sobolev_sub_eq_inverse_sobolev_mul, mul_assoc, norm_mul]
    calc
      _ ≤ ‖(inverseSobolevCoefficients d hd) n‖*C :=
        mul_le_mul_of_nonneg_left (hf n) (norm_nonneg _)
      _ = ‖(C : ℂ)*(inverseSobolevCoefficients d hd) n‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC]
        ring
  calc
    _ ≤ ‖(C : ℂ) • inverseSobolevCoefficients d hd‖ := hn
    _ = C*‖inverseSobolevCoefficients d hd‖ := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC]
    _ = _ := by dsimp only [C]; ring


/-- Actual Sobolev multiplication as a bounded complex bilinear map. -/
def periodOneFractionalMiuraProductCLM (t : ℝ) (ht : 0 ≤ t) (d : ℝ) (hd : 1/2 < d) :
    WeightedCoeff (Weight.sobolev t) 2 →L[ℂ]
      WeightedCoeff (Weight.sobolev t) 2 →L[ℂ] WeightedCoeff (Weight.sobolev (t-d)) 2 :=
  (LinearMap.mk₂ ℂ (periodOneFractionalMiuraProduct t ht d hd)
    (by
      intro a a' b
      apply Subtype.ext
      funext n
      change (periodOneMiuraProduct (WeightedCoeff.sobolevToL2 ht (a+a'))
        (WeightedCoeff.sobolevToL2 ht b)).val n=_
      simp only [map_add,_root_.add_apply,periodOneFractionalMiuraProduct,WeightedCoeff.add_val]; rfl)
    (by
      intro c a b
      apply Subtype.ext
      funext n
      change (periodOneMiuraProduct (WeightedCoeff.sobolevToL2 ht (c • a))
        (WeightedCoeff.sobolevToL2 ht b)).val n=_
      simp only [map_smul,_root_.smul_apply,periodOneFractionalMiuraProduct,
        WeightedCoeff.smul_val]; rfl)
    (by
      intro a b b'
      apply Subtype.ext
      funext n
      change (periodOneMiuraProduct (WeightedCoeff.sobolevToL2 ht a)
        (WeightedCoeff.sobolevToL2 ht (b+b'))).val n=_
      simp only [map_add,periodOneFractionalMiuraProduct,WeightedCoeff.add_val]; rfl)
    (by
      intro c a b
      apply Subtype.ext
      funext n
      change (periodOneMiuraProduct (WeightedCoeff.sobolevToL2 ht a)
        (WeightedCoeff.sobolevToL2 ht (c • b))).val n=_
      simp only [map_smul,periodOneFractionalMiuraProduct,WeightedCoeff.smul_val]; rfl)).mkContinuous₂
    (2*(2 : ℝ)^t*‖inverseSobolevCoefficients d hd‖)
    (fun a b => norm_periodOneFractionalMiuraProduct_le t ht d hd a b)

@[simp] theorem periodOneFractionalMiuraProductCLM_apply (t : ℝ) (ht : 0 ≤ t) (d : ℝ) (hd : 1/2 < d)
    (a b : WeightedCoeff (Weight.sobolev t) 2) :
    periodOneFractionalMiuraProductCLM t ht d hd a b=periodOneFractionalMiuraProduct t ht d hd a b := rfl

end NLS
