import NLS.SequenceSpaces.PeriodOneMiuraFiniteRegularity
import NLS.SequenceSpaces.WeightedSingle

/-! # Quantitative fractional regularity of an L2 Miura lift

The constants depend only on the negative Sobolev exponent. The lower-order
terms are estimated in the same weighted Hilbert space as the given potential.
-/
noncomputable section
open Complex
open scoped ENNReal
namespace NLS

def negativeSobolevL2Kernel (r : ℝ) (hr : 1 < r*2) : Coeff 2 :=
  ⟨fun k => (Weight.sobolev (-r) k : ℂ), by
    have he : (fun k : ℤ => (Weight.sobolev (-r) k : ℂ)) =
        fun k => (Weight.sobolev r k : ℂ)⁻¹ := by
      funext k
      simp only [Weight.sobolev_apply,
        Real.rpow_neg (show 0 ≤ 1+|(k : ℝ)| by positivity),Complex.ofReal_inv]
    rw [he]
    exact Weight.inverse_sobolev_memlp (by norm_num) (by simpa using hr)⟩

def boundedNegativeSobolevL2 (r : ℝ) (hr : 1 < r*2) (b : Coeff ⊤) :
    WeightedCoeff (Weight.sobolev (-r)) 2 :=
  ⟨b, memlp_smul_of_bounded_vector _ _
    (lp.memℓp (negativeSobolevL2Kernel r hr)) ‖b‖
    (fun k => lp.norm_apply_le_norm (by simp) b k)⟩

theorem norm_boundedNegativeSobolevL2_le (r : ℝ) (hr : 1 < r*2) (b : Coeff ⊤) :
    ‖boundedNegativeSobolevL2 r hr b‖ ≤ ‖negativeSobolevL2Kernel r hr‖*‖b‖ := by
  have h : ‖WeightedCoeff.weightEquiv (Weight.sobolev (-r)) 2
      (boundedNegativeSobolevL2 r hr b)‖ ≤
      ‖(‖b‖ : ℂ) • negativeSobolevL2Kernel r hr‖ := by
    apply lp.norm_mono (by norm_num)
    intro k
    change ‖(Weight.sobolev (-r) k : ℂ)*b k‖ ≤
      ‖(‖b‖ : ℂ)*(Weight.sobolev (-r) k : ℂ)‖
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg b)]
    exact (mul_le_mul_of_nonneg_left
      (lp.norm_apply_le_norm (by simp) b k) (abs_nonneg _)).trans_eq (mul_comm _ _)
  simpa only [norm_smul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg b),WeightedCoeff.norm_eq,mul_comm] using h

/-- The first-order inverse gains one derivative with norm at most two. -/
theorem norm_sobolev_gain_of_mass_equation (r : ℝ)
    (u : WeightedCoeff (Weight.sobolev (1-r)) 2)
    (b : WeightedCoeff (Weight.sobolev (-r)) 2)
    (heq : ∀ k, periodOneMassSymbol 0 k*u.val k = b.val k) :
    ‖u‖ ≤ 2*‖b‖ := by
  have h : ‖WeightedCoeff.weightEquiv (Weight.sobolev (1-r)) 2 u‖ ≤
      ‖(2 : ℂ) • WeightedCoeff.weightEquiv (Weight.sobolev (-r)) 2 b‖ := by
    apply lp.norm_mono (by norm_num)
    intro k
    have hu : u.val k = (periodOneMassSymbol 0 k)⁻¹*b.val k := by
      rw [← heq k,← mul_assoc,inv_mul_cancel₀ (periodOneMassSymbol_ne_zero 0 k),one_mul]
    have hw : Weight.sobolev (1-r) k =
        Weight.sobolev (-r) k*(1+|(k : ℝ)|) := by
      simp only [Weight.sobolev_apply]
      rw [show 1-r = -r+1 by ring,
        Real.rpow_add (by positivity : (0 : ℝ) < 1+|(k : ℝ)|),Real.rpow_one]
    change ‖(Weight.sobolev (1-r) k : ℂ)*u.val k‖ ≤
      ‖(2 : ℂ)*((Weight.sobolev (-r) k : ℂ)*b.val k)‖
    rw [hu,norm_mul,norm_mul,norm_mul,norm_mul,Complex.norm_ofNat,
      Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,
      abs_of_pos ((Weight.sobolev (1-r)).positive k),
      abs_of_pos ((Weight.sobolev (-r)).positive k),hw]
    have hb := norm_periodOneMassSymbol_inv_le_bracket 0 k
    have hmul : (1+|(k : ℝ)|)*‖(periodOneMassSymbol 0 k)⁻¹‖ ≤ 2 := by
      simpa only [mul_comm] using (le_div_iff₀ (by positivity)).mp hb
    nlinarith [mul_le_mul_of_nonneg_left hmul
      (mul_nonneg (le_of_lt ((Weight.sobolev (-r)).positive k)) (norm_nonneg (b.val k)))]
  simpa only [norm_smul,Complex.norm_ofNat,WeightedCoeff.norm_eq] using h

/-- A quantitative realization of the identical raw Miura lift in H^(1-r).
The potential and the energy translation are the actual coefficients of the
Miura equation, and no regularity of the lift is assumed in advance. -/
theorem exists_periodOneMiura_sobolev_lift_bound (r : ℝ) (hr : 1 < r*2)
    (u : Coeff 2) (q : WeightedCoeff (Weight.sobolev (-r)) 2) (c : ℂ)
    (heq : ∀ k, (periodOneMiura u).val k = q.val k+(lp.single 2 0 c : Coeff 2) k) :
    ∃ U : WeightedCoeff (Weight.sobolev (1-r)) 2,
      (∀ k, U.val k = u k) ∧
      ‖U‖ ≤ 2*(‖q‖+‖c‖+‖negativeSobolevL2Kernel r hr‖*(‖u‖^2+‖u‖)) := by
  let y := Coeff.youngConvolution youngRelation_two_two_top u u
  let v := Coeff.exponentInclusion (show (2 : ℝ≥0∞) ≤ ⊤ by simp) u
  let B := q+WeightedCoeff.single (Weight.sobolev (-r)) 0 c-
    boundedNegativeSobolevL2 r hr y+boundedNegativeSobolevL2 r hr v
  have hsingle : ‖(WeightedCoeff.single (p := 2) (Weight.sobolev (-r)) 0 c)‖ = ‖c‖ := by
    simp only [WeightedCoeff.norm_single,Weight.sobolev_apply,Int.cast_zero,
      abs_zero,add_zero,Real.one_rpow,one_mul]
  have hq : Memℓp (fun k => (Weight.sobolev (-r) k : ℂ)*(periodOneMiura u).val k) 2 := by
    have hs := (q+WeightedCoeff.single (p := 2) (Weight.sobolev (-r)) 0 c).property
    change Memℓp (fun k => (Weight.sobolev (-r) k : ℂ)*
      (q+WeightedCoeff.single (p := 2) (Weight.sobolev (-r)) 0 c).val k) 2 at hs
    convert hs using 1
    funext k
    simp only [heq,WeightedCoeff.add_val,WeightedCoeff.single_val,lp.single_apply]
  let U : WeightedCoeff (Weight.sobolev (1-r)) 2 :=
    ⟨u,(periodOneMiura_memlp_iff r (by norm_num) le_rfl (by simpa using hr) u).mp hq⟩
  refine ⟨U,fun _ => rfl,?_⟩
  have hm : ∀ k, periodOneMassSymbol 0 k*U.val k = B.val k := by
    intro k
    have hh := heq k
    rw [periodOneMiura_apply] at hh
    change periodOneMassSymbol 0 k*u k =
      q.val k+(WeightedCoeff.single (p := 2) (Weight.sobolev (-r)) 0 c).val k-y k+v k
    dsimp only [y,v]
    simp only [WeightedCoeff.single_val,Coeff.youngConvolution_apply,
      Coeff.exponentInclusion_apply,lp.single_apply] at hh ⊢
    simp only [periodOneMassSymbol,Nat.cast_zero,zero_add,Complex.ofReal_one]
    linear_combination hh
  have hB : ‖B‖ ≤ ‖q‖+‖c‖+
      ‖negativeSobolevL2Kernel r hr‖*(‖u‖^2+‖u‖) := by
    have hy := norm_boundedNegativeSobolevL2_le r hr y
    have hv := norm_boundedNegativeSobolevL2_le r hr v
    have hy2 : ‖y‖ ≤ ‖u‖^2 := by
      simpa only [pow_two] using Coeff.norm_youngConvolution_le youngRelation_two_two_top u u
    have hv2 : ‖v‖ ≤ ‖u‖ := Coeff.norm_exponentInclusion_le _ u
    have ht := norm_add_le (q+WeightedCoeff.single (p := 2) (Weight.sobolev (-r)) 0 c-
      boundedNegativeSobolevL2 r hr y) (boundedNegativeSobolevL2 r hr v)
    have hs := norm_sub_le (q+WeightedCoeff.single (p := 2) (Weight.sobolev (-r)) 0 c)
      (boundedNegativeSobolevL2 r hr y)
    have ha := norm_add_le q (WeightedCoeff.single (p := 2) (Weight.sobolev (-r)) 0 c)
    rw [hsingle] at ha
    change ‖B‖ ≤ _ at ht
    nlinarith [mul_le_mul_of_nonneg_left hy2 (norm_nonneg (negativeSobolevL2Kernel r hr)),
      mul_le_mul_of_nonneg_left hv2 (norm_nonneg (negativeSobolevL2Kernel r hr))]
  exact (norm_sobolev_gain_of_mass_equation r U B hm).trans (by linarith)

end NLS
