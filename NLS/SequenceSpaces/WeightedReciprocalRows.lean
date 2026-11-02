import NLS.SequenceSpaces.RefinedTripleProduct

/-! # Summable weighted rows with a reciprocal index

A cubic ℓp sequence paired with an ℓp' row is absolutely summable.
Multiplication by the integration index only costs the selected index
plus one; the selected coordinate is included as a separate singleton.
-/
noncomputable section
set_option autoImplicit false
open scoped ENNReal
namespace NLS.Coeff

/-- The integration-index multiplier is bounded away from its deleted pole. -/
theorem norm_index_ratio_le (n k : ℤ) (hk : k ≠ n) :
    ‖(k : ℂ)/((n-k:ℤ):ℂ)‖ ≤ |(n:ℝ)|+1 := by
  have hne : n-k ≠ 0 := sub_ne_zero.mpr (Ne.symm hk)
  have hone : (1:ℝ) ≤ |((n-k:ℤ):ℝ)| := by exact_mod_cast Int.one_le_abs hne
  have htri : |(k:ℝ)| ≤ |(n:ℝ)|+|((n-k:ℤ):ℝ)| := by
    have h := abs_sub_le (n:ℝ) 0 ((n-k:ℤ):ℝ)
    push_cast at h ⊢
    simpa [abs_sub_comm] using h
  rw [norm_div,Complex.norm_intCast,Complex.norm_intCast]
  apply (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hone)).mpr
  nlinarith [abs_nonneg (n:ℝ)]

/-- A cubic sequence and its dual coefficient factor have a genuine
absolutely summable product, with the sharp Hölder bound. -/
theorem exists_cubic_dual_product
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p)
    (g : Coeff p) (a : Coeff p.conjExponent) :
    ∃ v : Coeff 1, (∀ k, v k = (g k)^3*a k) ∧ ‖v‖ ≤ ‖g‖^3*‖a‖ := by
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos (zero_lt_one.trans hp1).ne' hp
  have hpc1 : 1 < p.conjExponent :=
    (ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top
  have hpc : p.conjExponent ≠ ⊤ :=
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt p.conjExponent p).mpr hp1).ne
  have hpc0 := ENNReal.toReal_pos (zero_lt_one.trans hpc1).ne' hpc
  obtain ⟨c,hc,hnc⟩ := exists_refined_triple_product hp (zero_lt_one.trans hp1) hp
    (zero_lt_one.trans hp1) (by
      conv_rhs => rw [← ENNReal.ofReal_toReal hp]
      exact ENNReal.ofReal_le_ofReal (by linarith [ENNReal.toReal_nonneg (a := p)])) g g g
  have hc' (k : ℤ) : c k = (g k)^3 := by rw [hc k]; ring
  let v : Coeff 1 := quasiHolderProduct c a
  have hv : ‖v‖ ≤ ‖g‖^3*‖a‖ := by
    apply (norm_quasiHolderProduct_le (r := 1) hp0 hpc0 c a).trans
    exact mul_le_mul_of_nonneg_right (by simpa only [pow_succ,pow_zero,one_mul] using hnc) (lp.norm_nonneg' a)
  exact ⟨v,fun k => by simp only [v,quasiHolderProduct_apply,hc' k],hv⟩

/-- The actual weighted row has an ℓ¹ realization with a quantitative bound.
No regularity or nonvanishing is imposed on the cubic sequence. -/
theorem exists_weighted_cubic_reciprocal_row
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p)
    (g : Coeff p) (a : Coeff p.conjExponent) (n : ℤ) (u : ℤ → ℂ)
    (hu : ∀ k : ℤ, k ≠ n → u k = (g k)^3/((n-k:ℤ):ℂ)*a k) :
    ∃ b : Coeff 1, (∀ k, b k = (k:ℂ)*u k) ∧
      ‖b‖ ≤ (|(n:ℝ)|+1)*‖g‖^3*‖a‖+‖(n:ℂ)*u n‖ := by
  obtain ⟨v,hv,hvn⟩ := exists_cubic_dual_product hp hp1 g a
  let C := |(n:ℝ)|+1
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hr (k : ℤ) : ‖(k:ℂ)/((n-k:ℤ):ℂ)‖ ≤ C := by
    by_cases hk : k=n
    · subst k
      simpa only [sub_self,Int.cast_zero,div_zero,norm_zero] using hC
    · exact norm_index_ratio_le n k hk
  let d : Coeff 1 := ⟨fun k => ((k:ℂ)/((n-k:ℤ):ℂ))*v k,by
    apply ((lp.memℓp v).norm.const_mul C).mono
    intro k
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hr k) (norm_nonneg _)⟩
  have hd : ‖d‖ ≤ C*‖v‖ := by
    have hh : ‖d‖ ≤ ‖(C:ℂ) • v‖ := by
      apply lp.norm_mono (by simp : (1:ℝ≥0∞)≠0)
      intro k
      simp only [d,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,norm_mul,
        Complex.norm_real,Real.norm_of_nonneg hC]
      exact mul_le_mul_of_nonneg_right (hr k) (norm_nonneg _)
    simpa only [norm_smul,Complex.norm_real,Real.norm_of_nonneg hC] using hh
  let b := d+lp.single 1 n ((n:ℂ)*u n)
  refine ⟨b,?_,?_⟩
  · intro k
    by_cases hk : k=n
    · subst k
      simp only [b,lp.coeFn_add,Pi.add_apply,d,sub_self,Int.cast_zero,div_zero,zero_mul,
        lp.single_apply,Pi.single_eq_same,zero_add]
    · simp only [b,lp.coeFn_add,Pi.add_apply,d,lp.single_apply,Pi.single_eq_of_ne hk,add_zero,
        hv k,hu k hk]
      ring
  · apply (norm_add_le _ _).trans
    rw [lp.norm_single (by norm_num : (0:ℝ≥0∞)<1)]
    exact add_le_add (hd.trans (by
      calc
        C*‖v‖ ≤ C*(‖g‖^3*‖a‖) := mul_le_mul_of_nonneg_left hvn hC
        _ = (|(n:ℝ)|+1)*‖g‖^3*‖a‖ := by dsimp only [C]; ring)) le_rfl

/-- Weighting a reciprocal row differs from multiplying its sum by the
selected index by a uniformly bounded absolutely convergent cubic sum. -/
theorem norm_weighted_tsum_sub_index_tsum_le
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p)
    (g : Coeff p) (a : Coeff p.conjExponent) (n : ℤ) (u : ℤ → ℂ)
    (han : a n = 0)
    (hu : ∀ k : ℤ, k ≠ n → u k = (g k)^3/((n-k:ℤ):ℂ)*a k)
    (hs : Summable u) (hw : Summable (fun k : ℤ => (k:ℂ)*u k)) :
    ‖(∑' k : ℤ, (k:ℂ)*u k)-(n:ℂ)*(∑' k : ℤ, u k)‖ ≤ ‖g‖^3*‖a‖ := by
  obtain ⟨v,hv,hvn⟩ := exists_cubic_dual_product hp hp1 g a
  have he (k : ℤ) : (k:ℂ)*u k-(n:ℂ)*u k = -v k := by
    rw [hv k]
    by_cases hk : k=n
    · subst k
      rw [sub_self,han,mul_zero,neg_zero]
    · have hnk : ((n-k:ℤ):ℂ) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr (Ne.symm hk)
      rw [hu k hk]
      push_cast
      push_cast at hnk
      field_simp [hnk]
      ring
  have hid : (∑' k : ℤ, (k:ℂ)*u k)-(n:ℂ)*(∑' k : ℤ, u k) = -(∑' k : ℤ, v k) := by
    rw [← tsum_mul_left,← hw.tsum_sub (hs.mul_left (n:ℂ))]
    simp only [he,tsum_neg]
  rw [hid,norm_neg]
  exact (lp.norm_tsum_le v).trans hvn

end NLS.Coeff
