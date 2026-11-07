import NLS.SequenceSpaces.PositiveSquaredGapMomentSummability

/-! A quantitative absolute-row bound: the finite low block plus
three times the squared full-l2 gap norm controls the weighted series. -/
noncomputable section
open Set
open scoped ENNReal Classical
namespace NLS.Coeff

theorem positive_weighted_signed_reciprocal_le_three (n m : ℕ+)
    (hm : 2*(n:ℕ) < (m:ℕ)) :
    ((m:ℕ):ℝ)*(1/|((n:ℕ):ℝ)-(m:ℕ)|+1/((n:ℕ)+(m:ℕ):ℝ)) ≤ 3 := by
  have hnr : 0 < ((n:ℕ):ℝ) := by exact_mod_cast n.pos
  have hmr : 2*((n:ℕ):ℝ) < ((m:ℕ):ℝ) := by exact_mod_cast hm
  rw [abs_of_neg (by linarith : ((n:ℕ):ℝ)-(m:ℕ)<0),neg_sub,mul_add,
    mul_one_div,mul_one_div]
  have h₁ : ((m:ℕ):ℝ)/(((m:ℕ):ℝ)-(n:ℕ)) ≤ 2 :=
    (div_le_iff₀ (by linarith)).mpr (by linarith)
  have h₂ : ((m:ℕ):ℝ)/(((n:ℕ):ℝ)+(m:ℕ)) ≤ 1 :=
    (div_le_iff₀ (by linarith)).mpr (by linarith)
  linarith

theorem sum_norm_positive_weighted_le_of_squared_gap_tail
    (a : Coeff 2) (n : ℕ+) (u : ℕ+ → ℂ) (K : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hu : ∀ m : ℕ+, K < (m:ℕ) → m ≠ n → ‖u m‖ ≤
      C*‖a ((m:ℕ):ℤ)‖^2*
        (1/|((n:ℕ):ℝ)-(m:ℕ)|+1/((n:ℕ)+(m:ℕ):ℝ)))
    (s : Finset ℕ+) (hs : ∀ m : ℕ+, (m:ℕ) ≤ max K (2*(n:ℕ)) → m ∈ s) :
    (∑' m : ℕ+, ‖((m:ℕ):ℂ)*u m‖) ≤
      (∑ m ∈ s, ‖((m:ℕ):ℂ)*u m‖)+3*C*‖a‖^2 := by
  have hsum := summable_norm_positive_weighted_of_squared_gap_tail a n u K C hC hu
  have hc : (2:ℝ≥0∞).toReal.HolderConjugate (2:ℝ≥0∞).toReal := Real.HolderConjugate.two_two
  have hgZ : Summable (fun k : ℤ => ‖a k‖^2) := by
    simpa only [pow_two] using (lp.tsum_mul_le_mul_norm hc a a).1
  have hinj : Function.Injective (fun m : ℕ+ => ((m:ℕ):ℤ)) := by
    intro i j h
    apply PNat.coe_injective
    exact Int.ofNat.inj h
  have hg : Summable (fun m : ℕ+ => ‖a ((m:ℕ):ℤ)‖^2) := hgZ.comp_injective hinj
  have hgB : (∑' m : ℕ+, ‖a ((m:ℕ):ℤ)‖^2) ≤ ‖a‖^2 := by
    have he : (∑' k : ℤ, ‖a k‖^2)=‖a‖^2 := by
      simpa using (lp.norm_rpow_eq_tsum (by norm_num : 0 < (2:ℝ≥0∞).toReal) a).symm
    rw [← he]
    exact tsum_comp_le_tsum_of_inj hgZ (fun _ => sq_nonneg _) hinj
  let H : ℕ+ → ℝ := fun m => if m ∈ s then ‖((m:ℕ):ℂ)*u m‖ else 0
  have hH : Summable H := summable_of_ne_finset_zero (s := s) (by intro m hm; simp [H,hm])
  have hpoint (m : ℕ+) : ‖((m:ℕ):ℂ)*u m‖ ≤ H m+(3*C)*‖a ((m:ℕ):ℤ)‖^2 := by
    by_cases hm : m ∈ s
    · simp only [H,if_pos hm]
      exact le_add_of_nonneg_right (by positivity)
    · have hmL : max K (2*(n:ℕ)) < (m:ℕ) := lt_of_not_ge (fun h => hm (hs m h))
      have hmK : K < (m:ℕ) := (le_max_left _ _).trans_lt hmL
      have hm2 : 2*(n:ℕ) < (m:ℕ) := (le_max_right _ _).trans_lt hmL
      have hmn : m ≠ n := by intro he; subst m; have := n.pos; omega
      simp only [H,if_neg hm,zero_add,norm_mul,Complex.norm_natCast]
      calc
        _ ≤ ((m:ℕ):ℝ)*(C*‖a ((m:ℕ):ℤ)‖^2*
            (1/|((n:ℕ):ℝ)-(m:ℕ)|+1/((n:ℕ)+(m:ℕ):ℝ))) :=
          mul_le_mul_of_nonneg_left (hu m hmK hmn) (by positivity)
        _ = (C*‖a ((m:ℕ):ℤ)‖^2)*
            (((m:ℕ):ℝ)*(1/|((n:ℕ):ℝ)-(m:ℕ)|+1/((n:ℕ)+(m:ℕ):ℝ))) := by ring
        _ ≤ (C*‖a ((m:ℕ):ℤ)‖^2)*3 :=
          mul_le_mul_of_nonneg_left (positive_weighted_signed_reciprocal_le_three n m hm2) (by positivity)
        _ = _ := by ring
  have hHB : (∑' m, H m)=∑ m ∈ s, ‖((m:ℕ):ℂ)*u m‖ := by
    rw [tsum_eq_sum (s := s) (by intro m hm; simp [H,hm])]
    exact Finset.sum_congr rfl (fun m hm => by simp only [H,if_pos hm])
  calc
    _ ≤ ∑' m, (H m+(3*C)*‖a ((m:ℕ):ℤ)‖^2) := hsum.tsum_le_tsum hpoint (hH.add (hg.mul_left (3*C)))
    _ = (∑ m ∈ s, ‖((m:ℕ):ℂ)*u m‖)+(3*C)*(∑' m : ℕ+, ‖a ((m:ℕ):ℤ)‖^2) := by
      rw [hH.tsum_add (hg.mul_left (3*C)),hHB,tsum_mul_left]
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hgB (by positivity : 0 ≤ 3*C))

end NLS.Coeff
