import NLS.SequenceSpaces.OffDiagonalWeightedSums

/-! The source squared-gap weight and the output weight are independent
for zero-diagonal cubic packets. The resulting strict gain is the
smoothing input for the physical frequency derivative correction. -/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.Coeff

theorem exists_negative_weighted_offDiagonal_packet
    (A B σ t M S C R : ℝ) (horder : 1≤σ+t+(1-A))
    (hM : 0≤M) (hS : 0≤S) (hC : 0≤C)
    (hcol : ∀ k : ℤ, Summable (fun n => negativeReciprocalMatrix B σ n k))
    (hcolbound : ∀ k : ℤ, (∑' n, negativeReciprocalMatrix B σ n k)≤C)
    (g : ℤ → ℂ) (h : Coeff 1) (hnorm : ‖h‖≤R)
    (hh : ∀ k : ℤ, ‖h k‖=Weight.sobolev (1-A) k*‖g k‖^2)
    (hg : ∀ k : ℤ, Weight.sobolev t k*‖g k‖≤S)
    (F : ℤ → ℤ → ℂ) (hdiag : ∀ n, F n n=0)
    (hoff : ∀ n k, k≠n → ‖F n k‖≤M*‖g k‖^3*‖puncturedLattice 2 (by norm_num) (n-k)‖)
    (hs : ∀ n, Summable (fun k : ℤ => ‖(k : ℂ)*F n k‖)) :
    ∃ b : Coeff 1,
      (∀ n : ℤ, b n=(Weight.sobolev (-B) n : ℂ)*positiveWeightedCubicSums F n) ∧
      ‖b‖≤M*C*S*R := by
  let f₃ := fun k : ℤ => ((‖(k : ℂ)‖*‖g k‖^3/Weight.sobolev σ k : ℝ) : ℂ)
  let H : Coeff 1 := (S : ℂ) • magnitude h
  have hH (k : ℤ) : ‖f₃ k‖≤‖H k‖ := by
    change ‖((‖(k : ℂ)‖*‖g k‖^3/Weight.sobolev σ k : ℝ) : ℂ)‖≤‖(S : ℂ)*(‖h k‖ : ℂ)‖
    simp only [←Complex.ofReal_mul,Complex.norm_real,
      Real.norm_of_nonneg (mul_nonneg hS (norm_nonneg _)),
      Real.norm_of_nonneg (div_nonneg (mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) _)) ((Weight.sobolev σ).positive k).le)]
    exact negative_weighted_cubic_coeff_bound A σ t S horder g h hh hg k
  let b₃ : Coeff 1 := ⟨f₃,(lp.memℓp H).mono' hH⟩
  have hb₃ (k : ℤ) : Weight.sobolev σ k*‖b₃ k‖=‖(k : ℂ)‖*‖g k‖^3 := by
    change Weight.sobolev σ k*‖((‖(k : ℂ)‖*‖g k‖^3/Weight.sobolev σ k : ℝ) : ℂ)‖=_
    rw [Complex.norm_real,Real.norm_of_nonneg (div_nonneg (mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) _)) ((Weight.sobolev σ).positive k).le)]
    exact mul_div_cancel₀ _ ((Weight.sobolev σ).positive k).ne'
  have h₃ : ‖b₃‖≤S*‖h‖ := by
    calc
      _≤‖H‖ := lp.norm_mono (by norm_num : (1 : ℝ≥0∞)≠0) hH
      _=_ := by simp only [H,norm_smul,norm_magnitude,Complex.norm_real,Real.norm_of_nonneg hS]
  obtain ⟨a,hrows,haval,hanorm⟩ := exists_one_of_nonnegative_column_bound
    (negativeReciprocalMatrix B σ) (negativeReciprocalMatrix_nonnegative B σ) C hcol hcolbound b₃
  have han (n : ℤ) : ‖a n‖=∑' k : ℤ, negativeReciprocalMatrix B σ n k*‖b₃ k‖ := by
    rw [haval n,Complex.norm_real,Real.norm_of_nonneg (tsum_nonneg (fun k =>
      mul_nonneg (negativeReciprocalMatrix_nonnegative B σ n k) (norm_nonneg _)))]
  let Y : Coeff 1 := (M : ℂ) • magnitude a
  have hY (n : ℤ) : ‖Y n‖=M*‖a n‖ := by
    simp only [Y,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,norm_mul,magnitude_apply,
      Complex.norm_real,Real.norm_of_nonneg hM,Real.norm_of_nonneg (norm_nonneg _)]
  let f := fun n : ℤ => (Weight.sobolev (-B) n : ℂ)*positiveWeightedCubicSums F n
  have hpoint (n : ℤ) : ‖f n‖≤‖Y n‖ := by
    rw [hY,han]
    dsimp only [f,positiveWeightedCubicSums]
    by_cases hn : 0<n
    · rw [if_pos hn]
      exact negative_weighted_zeroDiagonal_row_bound B σ M hM g b₃ hb₃ n (F n)
        (hdiag n) (hoff n) (hs n) (hrows n)
    · rw [if_neg hn,mul_zero,norm_zero]
      exact mul_nonneg hM (tsum_nonneg (fun k =>
        mul_nonneg (negativeReciprocalMatrix_nonnegative B σ n k) (norm_nonneg _)))
  let b : Coeff 1 := ⟨f,(lp.memℓp Y).mono' hpoint⟩
  refine ⟨b,fun _ => rfl,?_⟩
  have hYn : ‖Y‖=M*‖a‖ := by simp only [Y,norm_smul,norm_magnitude,Complex.norm_real,Real.norm_of_nonneg hM]
  calc
    _≤‖Y‖ := lp.norm_mono (by norm_num : (1 : ℝ≥0∞)≠0) hpoint
    _=M*‖a‖ := hYn
    _≤M*(C*(S*‖h‖)) := mul_le_mul_of_nonneg_left
      (hanorm.trans (mul_le_mul_of_nonneg_left h₃ hC)) hM
    _=M*C*S*‖h‖ := by ring
    _≤_ := mul_le_mul_of_nonneg_left hnorm (by positivity)

end NLS.Coeff
