import NLS.SequenceSpaces.NegativeWeightedCubicBounds
import NLS.SequenceSpaces.NonnegativeColumnMajorant

/-! Literal index-weighted cubic moment sums form the actual weighted
ell1 packet at negative orders. Summable weighted columns and the extra
gap factor give one full-vector bound before every output index. -/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.Coeff

def negativeReciprocalMatrix (A σ : ℝ) (n k : ℤ) : ℝ :=
  Weight.sobolev (-A) n*Weight.sobolev σ k*‖puncturedLattice 2 (by norm_num) (n-k)‖

theorem negativeReciprocalMatrix_nonnegative (A σ : ℝ) (n k : ℤ) :
    0≤negativeReciprocalMatrix A σ n k :=
  mul_nonneg (mul_nonneg ((Weight.sobolev (-A)).positive n).le ((Weight.sobolev σ).positive k).le) (norm_nonneg _)

theorem negative_weighted_cubic_row_bound
    (A σ D M : ℝ) (hD : 0≤D) (hM : 0≤M) (g : ℤ → ℂ) (h b : Coeff 1)
    (hh : ∀ k : ℤ, ‖h k‖=Weight.sobolev (1-A) k*‖g k‖^2)
    (hb : ∀ k : ℤ, Weight.sobolev σ k*‖b k‖=‖(k : ℂ)‖*‖g k‖^3)
    (n : ℤ) (f : ℤ → ℂ) (hdiag : ‖f n‖≤D*‖g n‖^2)
    (hoff : ∀ k, k≠n → ‖f k‖≤M*‖g k‖^3*‖puncturedLattice 2 (by norm_num) (n-k)‖)
    (hs : Summable (fun k : ℤ => ‖(k : ℂ)*f k‖))
    (hr : Summable (fun k : ℤ => negativeReciprocalMatrix A σ n k*‖b k‖)) :
    ‖(Weight.sobolev (-A) n : ℂ)*(∑' k : ℤ, (k : ℂ)*f k)‖≤D*‖h n‖+
      M*(∑' k : ℤ, negativeReciprocalMatrix A σ n k*‖b k‖) := by
  let v := fun k : ℤ => (Weight.sobolev (-A) n : ℂ)*((k : ℂ)*f k)
  have hv : Summable (fun k : ℤ => ‖v k‖) := by
    simpa only [v,norm_mul,Complex.norm_real,Real.norm_of_nonneg ((Weight.sobolev (-A)).positive n).le] using
      hs.mul_left (Weight.sobolev (-A) n)
  have hd : Summable (fun k : ℤ => if k=n then D*‖h n‖ else 0) :=
    summable_of_ne_finset_zero (s := {n}) (fun k hk => if_neg (by simpa only [Finset.mem_singleton] using hk))
  have hpoint (k : ℤ) : ‖v k‖≤(if k=n then D*‖h n‖ else 0)+M*(negativeReciprocalMatrix A σ n k*‖b k‖) := by
    simp only [v,norm_mul,Complex.norm_real,Real.norm_of_nonneg ((Weight.sobolev (-A)).positive n).le]
    by_cases hkn : k=n
    · subst k
      rw [if_pos rfl]
      have hdb := negative_weighted_diagonal_bound A D hD g h hh n (f n) hdiag
      have hb : Weight.sobolev (-A) n*(‖(n : ℂ)‖*‖f n‖)≤D*‖h n‖ := by simpa only [mul_assoc] using hdb
      exact hb.trans
        (le_add_of_nonneg_right (mul_nonneg hM (mul_nonneg (negativeReciprocalMatrix_nonnegative A σ n n) (norm_nonneg _))))
    · rw [if_neg hkn,zero_add]
      calc
        _≤Weight.sobolev (-A) n*(‖(k : ℂ)‖*(M*‖g k‖^3*‖puncturedLattice 2 (by norm_num) (n-k)‖)) := by
          apply mul_le_mul_of_nonneg_left _ ((Weight.sobolev (-A)).positive n).le
          exact mul_le_mul_of_nonneg_left (hoff k hkn) (norm_nonneg _)
        _=M*(negativeReciprocalMatrix A σ n k*‖b k‖) := by
          dsimp only [negativeReciprocalMatrix]
          calc
            _=M*Weight.sobolev (-A) n*‖puncturedLattice 2 (by norm_num) (n-k)‖*(‖(k : ℂ)‖*‖g k‖^3) := by ring
            _=_ := by rw [←hb k];ring
  rw [←tsum_mul_left]
  exact (norm_tsum_le_tsum_norm hv).trans ((hv.tsum_le_tsum hpoint (hd.add (hr.mul_left M))).trans_eq (by
    rw [hd.tsum_add (hr.mul_left M),tsum_ite_eq n,tsum_mul_left]))

theorem exists_negative_weighted_cubic_packet
    (A σ t D M S C R : ℝ) (horder : 1≤σ+t+(1-A))
    (hD : 0≤D) (hM : 0≤M) (hS : 0≤S) (hC : 0≤C)
    (hcol : ∀ k : ℤ, Summable (fun n => negativeReciprocalMatrix A σ n k))
    (hcolbound : ∀ k : ℤ, (∑' n, negativeReciprocalMatrix A σ n k)≤C)
    (g : ℤ → ℂ) (h : Coeff 1) (hnorm : ‖h‖≤R)
    (hh : ∀ k : ℤ, ‖h k‖=Weight.sobolev (1-A) k*‖g k‖^2)
    (hg : ∀ k : ℤ, Weight.sobolev t k*‖g k‖≤S)
    (F : ℤ → ℤ → ℂ) (hdiag : ∀ n, ‖F n n‖≤D*‖g n‖^2)
    (hoff : ∀ n k, k≠n → ‖F n k‖≤M*‖g k‖^3*‖puncturedLattice 2 (by norm_num) (n-k)‖)
    (hs : ∀ n, Summable (fun k : ℤ => ‖(k : ℂ)*F n k‖)) :
    ∃ b : Coeff 1,
      (∀ n : ℤ, b n=(Weight.sobolev (-A) n : ℂ)*positiveWeightedCubicSums F n) ∧
      ‖b‖≤(D+M*C*S)*R := by
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
    (negativeReciprocalMatrix A σ) (negativeReciprocalMatrix_nonnegative A σ) C hcol hcolbound b₃
  have han (n : ℤ) : ‖a n‖=∑' k : ℤ, negativeReciprocalMatrix A σ n k*‖b₃ k‖ := by
    rw [haval n,Complex.norm_real,Real.norm_of_nonneg (tsum_nonneg (fun k =>
      mul_nonneg (negativeReciprocalMatrix_nonnegative A σ n k) (norm_nonneg _)))]
  let X : Coeff 1 := (D : ℂ) • magnitude h
  let Y : Coeff 1 := (M : ℂ) • magnitude a
  have hX (n : ℤ) : ‖X n‖=D*‖h n‖ := by
    simp only [X,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,norm_mul,magnitude_apply,
      Complex.norm_real,Real.norm_of_nonneg hD,Real.norm_of_nonneg (norm_nonneg _)]
  have hY (n : ℤ) : ‖Y n‖=M*‖a n‖ := by
    simp only [Y,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,norm_mul,magnitude_apply,
      Complex.norm_real,Real.norm_of_nonneg hM,Real.norm_of_nonneg (norm_nonneg _)]
  let f := fun n : ℤ => (Weight.sobolev (-A) n : ℂ)*positiveWeightedCubicSums F n
  have hpoint (n : ℤ) : ‖f n‖≤1*(‖X n‖+‖Y n‖) := by
    rw [one_mul,hX,hY,han]
    dsimp only [f,positiveWeightedCubicSums]
    by_cases hn : 0<n
    · rw [if_pos hn]
      exact negative_weighted_cubic_row_bound A σ D M hD hM g h b₃ hh hb₃ n (F n)
        (hdiag n) (hoff n) (hs n) (hrows n)
    · rw [if_neg hn,mul_zero,norm_zero]
      exact add_nonneg (mul_nonneg hD (norm_nonneg _)) (mul_nonneg hM (tsum_nonneg (fun k =>
        mul_nonneg (negativeReciprocalMatrix_nonnegative A σ n k) (norm_nonneg _))))
  obtain ⟨hmem,hbound⟩ := memℓp_and_norm_ofFunctionOrZero_le_of_two_sequence_bound f X Y 1 (by norm_num) hpoint
  refine ⟨ofFunctionOrZero 1 f,ofFunctionOrZero_apply_of_mem 1 f hmem,?_⟩
  have hXn : ‖X‖=D*‖h‖ := by simp only [X,norm_smul,norm_magnitude,Complex.norm_real,Real.norm_of_nonneg hD]
  have hYn : ‖Y‖=M*‖a‖ := by simp only [Y,norm_smul,norm_magnitude,Complex.norm_real,Real.norm_of_nonneg hM]
  have hb : ‖ofFunctionOrZero 1 f‖≤D*‖h‖+M*‖a‖ := by simpa only [one_mul,hXn,hYn] using hbound
  calc
    _≤D*‖h‖+M*(C*(S*‖h‖)) := hb.trans (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left (hanorm.trans (mul_le_mul_of_nonneg_left h₃ hC)) hM))
    _=(D+M*C*S)*‖h‖ := by ring
    _≤_ := mul_le_mul_of_nonneg_left hnorm (by positivity)

end NLS.Coeff
