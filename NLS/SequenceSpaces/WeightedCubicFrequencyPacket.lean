import NLS.SequenceSpaces.DividedCubicFrequencyPacket

/-! Index-weighted second-moment rows form an unweighted ellr packet when
the actual squared gaps have one summable index weight. The diagonal and
the reciprocal convolution are retained before all output coordinates. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.Coeff
variable {r : ℝ≥0∞} [Fact (1 ≤ r)]

def positiveWeightedCubicSums (F : ℤ → ℤ → ℂ) (n : ℤ) : ℂ :=
  if 0<n then ∑' k : ℤ, (k : ℂ)*F n k else 0

theorem weighted_cubic_row_sum_bound (hr : 1<r) (n : ℤ)
    (g a : Coeff 2) (b : Coeff 1) (hb : ∀ k, ‖b k‖=‖(k : ℂ)‖*‖g k‖^3)
    (f : ℤ → ℂ) (D M : ℝ) (hM : 0≤M) (ha : ‖a‖≤M)
    (hdiag : ‖f n‖≤D*‖g n‖^2)
    (hoff : ∀ j, j≠n → f j=g j^3/((n-j : ℤ) : ℂ)*a j)
    (hs : Summable (fun k : ℤ => ‖(k : ℂ)*f k‖)) :
    ‖∑' k : ℤ, (k : ℂ)*f k‖≤D*‖(n : ℂ)‖*‖g n‖^2+
      M*‖convolution (magnitude (puncturedLattice r hr)) (magnitude b) n‖ := by
  let K := puncturedLattice r hr
  have hbS : Summable (fun k : ℤ => ‖b k‖) := (lp.memℓp b).norm.summable_of_one
  have hconv : Summable (fun k : ℤ => ‖K (n-k)‖*‖b k‖) := by
    apply (hbS.mul_left ‖K‖).of_nonneg_of_le (fun k => by positivity)
    intro k
    exact mul_le_mul_of_nonneg_right
      (lp.norm_apply_le_norm (zero_lt_one.trans hr).ne' K (n-k)) (norm_nonneg _)
  have hd : Summable (fun k : ℤ => if k=n then D*‖(n : ℂ)‖*‖g n‖^2 else 0) :=
    summable_of_ne_finset_zero (s := {n}) (fun k hk => if_neg (by simpa only [Finset.mem_singleton] using hk))
  have hpoint (k : ℤ) : ‖(k : ℂ)*f k‖≤
      (if k=n then D*‖(n : ℂ)‖*‖g n‖^2 else 0)+M*(‖K (n-k)‖*‖b k‖) := by
    by_cases hkn : k=n
    · subst k
      rw [norm_mul,if_pos rfl]
      calc
        _≤‖(n : ℂ)‖*(D*‖g n‖^2) := mul_le_mul_of_nonneg_left hdiag (norm_nonneg _)
        _≤_ := by nlinarith [mul_nonneg hM (mul_nonneg (norm_nonneg (K (n-n))) (norm_nonneg (b n)))]
    · have hnk : n-k≠0 := sub_ne_zero.mpr (Ne.symm hkn)
      have hak := (lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞)≠0) a k).trans ha
      rw [hoff k hkn,if_neg hkn,zero_add,hb k]
      simp only [K,puncturedLattice_apply,if_neg hnk,norm_mul,norm_div,norm_pow,norm_inv]
      calc
        _≤‖(k : ℂ)‖*(‖g k‖^3/‖((n-k : ℤ) : ℂ)‖*M) := by gcongr
        _=_ := by ring
  exact (norm_tsum_le_tsum_norm hs).trans ((hs.tsum_le_tsum hpoint (hd.add (hconv.mul_left M))).trans_eq (by
    rw [hd.tsum_add (hconv.mul_left M),tsum_ite_eq n,tsum_mul_left,←norm_magnitude_convolution_apply K b n]))

/-- A summable weighted squared-gap sequence suffices for the actual
UNDIVIDED packet, for every r>1, including infinity. -/
theorem exists_positive_weighted_cubic_packet (hr : 1<r) (g : Coeff 2) (F : ℤ → ℤ → ℂ)
    (h : Coeff 1) (R S D M : ℝ) (hS : 0≤S) (hD : 0≤D) (hM : 0≤M)
    (hh : ‖h‖≤R) (hg : ‖g‖≤S)
    (hweight : ∀ k : ℤ, ‖(k : ℂ)‖*‖g k‖^2≤‖h k‖)
    (hdiag : ∀ n, ‖F n n‖≤D*‖g n‖^2)
    (hoff : ∀ n, ∃ a : Coeff 2, ‖a‖≤M ∧ ∀ k, k≠n → F n k=g k^3/((n-k : ℤ) : ℂ)*a k)
    (hs : ∀ n, Summable (fun k : ℤ => ‖(k : ℂ)*F n k‖)) :
    ∃ b : Coeff r, (∀ n, b n=positiveWeightedCubicSums F n) ∧
      ‖b‖≤D*R+M*‖puncturedLattice r hr‖*(S*R) := by
  let f := fun k : ℤ => (((‖(k : ℂ)‖*‖g k‖^3 : ℝ) : ℂ))
  let H : Coeff 1 := (S : ℂ) • magnitude h
  have hH (k : ℤ) : ‖f k‖≤‖H k‖ := by
    change ‖((‖(k : ℂ)‖*‖g k‖^3 : ℝ) : ℂ)‖≤‖(S : ℂ)*(‖h k‖ : ℂ)‖
    simp only [←Complex.ofReal_mul,Complex.norm_real,Real.norm_of_nonneg (by positivity : 0≤S*‖h k‖),
      Real.norm_of_nonneg (by positivity : 0≤‖(k : ℂ)‖*‖g k‖^3)]
    calc
      _=(‖(k : ℂ)‖*‖g k‖^2)*‖g k‖ := by ring
      _≤‖h k‖*S := mul_le_mul (hweight k)
        ((lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞)≠0) g k).trans hg) (norm_nonneg _) (norm_nonneg _)
      _=_ := by ring
  let b3 : Coeff 1 := ⟨f,(lp.memℓp H).mono' hH⟩
  have hb3 (k : ℤ) : ‖b3 k‖=‖(k : ℂ)‖*‖g k‖^3 := by
    exact Complex.norm_of_nonneg (by positivity)
  have h3 : ‖b3‖≤S*R := by
    calc
      _≤‖H‖ := lp.norm_mono (by norm_num : (1 : ℝ≥0∞)≠0) hH
      _=S*‖h‖ := by simp only [H,norm_smul,norm_magnitude,Complex.norm_real,Real.norm_of_nonneg hS]
      _≤_ := mul_le_mul_of_nonneg_left hh hS
  let K := puncturedLattice r hr
  let C := convolution (magnitude K) (magnitude b3)
  let A : Coeff r := (D : ℂ) • exponentInclusion hr.le (magnitude h)
  let B : Coeff r := (M : ℂ) • magnitude C
  have hAn (n : ℤ) : ‖A n‖=D*‖h n‖ := by
    simp only [A,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,norm_mul,Complex.norm_real,
      Real.norm_of_nonneg hD,exponentInclusion_apply,magnitude_apply,Complex.norm_real,Real.norm_of_nonneg (norm_nonneg _)]
  have hBn (n : ℤ) : ‖B n‖=M*‖C n‖ := by
    simp only [B,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,norm_mul,Complex.norm_real,
      Real.norm_of_nonneg hM,magnitude_apply,Complex.norm_real,Real.norm_of_nonneg (norm_nonneg _)]
  have hpoint (n : ℤ) : ‖positiveWeightedCubicSums F n‖≤1*(‖A n‖+‖B n‖) := by
    rw [one_mul,hAn,hBn,positiveWeightedCubicSums]
    by_cases hn : 0<n
    · rw [if_pos hn]
      obtain ⟨a,ha,hoff⟩ := hoff n
      apply (weighted_cubic_row_sum_bound hr n g a b3 hb3 (F n) D M hM ha (hdiag n) hoff (hs n)).trans
      exact add_le_add (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hweight n) hD) le_rfl
    · rw [if_neg hn,norm_zero];positivity
  obtain ⟨hmem,hbound⟩ := memℓp_and_norm_ofFunctionOrZero_le_of_two_sequence_bound
    (positiveWeightedCubicSums F) A B 1 (by norm_num) hpoint
  refine ⟨ofFunctionOrZero r (positiveWeightedCubicSums F),ofFunctionOrZero_apply_of_mem r _ hmem,?_⟩
  have hA : ‖A‖≤D*R := by
    rw [show ‖A‖=‖(D : ℂ)‖*‖exponentInclusion hr.le (magnitude h)‖ from norm_smul _ _,
      Complex.norm_real,Real.norm_of_nonneg hD]
    exact mul_le_mul_of_nonneg_left ((norm_exponentInclusion_le hr.le _).trans (by simpa only [norm_magnitude] using hh)) hD
  have hC : ‖C‖≤‖K‖*‖b3‖ := by
    simpa only [C,norm_magnitude] using norm_convolution_le (magnitude K) (magnitude b3)
  have hB : ‖B‖≤M*‖K‖*(S*R) := by
    rw [show ‖B‖=‖(M : ℂ)‖*‖magnitude C‖ from norm_smul _ _,
      Complex.norm_real,Real.norm_of_nonneg hM,norm_magnitude]
    exact (mul_le_mul_of_nonneg_left (hC.trans (mul_le_mul_of_nonneg_left h3 (norm_nonneg K))) hM).trans_eq (by ring)
  have hhbound : ‖ofFunctionOrZero r (positiveWeightedCubicSums F)‖≤‖A‖+‖B‖ := by
    simpa only [one_mul] using hbound
  exact hhbound.trans (add_le_add hA hB)

end NLS.Coeff
