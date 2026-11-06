import NLS.SequenceSpaces.DividedCubicRowBounds
import NLS.SequenceSpaces.TwoSequenceBound
import NLS.SequenceSpaces.ExponentEmbedding

/-! A full ellr packet of literal weighted cubic row sums divided by their
own index. A genuine ell1 cubic gap sequence and a reciprocal convolution
majorant establish membership and one norm bound before all coordinates. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.Coeff
variable {r : ℝ≥0∞} [Fact (1 ≤ r)]

def positiveDividedCubicSums (F : ℤ → ℤ → ℂ) (n : ℤ) : ℂ :=
  if 0<n then (∑' k : ℤ, (k : ℂ)*F n k)/(n : ℂ) else 0

theorem exists_positive_divided_cubic_packet (hr : 1<r) (g : Coeff 2) (F : ℤ → ℤ → ℂ)
    (R D M : ℝ) (hR : 0≤R) (hD : 0≤D) (hM : 0≤M) (hg : ‖g‖≤R)
    (hdiag : ∀ n, ‖F n n‖≤D*‖g n‖^2)
    (hoff : ∀ n, ∃ a : Coeff 2, ‖a‖≤M ∧ ∀ k, k≠n → F n k=g k^3/((n-k : ℤ) : ℂ)*a k)
    (hs : ∀ n, Summable (fun k : ℤ => ‖(k : ℂ)*F n k‖)) :
    ∃ b : Coeff r, (∀ n, b n=positiveDividedCubicSums F n) ∧
      ‖b‖≤D*R^2+2*M*‖puncturedLattice r hr‖*R^3 := by
  obtain ⟨b2,hb2,hb2norm⟩ := exists_one_of_hilbert_quadratic_majorant g
    (fun n => ((‖g n‖^2 : ℝ) : ℂ)) 1 (by intro n;rw [Complex.norm_real,Real.norm_of_nonneg (sq_nonneg _),one_mul])
  have hb2n (n : ℤ) : ‖b2 n‖=‖g n‖^2 := by rw [hb2 n,Complex.norm_real,Real.norm_of_nonneg (sq_nonneg _)]
  obtain ⟨b3,hb3,hb3norm⟩ := exists_one_of_hilbert_quadratic_majorant g
    (fun n => ((‖g n‖^3 : ℝ) : ℂ)) R (by
      intro n
      rw [Complex.norm_real,Real.norm_of_nonneg (by positivity : 0≤‖g n‖^3)]
      have hn := (lp.norm_apply_le_norm (by norm_num : (2 : ENNReal)≠0) g n).trans hg
      nlinarith [mul_nonneg (sq_nonneg ‖g n‖) (sub_nonneg.mpr hn)])
  have hb3n (n : ℤ) : ‖b3 n‖=‖g n‖^3 := by rw [hb3 n,Complex.norm_real,Real.norm_of_nonneg (by positivity : 0≤‖g n‖^3)]
  have hg2 : ‖g‖^2≤R^2 := pow_le_pow_left₀ (norm_nonneg g) hg 2
  have h2 : ‖b2‖≤R^2 := hb2norm.trans (by nlinarith)
  have h3 : ‖b3‖≤R^3 := hb3norm.trans (by
    nlinarith [mul_le_mul_of_nonneg_left hg2 hR])
  let K := puncturedLattice r hr
  let C := convolution (magnitude K) (magnitude b3)
  let A : Coeff r := (D : ℂ) • exponentInclusion hr.le b2
  let B : Coeff r := (M : ℂ) • (magnitude C+(‖b3‖ : ℂ) • magnitude K)
  have hAn (n : ℤ) : ‖A n‖=D*‖g n‖^2 := by
    simp only [A,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,norm_mul,Complex.norm_real,
      Real.norm_of_nonneg hD,exponentInclusion_apply,hb2n]
  have hBn (n : ℤ) : ‖B n‖=M*(‖C n‖+‖K n‖*‖b3‖) := by
    change ‖(M : ℂ)*((‖C n‖ : ℂ)+(‖b3‖ : ℂ)*(‖K n‖ : ℂ))‖=_
    rw [←Complex.ofReal_mul,←Complex.ofReal_add,←Complex.ofReal_mul,
      Complex.norm_real,Real.norm_of_nonneg (by positivity : 0≤M*(‖C n‖+‖b3‖*‖K n‖))]
    ring
  have hpoint (n : ℤ) : ‖positiveDividedCubicSums F n‖≤1*(‖A n‖+‖B n‖) := by
    rw [one_mul,hAn,hBn,positiveDividedCubicSums]
    by_cases hn : 0<n
    · rw [if_pos hn]
      obtain ⟨a,ha,hoff⟩ := hoff n
      exact divided_cubic_row_sum_bound hr n hn.ne' g a b3 hb3n (F n) D M hM ha (hdiag n) hoff (hs n)
    · rw [if_neg hn,norm_zero]
      positivity
  obtain ⟨hmem,hbound⟩ := memℓp_and_norm_ofFunctionOrZero_le_of_two_sequence_bound
    (positiveDividedCubicSums F) A B 1 (by norm_num) hpoint
  refine ⟨ofFunctionOrZero r (positiveDividedCubicSums F),
    ofFunctionOrZero_apply_of_mem r _ hmem,?_⟩
  have hA : ‖A‖≤D*R^2 := by
    rw [show ‖A‖=‖(D : ℂ)‖*‖exponentInclusion hr.le b2‖ from norm_smul _ _,
      Complex.norm_real,Real.norm_of_nonneg hD]
    exact mul_le_mul_of_nonneg_left ((norm_exponentInclusion_le hr.le b2).trans h2) hD
  have hC : ‖C‖≤‖K‖*‖b3‖ := by
    simpa only [C,norm_magnitude] using norm_convolution_le (magnitude K) (magnitude b3)
  have hB : ‖B‖≤2*M*‖K‖*R^3 := by
    rw [show ‖B‖=‖(M : ℂ)‖*‖magnitude C+(‖b3‖ : ℂ) • magnitude K‖ from norm_smul _ _,
      Complex.norm_real,Real.norm_of_nonneg hM]
    calc
      _≤M*(‖C‖+‖b3‖*‖K‖) := by
        apply mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans_eq ?_) hM
        simp only [norm_magnitude,norm_smul,Complex.norm_real,Real.norm_of_nonneg (norm_nonneg b3)]
      _≤M*(‖K‖*R^3+R^3*‖K‖) := by
        apply mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) hM
        · exact hC.trans (mul_le_mul_of_nonneg_left h3 (norm_nonneg K))
        · exact mul_le_mul_of_nonneg_right h3 (norm_nonneg K)
      _=_ := by ring
  have hbound' : ‖ofFunctionOrZero r (positiveDividedCubicSums F)‖≤‖A‖+‖B‖ := by
    simpa only [one_mul] using hbound
  exact hbound'.trans (add_le_add hA hB)

end NLS.Coeff
