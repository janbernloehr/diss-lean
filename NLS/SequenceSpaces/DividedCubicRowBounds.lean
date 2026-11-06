import NLS.SequenceSpaces.PuncturedLattice
import NLS.SequenceSpaces.ConvolutionMajorants
import NLS.SequenceSpaces.WeightedCubicRows

/-! Dividing the literal index-weighted cubic row by its OWN index retains
reciprocal convolution decay. The identity k/(n*(n-k))=1/(n-k)-1/n supplies
an ellr majorant for every r>1, rather than only a uniform scalar bound. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.Coeff
variable {r : ℝ≥0∞}

theorem norm_divided_int_cubic_factor_le (hr : 1<r) (n k : ℤ) (hn : n≠0) (hkn : k≠n) :
    ‖(k : ℂ)/((n : ℂ)*((n-k : ℤ) : ℂ))‖≤
      ‖puncturedLattice r hr (n-k)‖+‖puncturedLattice r hr n‖ := by
  have hnc : (n : ℂ)≠0 := by exact_mod_cast hn
  have hnk : n-k≠0 := sub_ne_zero.mpr hkn.symm
  have hnkc : ((n-k : ℤ) : ℂ)≠0 := by exact_mod_cast hnk
  have he : (k : ℂ)/((n : ℂ)*((n-k : ℤ) : ℂ))=
      ((n-k : ℤ) : ℂ)⁻¹-(n : ℂ)⁻¹ := by
    have hnks : (n : ℂ)-(k : ℂ)≠0 := by exact_mod_cast hnk
    push_cast
    field_simp [hnc,hnks]
    ring
  rw [he,puncturedLattice_apply,if_neg hnk,puncturedLattice_apply,if_neg hn]
  exact norm_sub_le _ _

theorem divided_cubic_row_term_bound (hr : 1<r) (n k : ℤ) (hn : n≠0)
    (g a : Coeff 2) (f : ℤ → ℂ) (D M : ℝ) (hM : 0≤M) (ha : ‖a‖≤M)
    (hdiag : ‖f n‖≤D*‖g n‖^2)
    (hoff : ∀ j, j≠n → f j=g j^3/((n-j : ℤ) : ℂ)*a j) :
    ‖(k : ℂ)*f k/(n : ℂ)‖≤
      (if k=n then D*‖g n‖^2 else 0)+
        M*(‖puncturedLattice r hr (n-k)‖*‖g k‖^3+
          ‖puncturedLattice r hr n‖*‖g k‖^3) := by
  have hnc : (n : ℂ)≠0 := by exact_mod_cast hn
  by_cases hkn : k=n
  · subst k
    rw [mul_div_cancel_left₀ _ hnc,if_pos rfl]
    exact hdiag.trans (le_add_of_nonneg_right (by positivity))
  · have he : (k : ℂ)*f k/(n : ℂ)=
        ((k : ℂ)/((n : ℂ)*((n-k : ℤ) : ℂ)))*g k^3*a k := by rw [hoff k hkn];ring
    rw [he,norm_mul,norm_mul,norm_pow,if_neg hkn,zero_add]
    have hak := (lp.norm_apply_le_norm (by norm_num : (2 : ENNReal)≠0) a k).trans ha
    calc
      _≤(‖puncturedLattice r hr (n-k)‖+‖puncturedLattice r hr n‖)*‖g k‖^3*M := by
        gcongr
        exact norm_divided_int_cubic_factor_le hr n k hn hkn
      _=_ := by ring

/-- A literal actual row sum, divided by its own nonzero index, has the
full convolution majorant, retaining the diagonal and both off-diagonal terms. -/
theorem divided_cubic_row_sum_bound [Fact (1 ≤ r)] (hr : 1<r) (n : ℤ) (hn : n≠0)
    (g a : Coeff 2) (b : Coeff 1) (hb : ∀ k, ‖b k‖=‖g k‖^3)
    (f : ℤ → ℂ) (D M : ℝ) (hM : 0≤M) (ha : ‖a‖≤M)
    (hdiag : ‖f n‖≤D*‖g n‖^2)
    (hoff : ∀ j, j≠n → f j=g j^3/((n-j : ℤ) : ℂ)*a j)
    (hs : Summable (fun k : ℤ => ‖(k : ℂ)*f k‖)) :
    ‖(∑' k : ℤ, (k : ℂ)*f k)/(n : ℂ)‖≤D*‖g n‖^2+
      M*(‖convolution (magnitude (puncturedLattice r hr)) (magnitude b) n‖+
        ‖puncturedLattice r hr n‖*‖b‖) := by
  let K := puncturedLattice r hr
  have hbS : Summable (fun k : ℤ => ‖b k‖) := (lp.memℓp b).norm.summable_of_one
  have hconv : Summable (fun k : ℤ => ‖K (n-k)‖*‖b k‖) := by
    apply (hbS.mul_left ‖K‖).of_nonneg_of_le (fun k => by positivity)
    intro k
    exact mul_le_mul_of_nonneg_right
      (lp.norm_apply_le_norm (zero_lt_one.trans hr).ne' K (n-k)) (norm_nonneg _)
  have hd : Summable (fun k : ℤ => if k=n then D*‖g n‖^2 else 0) :=
    summable_of_ne_finset_zero (s := {n}) (fun k hk => if_neg (by simpa only [Finset.mem_singleton] using hk))
  have ht := (hconv.add (hbS.mul_left ‖K n‖)).mul_left M
  have hds : Summable (fun k : ℤ => ‖(k : ℂ)*f k/(n : ℂ)‖) := by
    simp only [norm_div]
    exact hs.div_const ‖(n : ℂ)‖
  have hbound (k : ℤ) : ‖(k : ℂ)*f k/(n : ℂ)‖≤
      (if k=n then D*‖g n‖^2 else 0)+M*(‖K (n-k)‖*‖b k‖+‖K n‖*‖b k‖) := by
    simp only [hb]
    exact divided_cubic_row_term_bound hr n k hn g a f D M hM ha hdiag hoff
  rw [←tsum_div_const]
  apply (norm_tsum_le_tsum_norm hds).trans ((hds.tsum_le_tsum hbound (hd.add ht)).trans_eq ?_)
  rw [Summable.tsum_add hd ht,tsum_ite_eq n,tsum_mul_left,
    Summable.tsum_add hconv (hbS.mul_left ‖K n‖),tsum_mul_left]
  rw [←norm_magnitude_convolution_apply K b n]
  have he : (∑' k : ℤ, ‖b k‖)=‖b‖ := by simpa using (lp.hasSum_norm (p := 1) (by simp) b).tsum_eq
  rw [he]

end NLS.Coeff
