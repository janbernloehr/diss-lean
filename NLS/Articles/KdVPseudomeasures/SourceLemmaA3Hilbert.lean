import NLS.Articles.KdVPseudomeasures.SourceLemmaA3
import NLS.SequenceSpaces.TameSpectralConvolution
import NLS.SequenceSpaces.ConvolutionMajorants

/-! Appendix A.3(i). A tame weight split reduces negative-order Hilbert
multiplication to l2*l1 and l2*l2 estimates. The second term is summable in
the output Hilbert norm because -t>1/2. -/
noncomputable section
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open WeightedCoeff

private theorem sourceA3_inverse_weight (r : ℝ) (k : ℤ) :
    Weight.sobolev (-r) k = (Weight.sobolev r k)⁻¹ := by
  simp only [Weight.sobolev_apply, Real.rpow_neg (by positivity : 0 ≤ 1+|(k:ℝ)|)]

private theorem sourceA3_row (r : ℝ) (hr : 0 ≤ r)
    (a : WeightedCoeff (Weight.sobolev (-r)) 2)
    (b : WeightedCoeff (Weight.sobolev r) 2) (b0 : Coeff 1)
    (hb0 : ∀ k, b0 k=b.val k) (n : ℤ) :
    Summable (fun k : ℤ => a.val (n-k)*b.val k) ∧
      Weight.sobolev (-r) n*‖∑' k : ℤ, a.val (n-k)*b.val k‖ ≤
        (2:ℝ)^r*(‖Coeff.convolution (Coeff.magnitude (weightEquiv _ 2 a))
          (Coeff.magnitude b0) n‖ + Weight.sobolev (-r) n*‖a‖*‖b‖) := by
  let A := weightEquiv (Weight.sobolev (-r)) 2 a
  let B := weightEquiv (Weight.sobolev r) 2 b
  let w := Weight.sobolev (-r) n
  have hw : 0 < w := (Weight.sobolev (-r)).positive n
  have hA (k : ℤ) : ‖a.val k‖=Weight.sobolev r k*‖A k‖ := by
    have he : ‖A k‖=Weight.sobolev (-r) k*‖a.val k‖ := by
      change ‖(Weight.sobolev (-r) k:ℂ)*a.val k‖=_
      rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg ((Weight.sobolev (-r)).positive k).le]
    rw [he,sourceA3_inverse_weight,← mul_assoc,
      mul_inv_cancel₀ (ne_of_gt ((Weight.sobolev r).positive k)),one_mul]
  have hB (k : ℤ) : ‖B k‖=Weight.sobolev r k*‖b.val k‖ := by
    simp only [B,weightEquiv_apply,norm_mul,Complex.norm_real,
      Real.norm_of_nonneg ((Weight.sobolev r).positive k).le]
  have hterm (k : ℤ) : w*‖a.val (n-k)*b.val k‖ ≤
      (2:ℝ)^r*(‖A (n-k)‖*‖b0 k‖+w*(‖A (n-k)‖*‖B k‖)) := by
    have hadd := SpectralWeight.sobolev_add_le r hr n (-k)
    simp only [SpectralWeight.sobolev_apply,Weight.sobolev_neg,← sub_eq_add_neg] at hadd
    rw [norm_mul,hA,hb0,hB]
    have hcancel : w*Weight.sobolev r n=1 := by
      dsimp only [w]
      rw [sourceA3_inverse_weight,inv_mul_cancel₀ (ne_of_gt ((Weight.sobolev r).positive n))]
    have hh := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hadd (mul_nonneg (norm_nonneg (A (n-k)))
        (norm_nonneg (b.val k)))) hw.le
    calc
      _ ≤ w*((2:ℝ)^r*(Weight.sobolev r n+Weight.sobolev r k)*
          (‖A (n-k)‖*‖b.val k‖)) := by simpa only [mul_assoc] using hh
      _ = (w*Weight.sobolev r n)*((2:ℝ)^r*(‖A (n-k)‖*‖b.val k‖))+
          (2:ℝ)^r*(w*(‖A (n-k)‖*(Weight.sobolev r k*‖b.val k‖))) := by ring
      _ = _ := by rw [hcancel]; ring
  have hfirst : Summable (fun k : ℤ => ‖A (n-k)‖*‖b0 k‖) := by
    simpa only [norm_mul] using Coeff.summable_norm_youngConvolution_terms
      (show YoungRelation 2 1 2 by simp [YoungRelation,add_comm]) A b0 n
  have hsecond : Summable (fun k : ℤ => ‖A (n-k)‖*‖B k‖) := by
    simpa only [norm_mul] using Coeff.summable_norm_youngConvolution_terms
      (show YoungRelation 2 2 ⊤ by
        simpa only [YoungRelation,ENNReal.inv_top,add_zero] using
          (ENNReal.HolderConjugate.inv_add_inv_eq_one (2:ℝ≥0∞) 2).symm) A B n
  have hmajor := (hfirst.add (hsecond.mul_left w)).mul_left ((2:ℝ)^r)
  have hs := hmajor.of_nonneg_of_le (fun k => mul_nonneg hw.le (norm_nonneg _)) hterm
  have hnorm : Summable (fun k : ℤ => ‖a.val (n-k)*b.val k‖) := by
    simpa only [← mul_assoc,inv_mul_cancel₀ hw.ne',one_mul] using hs.mul_left w⁻¹
  refine ⟨hnorm.of_norm,?_⟩
  calc
    _ ≤ w*(∑' k : ℤ, ‖a.val (n-k)*b.val k‖) :=
      mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hnorm) hw.le
    _ = ∑' k : ℤ, w*‖a.val (n-k)*b.val k‖ := (tsum_mul_left).symm
    _ ≤ ∑' k : ℤ, (2:ℝ)^r*(‖A (n-k)‖*‖b0 k‖+w*(‖A (n-k)‖*‖B k‖)) :=
      hs.tsum_le_tsum hterm hmajor
    _ = (2:ℝ)^r*((∑' k : ℤ, ‖A (n-k)‖*‖b0 k‖)+
        w*(∑' k : ℤ, ‖A (n-k)‖*‖B k‖)) := by
      rw [tsum_mul_left,hfirst.tsum_add (hsecond.mul_left w),tsum_mul_left]
    _ ≤ (2:ℝ)^r*(‖Coeff.convolution (Coeff.magnitude A) (Coeff.magnitude b0) n‖+
        w*‖a‖*‖b‖) := by
      rw [Coeff.norm_magnitude_convolution_apply]
      have hcs := Coeff.norm_youngConvolution_tsum_le
        (show YoungRelation 2 2 ⊤ by
        simpa only [YoungRelation,ENNReal.inv_top,add_zero] using
          (ENNReal.HolderConjugate.inv_add_inv_eq_one (2:ℝ≥0∞) 2).symm)
        (Coeff.magnitude A) (Coeff.magnitude B) n
      have he : ‖∑' k : ℤ, Coeff.magnitude A (n-k)*Coeff.magnitude B k‖ =
          ∑' k : ℤ, ‖A (n-k)‖*‖B k‖ := by
        simp only [Coeff.magnitude_apply,← Complex.ofReal_mul,← Complex.ofReal_tsum,
          Complex.norm_real]
        exact Real.norm_of_nonneg (tsum_nonneg (fun _ => by positivity))
      rw [he,Coeff.norm_magnitude,Coeff.norm_magnitude] at hcs
      have hAn : ‖A‖=‖a‖ := rfl
      have hBn : ‖B‖=‖b‖ := rfl
      rw [hAn,hBn] at hcs
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [mul_assoc] using add_le_add (le_refl (∑' k : ℤ, ‖A (n-k)‖*‖b0 k‖))
        (mul_le_mul_of_nonneg_left hcs hw.le)

private theorem sourceA3_realize_majorant (w : Weight) (f : ℤ → ℂ) (D : Coeff 2)
    (h : ∀ n, ‖(w n:ℂ)*f n‖ ≤ ‖D n‖) :
    ∃ c : WeightedCoeff w 2, (∀ n, c.val n=f n) ∧ ‖c‖ ≤ ‖D‖ := by
  let c : WeightedCoeff w 2 := ⟨f,(lp.memℓp D).mono' h⟩
  refine ⟨c,fun _ => rfl,?_⟩
  change ‖weightEquiv w 2 c‖ ≤ ‖D‖
  exact lp.norm_mono (by norm_num : (2:ℝ≥0∞)≠0) h

/-- The literal negative Hilbert convolution estimate and its absolute convergence clauses. -/
def SourceA3HilbertEstimate (t : ℝ) : Prop :=
    ∃ C : ℝ, 0 < C ∧
      ∀ a : WeightedCoeff (Weight.sobolev t) 2,
      ∀ b : WeightedCoeff (Weight.sobolev 1) 2,
      ∃ c : WeightedCoeff (Weight.sobolev t) 2,
        (∀ n : ℤ, Summable (fun k : ℤ => a.val (n-k)*b.val k) ∧
          c.val n=∑' k : ℤ, a.val (n-k)*b.val k) ∧
        ‖c‖ ≤ C*‖a‖*‖b‖

/-- Appendix A.3(i), with absolute convergence and the exact negative
Hilbert order throughout the full printed range. -/
private theorem sourceA3_hilbert_core (r : ℝ) (hrHalf : (1:ℝ)/2 < r) (hr1 : r ≤ 1) :
    SourceA3HilbertEstimate (-r) := by
  unfold SourceA3HilbertEstimate
  have hr : 0 ≤ r := by linarith
  have hi (k : ℤ) : Weight.sobolev r k ≤ 1*Weight.sobolev 1 k := by
    rw [one_mul]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg (k:ℝ)]) hr1
  let J := WeightComparison.map (p := 2) (Weight.sobolev 1) (Weight.sobolev r)
    1 zero_le_one hi
  let B0 := sobolevToL1CLM 2 (by norm_num)
  let K : Coeff 2 := ⟨fun n => (Weight.sobolev r n:ℂ)⁻¹,
    Weight.inverse_sobolev_memlp (by norm_num) (by
      norm_num only [ENNReal.toReal_ofNat]; linarith)⟩
  let C0 := (2:ℝ)^r
  let C := C0*(‖B0‖+‖K‖)+1
  have hC0 : 0 ≤ C0 := by positivity
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro a b
  let A := weightEquiv (Weight.sobolev (-r)) 2 a
  let M := Coeff.convolution (Coeff.magnitude A) (Coeff.magnitude (B0 b))
  let D := (C0:ℂ) • (Coeff.magnitude M + ((‖a‖*‖J b‖:ℝ):ℂ) • Coeff.magnitude K)
  have hKpoint (n : ℤ) : ‖K n‖=Weight.sobolev (-r) n := by
    change ‖(Weight.sobolev r n:ℂ)⁻¹‖=_
    rw [norm_inv,Complex.norm_real,
      Real.norm_of_nonneg ((Weight.sobolev r).positive n).le,sourceA3_inverse_weight]
  have hDpoint (n : ℤ) : ‖D n‖=C0*(‖M n‖+Weight.sobolev (-r) n*‖a‖*‖J b‖) := by
    change ‖(C0:ℂ)*((‖M n‖:ℂ)+((‖a‖*‖J b‖:ℝ):ℂ)*(‖K n‖:ℂ))‖=_
    have he : (C0:ℂ)*((‖M n‖:ℂ)+((‖a‖*‖J b‖:ℝ):ℂ)*(‖K n‖:ℂ))=
        ((C0*(‖M n‖+‖a‖*‖J b‖*‖K n‖):ℝ):ℂ) := by push_cast; ring
    rw [he,Complex.norm_real,Real.norm_of_nonneg (by positivity),hKpoint]
    ring
  have hrow (n : ℤ) := sourceA3_row r hr a (J b) (B0 b) (fun k => by
    simp only [B0,sobolevToL1CLM_apply,J,WeightComparison.map_apply]) n
  have hcoeff (n k : ℤ) : a.val (n-k)*(J b).val k=a.val (n-k)*b.val k := by
    simp only [J,WeightComparison.map_apply]
  have hpoint (n : ℤ) :
      ‖(Weight.sobolev (-r) n:ℂ)*(∑' k : ℤ, a.val (n-k)*b.val k)‖ ≤ ‖D n‖ := by
    rw [norm_mul,Complex.norm_real,
      Real.norm_of_nonneg ((Weight.sobolev (-r)).positive n).le,hDpoint]
    simpa only [hcoeff] using (hrow n).2
  obtain ⟨c,hc,hcnorm⟩ := sourceA3_realize_majorant (Weight.sobolev (-r))
    (fun n => ∑' k : ℤ, a.val (n-k)*b.val k) D hpoint
  refine ⟨c,fun n => ⟨by simpa only [hcoeff] using (hrow n).1,hc n⟩,?_⟩
  have hM : ‖M‖ ≤ ‖a‖*‖B0 b‖ := by
    have hAn : ‖A‖=‖a‖ := rfl
    have h := Coeff.norm_convolution_le (Coeff.magnitude A) (Coeff.magnitude (B0 b))
    rw [Coeff.norm_magnitude,Coeff.norm_magnitude,hAn] at h
    exact h
  have hJ : ‖J b‖ ≤ ‖b‖ := by
    simpa only [one_mul] using WeightComparison.norm_map_le
      (Weight.sobolev 1) (Weight.sobolev r) 1 zero_le_one hi b
  calc
    _ ≤ ‖D‖ := hcnorm
    _ ≤ C0*(‖M‖+‖a‖*‖J b‖*‖K‖) := by
      calc
        _ = C0*‖Coeff.magnitude M+((‖a‖*‖J b‖:ℝ):ℂ) • Coeff.magnitude K‖ := by
          rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg hC0]
        _ ≤ _ := mul_le_mul_of_nonneg_left
          ((norm_add_le _ _).trans_eq (by simp only [Coeff.norm_magnitude,norm_smul,
            Complex.norm_real,Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))])) hC0
    _ ≤ C0*(‖a‖*(‖B0‖*‖b‖)+‖a‖*‖b‖*‖K‖) := by
      gcongr
      exact hM.trans (mul_le_mul_of_nonneg_left (B0.le_opNorm b) (norm_nonneg _))
    _ ≤ C*‖a‖*‖b‖ := by dsimp [C]; nlinarith [norm_nonneg a,norm_nonneg b]

/-- Appendix A.3(i), with the full printed parameter range. -/
theorem sourceLemmaA_3_i (t : ℝ) (ht : -1 ≤ t) (ht1 : t < -(1:ℝ)/2) :
    SourceA3HilbertEstimate t := by
  simpa only [neg_neg] using sourceA3_hilbert_core (-t) (by linarith) (by linarith)

end NLS.Articles.KdVPseudomeasures
