import NLS.SequenceSpaces.PeriodOneFractionalMiuraProduct
import NLS.SequenceSpaces.FourierLebesgueHilbertEmbedding
import NLS.SequenceSpaces.ExponentEmbedding

/-! # The literal Miura product in native Fourier-Lebesgue norms -/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS

def periodOneFourierLebesgueMiuraHilbertInclusion (s p : ℝ) (hp : 2<p)
    [Fact (1≤ENNReal.ofReal p)] :
    WeightedCoeff (Weight.sobolev (s+1)) (ENNReal.ofReal p) →L[ℂ]
      WeightedCoeff (Weight.sobolev (s+1/2+1/(2*p))) 2 :=
  (WeightedCoeff.sobolevInclusion
    (by linarith : s+1/2+1/(2*p)≤s+1-1/2+1/(2*p))).comp
      (WeightedCoeff.fourierLebesgueHilbertInclusion (s+1) p hp)

@[simp] theorem periodOneFourierLebesgueMiuraHilbertInclusion_apply
    (s p : ℝ) (hp : 2<p) [Fact (1≤ENNReal.ofReal p)]
    (a : WeightedCoeff (Weight.sobolev (s+1)) (ENNReal.ofReal p)) (n : ℤ) :
    (periodOneFourierLebesgueMiuraHilbertInclusion s p hp a).val n=a.val n := by
  simp only [periodOneFourierLebesgueMiuraHilbertInclusion,ContinuousLinearMap.comp_apply,
    WeightedCoeff.sobolevInclusion_apply,WeightedCoeff.fourierLebesgueHilbertInclusion_apply]

def periodOneFourierLebesgueMiuraProduct (s p : ℝ) (hs : -1/2≤s) (hp : 2<p)
    [Fact (1≤ENNReal.ofReal p)] :
    WeightedCoeff (Weight.sobolev (s+1)) (ENNReal.ofReal p) →L[ℂ]
      WeightedCoeff (Weight.sobolev (s+1)) (ENNReal.ofReal p) →L[ℂ]
        WeightedCoeff (Weight.sobolev s) (ENNReal.ofReal p) := by
  let r := s+1/2+1/(2*p)
  let d := 1/2+1/(2*p)
  have hδ : 0<1/(2*p) := by positivity
  have hr : 0≤r := by dsimp only [r];linarith
  have hd : 1/2<d := by dsimp only [d];linarith
  have h2p : (2 : ℝ≥0∞)≤ENNReal.ofReal p := by exact_mod_cast ENNReal.ofReal_le_ofReal hp.le
  let L := periodOneFourierLebesgueMiuraHilbertInclusion s p hp
  let B := periodOneFractionalMiuraProductCLM r hr d hd
  let J : WeightedCoeff (Weight.sobolev (r-d)) 2 →L[ℂ]
      WeightedCoeff (Weight.sobolev s) (ENNReal.ofReal p) :=
    (WeightedCoeff.exponentInclusion _ h2p).comp
      (WeightedCoeff.sobolevInclusion (by dsimp only [r,d];linarith : s≤r-d))
  exact ((ContinuousLinearMap.compL ℂ (WeightedCoeff (Weight.sobolev (s+1)) (ENNReal.ofReal p))
    (WeightedCoeff (Weight.sobolev (r-d)) 2) (WeightedCoeff (Weight.sobolev s) (ENNReal.ofReal p))) J).comp
      (B.bilinearComp L L)

@[simp] theorem periodOneFourierLebesgueMiuraProduct_apply
    (s p : ℝ) (hs : -1/2≤s) (hp : 2<p) [Fact (1≤ENNReal.ofReal p)]
    (a b : WeightedCoeff (Weight.sobolev (s+1)) (ENNReal.ofReal p)) (n : ℤ) :
    (periodOneFourierLebesgueMiuraProduct s p hs hp a b).val n=
      ∑' j : ℤ, a.val (n-j)*b.val j := by
  simp only [periodOneFourierLebesgueMiuraProduct,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply,ContinuousLinearMap.bilinearComp_apply,
    WeightedCoeff.exponentInclusion_apply,WeightedCoeff.sobolevInclusion_apply,
    periodOneFractionalMiuraProductCLM_apply,periodOneFractionalMiuraProduct_apply,
    periodOneFourierLebesgueMiuraHilbertInclusion_apply]

/-- The uniform weighted row estimate retains the FULL input order,
with no derivative loss inside the row bound. -/
theorem weighted_periodOneFractionalMiuraProduct_row_bound
    (t : ℝ) (ht : 0≤t) (d : ℝ) (hd : 1/2<d)
    (a b : WeightedCoeff (Weight.sobolev t) 2) (n : ℤ) :
    ‖(Weight.sobolev t n : ℂ)*(periodOneFractionalMiuraProduct t ht d hd a b).val n‖≤
      (2*(2 : ℝ)^t*‖a‖)*‖b‖ := by
  let u := WeightedCoeff.sobolevToL2 ht a
  let v := WeightedCoeff.sobolevToL2 ht b
  have hu : Memℓp (fun j => (Weight.sobolev t j : ℂ)*u j) 2 := by
    simpa only [u,WeightedCoeff.sobolevToL2_apply] using
      (show Memℓp (fun j => (Weight.sobolev t j : ℂ)*a.val j) 2 from a.property)
  have hv : Memℓp (fun j => (Weight.sobolev t j : ℂ)*v j) 2 := by
    simpa only [v,WeightedCoeff.sobolevToL2_apply] using
      (show Memℓp (fun j => (Weight.sobolev t j : ℂ)*b.val j) 2 from b.property)
  have hU : (⟨_,hu⟩ : Coeff 2)=WeightedCoeff.weightEquiv (Weight.sobolev t) 2 a := by
    ext j
    simp only [u,WeightedCoeff.sobolevToL2_apply,WeightedCoeff.weightEquiv_apply]
  have hV : (⟨_,hv⟩ : Coeff 2)=WeightedCoeff.weightEquiv (Weight.sobolev t) 2 b := by
    ext j
    simp only [v,WeightedCoeff.sobolevToL2_apply,WeightedCoeff.weightEquiv_apply]
  have H := weighted_miura_product_uniform_bound t ht u v hu hv n
  rw [hU,hV] at H
  change Weight.sobolev t n*‖(periodOneMiuraProduct u v).val n‖≤
    (2 : ℝ)^t*(‖a‖*‖v‖+‖u‖*‖b‖) at H
  change ‖(Weight.sobolev t n : ℂ)*(periodOneMiuraProduct u v).val n‖≤_
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Weight.positive _ n)]
  have h1 := WeightedCoeff.norm_sobolevToL2_le ht a
  have h2 := WeightedCoeff.norm_sobolevToL2_le ht b
  exact H.trans (by
    change (2 : ℝ)^t*(‖a‖*‖v‖+‖u‖*‖b‖)≤_
    nlinarith [mul_le_mul_of_nonneg_left h2 (norm_nonneg a),
      mul_le_mul_of_nonneg_right h1 (norm_nonneg b),
      Real.rpow_pos_of_pos (by norm_num : (0 : ℝ)<2) t])

theorem periodOneFourierLebesgueMiuraProduct_comm
    (s p : ℝ) (hs : -1/2≤s) (hp : 2<p) [Fact (1≤ENNReal.ofReal p)]
    (a b : WeightedCoeff (Weight.sobolev (s+1)) (ENNReal.ofReal p)) :
    periodOneFourierLebesgueMiuraProduct s p hs hp a b=
      periodOneFourierLebesgueMiuraProduct s p hs hp b a := by
  let r : ℝ := s+1/2+1/(2*p)
  have hr : 0≤r := by
    dsimp only [r]
    have hδ : 0<1/(2*p) := by positivity
    linarith
  let L := periodOneFourierLebesgueMiuraHilbertInclusion s p hp
  have he := periodOneMiuraProduct_comm (WeightedCoeff.sobolevToL2 hr (L a))
    (WeightedCoeff.sobolevToL2 hr (L b))
  apply Subtype.ext
  funext n
  have h := congrArg (fun q : PeriodOneHminusOne => q.val n) he
  simpa only [periodOneFourierLebesgueMiuraProduct_apply,periodOneMiuraProduct_apply,
    WeightedCoeff.sobolevToL2_apply,L,periodOneFourierLebesgueMiuraHilbertInclusion_apply] using h

end NLS
