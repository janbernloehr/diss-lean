import NLS.ZakharovShabat.LinearWeightDoubleSeries
import NLS.ZakharovShabat.ComplementaryDoubleEstimate

/-! # Lemma 25.2: the scalar double inverse on M₁

The absolutely convergent double series controls the actual complementary
sandwich in shifted weighted ℓ¹. Reflection gives the opposite physical sign.
-/
noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Scalar double inverse estimate, in the first physical orientation. -/
theorem shiftedNorm_complementarySandwich_false_linear (w : SpectralWeight)
    (hw : w.HasLinearFactor) (φ f : WeightedCoeff w.toWeight 2)
    {n : ℤ} {z : ℂ} (hz : z ∈ resonantStrip n) :
    w.shiftedNorm (-n) (complementarySandwich (by simp) w φ n z hz false f) ≤
      (4/(1+|(n:ℝ)|))*‖φ‖*w.shiftedNorm (-n) f := by
  let g := complementarySandwich (by simp) w φ n z hz false f
  let U (k l : ℤ) : ℂ := (w (k-n):ℂ)*complementarySymbol n z k*
    (φ.val (k+l)*(complementarySymbol n z l*f.val (-l)))
  obtain ⟨hs,hbound⟩ := summable_and_linearWeightAbsoluteSeries_le w hw φ f hz
  have hU (k l : ℤ) : ‖U k l‖ = linearWeightAbsoluteSeries w φ f n z (l,k) := by
    simp only [U, linearWeightAbsoluteSeries, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (w.positive (k-n))]
    ring
  have hcoeff (k : ℤ) : (w (k-n):ℂ)*g.val k = ∑' l : ℤ, U k l := by
    simp only [g, complementarySandwich_apply, Bool.not_false, freeFrequency_false, freeFrequency_true]
    rw [← (Equiv.neg ℤ).tsum_eq (fun l : ℤ => φ.val (k-l)*(complementarySymbol n z (-l)*f.val l))]
    simp only [Equiv.neg_apply, neg_neg, sub_neg_eq_add]
    simp only [U, tsum_mul_left]
    ring
  have hrow (k : ℤ) : w (k-n)*‖g.val k‖ ≤ ∑' l : ℤ, linearWeightAbsoluteSeries w φ f n z (l,k) := by
    have hUs : Summable (fun l : ℤ => ‖U k l‖) := by
      simpa only [hU, Prod.swap_prod_mk] using! hs.prod_symm.prod_factor k
    have h := norm_tsum_le_tsum_norm hUs
    rw [← hcoeff] at h
    simpa only [hU, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (w.positive (k-n))] using h
  have hgs : Summable (fun k : ℤ => w (k-n)*‖g.val k‖) := by
    simpa only [ENNReal.toReal_one, Real.rpow_one, ← sub_eq_add_neg] using
      w.summable_shiftedNorm_terms (by simp : (1:ℝ≥0∞) ≠ ⊤) (-n) g
  calc
    _ = ∑' k : ℤ, w (k-n)*‖g.val k‖ := by
      simpa only [ENNReal.toReal_one, Real.rpow_one, ← sub_eq_add_neg] using
        w.shiftedNorm_rpow_eq_tsum (by simp : (1:ℝ≥0∞) ≠ ⊤) (-n) g
    _ ≤ ∑' k : ℤ, ∑' l : ℤ, linearWeightAbsoluteSeries w φ f n z (l,k) :=
      Summable.tsum_le_tsum hrow hgs hs.prod_symm.prod
    _ = ∑' p : ℤ × ℤ, linearWeightAbsoluteSeries w φ f n z p := by
      exact hs.prod_symm.tsum_prod.symm.trans ((Equiv.prodComm ℤ ℤ).tsum_eq _)
    _ ≤ _ := hbound

/-- Reflection interchanges the two physical orientations of the actual sandwich. -/
theorem complementarySandwich_true_eq_reflection (w : SpectralWeight)
    (φ f : WeightedCoeff w.toWeight 2) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) :
    complementarySandwich (by simp) w φ n z hz true f =
      w.reflection (complementarySandwich (by simp) w (w.reflection φ) n z hz false (w.reflection f)) := by
  apply Subtype.ext
  funext j
  simp only [SpectralWeight.reflection_apply, complementarySandwich_apply,
    Bool.not_true, Bool.not_false, freeFrequency_false, freeFrequency_true]
  congr 1
  rw [← (Equiv.neg ℤ).tsum_eq (fun k : ℤ => φ.val (-(-j-k))*(complementarySymbol n z (-k)*f.val (-k)))]
  simp only [Equiv.neg_apply, neg_neg]
  apply tsum_congr
  intro k
  rw [show -(-j- -k)=j-k by omega]

/-- The uniform scalar estimate for either physical sign, throughout the closed strip. -/
theorem shiftedNorm_complementarySandwich_linear (w : SpectralWeight)
    (hw : w.HasLinearFactor) (φ f : WeightedCoeff w.toWeight 2)
    {n : ℤ} {z : ℂ} (hz : z ∈ resonantStrip n) (b : Bool) :
    w.shiftedNorm (-reciprocalCenter b n) (complementarySandwich (by simp) w φ n z hz b f) ≤
      (4/(1+|(n:ℝ)|))*‖φ‖*w.shiftedNorm (-reciprocalCenter b n) f := by
  cases b
  · exact shiftedNorm_complementarySandwich_false_linear w hw φ f hz
  · simp only [reciprocalCenter, freeFrequency_true, neg_neg]
    rw [complementarySandwich_true_eq_reflection, SpectralWeight.shiftedNorm_reflection]
    have h := shiftedNorm_complementarySandwich_false_linear w hw (w.reflection φ) (w.reflection f) hz
    simpa only [LinearIsometryEquiv.norm_map, SpectralWeight.shiftedNorm_reflection, neg_neg] using h

end NLS.ZakharovShabat
