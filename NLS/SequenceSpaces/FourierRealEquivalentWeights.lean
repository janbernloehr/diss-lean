import NLS.SequenceSpaces.FourierRealZeroMultiplier
import NLS.SequenceSpaces.SignedSobolevWeight
import NLS.SequenceSpaces.WeightedInsertion

/-! Equivalent even weights give coefficient-preserving continuous
real linear equivalences on the physical mean-zero Fourier form. -/
noncomputable section
open Complex
open scoped ENNReal
namespace NLS.WeightedCoeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def fourierRealWeightEquiv (w v : Weight) (hw : ∀ k, w (-k)=w k) (hv : ∀ k, v (-k)=v k)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hvw : ∀ k, v k ≤ A*w k) (hwv : ∀ k, w k ≤ B*v k) :
    fourierRealZeroSubmodule w p ≃L[ℝ] fourierRealZeroSubmodule v p :=
  ContinuousLinearEquiv.equivOfInverse
    (fourierRealZeroMultiplier w v hv (fun _ => 1) A hA (by simpa only [norm_one,mul_one] using hvw) (by intro k; simp))
    (fourierRealZeroMultiplier v w hw (fun _ => 1) B hB (by simpa only [norm_one,mul_one] using hwv) (by intro k; simp))
    (by intro a; apply Subtype.ext; apply Subtype.ext; apply Subtype.ext; funext k
        simp only [fourierRealZeroMultiplier_apply,one_mul])
    (by intro a; apply Subtype.ext; apply Subtype.ext; apply Subtype.ext; funext k
        simp only [fourierRealZeroMultiplier_apply,one_mul])

theorem fourierRealWeightEquiv_apply (w v : Weight) (hw : ∀ k, w (-k)=w k) (hv : ∀ k, v (-k)=v k)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hvw : ∀ k, v k ≤ A*w k) (hwv : ∀ k, w k ≤ B*v k)
    (a : fourierRealZeroSubmodule w p) (k : ℤ) :
    (fourierRealWeightEquiv w v hw hv A B hA hB hvw hwv a).val.val.val k = a.val.val.val k := by
  change (fourierRealZeroMultiplier w v hv (fun _ => 1) A hA
    (by simpa only [norm_one,mul_one] using hvw) (by intro j; simp) a).val.val.val k = _
  rw [fourierRealZeroMultiplier_apply,one_mul]

theorem fourierRealWeightEquiv_symm_apply (w v : Weight) (hw : ∀ k, w (-k)=w k) (hv : ∀ k, v (-k)=v k)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hvw : ∀ k, v k ≤ A*w k) (hwv : ∀ k, w k ≤ B*v k)
    (a : fourierRealZeroSubmodule v p) (k : ℤ) :
    ((fourierRealWeightEquiv w v hw hv A B hA hB hvw hwv).symm a).val.val.val k = a.val.val.val k := by
  change (fourierRealZeroMultiplier v w hw (fun _ => 1) B hB
    (by simpa only [norm_one,mul_one] using hwv) (by intro j; simp) a).val.val.val k = _
  rw [fourierRealZeroMultiplier_apply,one_mul]

def periodOneSobolevPullback (s : ℝ) : Weight := (Weight.sobolev s).pullback (Coeff.parityEmbedding 0)

theorem periodOneSobolevPullback_neg (s : ℝ) (k : ℤ) : periodOneSobolevPullback s (-k) = periodOneSobolevPullback s k := by
  simp only [periodOneSobolevPullback,Weight.pullback_apply,Coeff.parityEmbedding_apply,add_zero,mul_neg,Weight.sobolev_neg]

theorem periodOneSobolevPullback_signed_bounds (s : ℝ) (hs : 0 ≤ s) (k : ℤ) :
    Weight.signedSobolev s k ≤ periodOneSobolevPullback s k ∧
      periodOneSobolevPullback s k ≤ (3:ℝ)^s*Weight.signedSobolev s k := by
  simp only [periodOneSobolevPullback,Weight.pullback_apply,Coeff.parityEmbedding_apply,add_zero,
    Weight.sobolev_apply,Weight.signedSobolev,Int.cast_mul,Int.cast_ofNat,abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 2)]
  have hbase : max 1 |(k:ℝ)| ≤ 1+2*|(k:ℝ)| :=
    max_le (by linarith [abs_nonneg (k:ℝ)]) (by linarith [abs_nonneg (k:ℝ)])
  have hu : 1+2*|(k:ℝ)| ≤ 3*max 1 |(k:ℝ)| := by
    linarith [le_max_left (1:ℝ) |(k:ℝ)|,le_max_right (1:ℝ) |(k:ℝ)|]
  refine ⟨Real.rpow_le_rpow (by positivity) hbase hs,?_⟩
  calc
    _ ≤ (3*max 1 |(k:ℝ)|)^s := Real.rpow_le_rpow (by positivity) hu hs
    _ = _ := Real.mul_rpow (by norm_num) (by positivity)

def periodOneSobolevSignedEquiv (s : ℝ) (hs : 0 ≤ s) :
    fourierRealZeroSubmodule (periodOneSobolevPullback s) p ≃L[ℝ]
      fourierRealZeroSubmodule (Weight.signedSobolev s) p :=
  fourierRealWeightEquiv _ _ (periodOneSobolevPullback_neg s) (Weight.signedSobolev_neg s)
    1 ((3:ℝ)^s) zero_le_one (by positivity)
    (fun k => by simpa only [one_mul] using (periodOneSobolevPullback_signed_bounds s hs k).1)
    (fun k => (periodOneSobolevPullback_signed_bounds s hs k).2)

theorem sobolev_signed_bounds (s : ℝ) (hs : 0 ≤ s) (k : ℤ) :
    Weight.signedSobolev s k ≤ Weight.sobolev s k ∧
      Weight.sobolev s k ≤ (3:ℝ)^s*Weight.signedSobolev s k := by
  have hl : max 1 |(k:ℝ)| ≤ 1+|(k:ℝ)| := max_le
    (by linarith [abs_nonneg (k:ℝ)]) (by linarith)
  refine ⟨Real.rpow_le_rpow (by positivity) hl hs,?_⟩
  apply le_trans _ (periodOneSobolevPullback_signed_bounds s hs k).2
  change (1+|(k:ℝ)|)^s ≤ (1+|((2*k+0:ℤ):ℝ)|)^s
  apply Real.rpow_le_rpow (by positivity) _ hs
  simp only [add_zero,Int.cast_mul,Int.cast_ofNat,abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 2)]
  linarith [abs_nonneg (k:ℝ)]

def sobolevSignedRealEquiv (s : ℝ) (hs : 0 ≤ s) :
    fourierRealZeroSubmodule (Weight.sobolev s) p ≃L[ℝ]
      fourierRealZeroSubmodule (Weight.signedSobolev s) p :=
  fourierRealWeightEquiv _ _ (Weight.sobolev_neg s) (Weight.signedSobolev_neg s)
    1 ((3:ℝ)^s) zero_le_one (by positivity)
    (fun k => by simpa only [one_mul] using (sobolev_signed_bounds s hs k).1)
    (fun k => (sobolev_signed_bounds s hs k).2)

theorem sobolevSignedRealEquiv_apply (s : ℝ) (hs : 0 ≤ s)
    (a : fourierRealZeroSubmodule (Weight.sobolev s) p) (k : ℤ) :
    (sobolevSignedRealEquiv s hs a).val.val.val k = a.val.val.val k := by
  rw [sobolevSignedRealEquiv,fourierRealWeightEquiv_apply]

theorem sobolevSignedRealEquiv_symm_apply (s : ℝ) (hs : 0 ≤ s)
    (a : fourierRealZeroSubmodule (Weight.signedSobolev s) p) (k : ℤ) :
    ((sobolevSignedRealEquiv s hs).symm a).val.val.val k = a.val.val.val k := by
  rw [sobolevSignedRealEquiv,fourierRealWeightEquiv_symm_apply]

end NLS.WeightedCoeff
