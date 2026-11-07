import NLS.Articles.KdVPseudomeasures.OriginalHillIntegerCanonicalFlow
import NLS.KdV.HillNativeIntegerLower
import NLS.SequenceSpaces.SignedSobolevPositiveEquivalence

/-! Coefficient-preserving equivalence between the article's exact original
Sobolev domain and the signed native Sobolev model of the actual KdV flow.
The norms are compared, never identified. -/
noncomputable section
set_option autoImplicit false
open Complex NLS.WeightedCoeff NLS.Articles.KdVPseudomeasures
namespace NLS.KdV

abbrev KdVMeanZeroSobolev (m : ℕ) :=
  {p : RealHillWeightedPotential (hillIntegerWeight m) // p.val.val 0 = 0}

theorem kdv_signedWeight_le_original (m : ℕ) (k : ℤ) :
    Weight.signedSobolev (signedStepOrder 0 m) k ≤ (hillIntegerWeight m).doubleIndex.toWeight k := by
  rw [hillIntegerSobolev_source_order]
  exact (Weight.signedSobolev_le_sobolev m (Nat.cast_nonneg m) k).trans
    (hillIntegerWeight_dominate_scalar m k)

def kdvOriginalToSignedCLM (m : ℕ) :
    WeightedCoeff (hillIntegerWeight m).doubleIndex.toWeight 2 →L[ℂ]
      WeightedCoeff (Weight.signedSobolev (signedStepOrder 0 m)) 2 :=
  WeightedCoeff.inclusionCLM _ _ (kdv_signedWeight_le_original m)

theorem kdv_originalWeight_le_signed (m : ℕ) (k : ℤ) :
    (hillIntegerWeight m).doubleIndex.toWeight k ≤
      ((2*Real.pi)^m*2^m)*Weight.signedSobolev (signedStepOrder 0 m) k := by
  rw [hillIntegerSobolev_source_order]
  apply (hillIntegerWeight_le_scalar_scaled m k).trans
  have h := Weight.sobolev_le_two_rpow_mul_signedSobolev m (Nat.cast_nonneg m) k
  rw [Real.rpow_natCast] at h
  calc
    _ ≤ (2*Real.pi)^m*(2^m*Weight.signedSobolev m k) := mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by ring

def kdvSignedToOriginalCLM (m : ℕ) :
    WeightedCoeff (Weight.signedSobolev (signedStepOrder 0 m)) 2 →L[ℂ]
      WeightedCoeff (hillIntegerWeight m).doubleIndex.toWeight 2 :=
  WeightComparison.map _ _ ((2*Real.pi)^m*2^m) (by positivity) (kdv_originalWeight_le_signed m)

@[simp] theorem kdvOriginalToSignedCLM_apply (m : ℕ)
    (p : WeightedCoeff (hillIntegerWeight m).doubleIndex.toWeight 2) (k : ℤ) :
    (kdvOriginalToSignedCLM m p).val k = p.val k :=
  WeightedCoeff.inclusionCLM_apply _ _ _ p k

@[simp] theorem kdvSignedToOriginalCLM_apply (m : ℕ)
    (p : WeightedCoeff (Weight.signedSobolev (signedStepOrder 0 m)) 2) (k : ℤ) :
    (kdvSignedToOriginalCLM m p).val k = p.val k := WeightComparison.map_apply _ _ _ _ _ p k

def kdvOriginalToSigned (m : ℕ) (p : KdVMeanZeroSobolev m) : RealSignedHilbert (signedStepOrder 0 m) :=
  ⟨⟨kdvOriginalToSignedCLM m p.val.val,by
    change (kdvOriginalToSignedCLM m p.val.val).val 0 = 0
    simpa only [kdvOriginalToSignedCLM_apply] using p.property⟩,
    fun k => by simpa only [kdvOriginalToSignedCLM_apply,SpectralWeight.toCoeff_apply] using p.val.property k⟩

def kdvSignedToOriginal (m : ℕ) (p : RealSignedHilbert (signedStepOrder 0 m)) : KdVMeanZeroSobolev m :=
  ⟨⟨kdvSignedToOriginalCLM m p.val.val,fun k => by
    simpa only [SpectralWeight.toCoeff_apply,kdvSignedToOriginalCLM_apply] using p.property k⟩,
    by
      simpa only [kdvSignedToOriginalCLM_apply] using (show p.val.val.val 0 = 0 from p.val.property)⟩

@[simp] theorem kdvOriginalToSigned_apply (m : ℕ) (p : KdVMeanZeroSobolev m) (k : ℤ) :
    (kdvOriginalToSigned m p).val.val.val k = p.val.val.val k := kdvOriginalToSignedCLM_apply m _ k

@[simp] theorem kdvSignedToOriginal_apply (m : ℕ)
    (p : RealSignedHilbert (signedStepOrder 0 m)) (k : ℤ) :
    (kdvSignedToOriginal m p).val.val.val k = p.val.val.val k := kdvSignedToOriginalCLM_apply m _ k

/-- Exact original coefficients and equivalent original Sobolev norm
 topologies, including the real form and the zero mode. -/
def kdvOriginalSobolevHomeomorph (m : ℕ) :
    KdVMeanZeroSobolev m ≃ₜ RealSignedHilbert (signedStepOrder 0 m) where
  toFun := kdvOriginalToSigned m
  invFun := kdvSignedToOriginal m
  left_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    funext k
    simp only [kdvSignedToOriginal_apply,kdvOriginalToSigned_apply]
  right_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    funext k
    simp only [kdvOriginalToSigned_apply,kdvSignedToOriginal_apply]
  continuous_toFun := by
    have h : Continuous (fun p : KdVMeanZeroSobolev m => kdvOriginalToSignedCLM m p.val.val) :=
      (kdvOriginalToSignedCLM m).continuous.comp (continuous_subtype_val.comp continuous_subtype_val)
    exact (h.subtype_mk _).subtype_mk _
  continuous_invFun := by
    have h : Continuous (fun p : RealSignedHilbert (signedStepOrder 0 m) => kdvSignedToOriginalCLM m p.val.val) :=
      (kdvSignedToOriginalCLM m).continuous.comp (continuous_subtype_val.comp continuous_subtype_val)
    exact (h.subtype_mk _).subtype_mk _

end NLS.KdV
