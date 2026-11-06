import NLS.Articles.KdVKdV2Frequencies.NativeAllGapFrequencyMoments
import NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianOrigin

/-! # Exact free values of the intrinsic original physical frequencies

Closed-mode identification determines the true action derivatives even at
the completely collapsed free spectrum. No spectral definition of omega
or nonzero coordinate assumption is used.
-/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.KdV NLS.ZakharovShabat NLS.MKdV
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData

@[simp] theorem rawIntegerForwardHomeomorph_zero (D : GlobalRoughAbelianForwardData) (m : ℕ) :
    D.rawIntegerForwardHomeomorph m 0=0 := by
  have he := D.rawIntegerForwardHomeomorph_signed m 0
  simp only [Submodule.coe_zero,map_zero,D.signed_at_origin] at he
  apply Subtype.ext
  apply Subtype.ext
  funext j
  have h := congrArg (fun a : WeightedCoeff (Weight.sobolev (-1/2)) 2 => a.val j) he
  simpa only [WeightedCoeff.sobolevInclusion_apply,WeightedCoeff.zero_val] using! h

@[simp] theorem originalPositiveActions_zero (m : ℕ) (r : ℝ) (hrs : r=2*((m : ℝ)+1/2)) :
    originalPositiveActions m r hrs 0=⟨0,WeightedCoeff.zero_mem_positiveActionLocus _ _⟩ := by
  apply Subtype.ext
  apply Subtype.ext
  funext j
  simp only [originalPositiveActions_val,sobolevSignedActionSequence_apply,Submodule.coe_zero,
    WeightedCoeff.zero_val,mul_zero,ite_self]

private theorem zero_source_all_gaps_closed (D : GlobalRoughAbelianForwardData) (m : ℕ) (k : ℕ+) :
    hillRealGapHalfLength (nativeHillPhysicalSource m (0 : ScalarSobolev m) (by intro j; simp)).val
      (nativeHillPhysicalSource m (0 : ScalarSobolev m) (by intro j; simp)).property.1
      (nativeHillPhysicalSource m (0 : ScalarSobolev m) (by intro j; simp)).property.2 k=0 := by
  apply (D.rawIntegerForwardHomeomorph_zero_iff_closed m 0 k).mp
  rw [D.rawIntegerForwardHomeomorph_zero]
  rfl

private theorem zero_source_moment_sum (D : GlobalRoughAbelianForwardData) (m : ℕ) (n : ℕ+)
    (w : ℕ → ℂ) (hw : w 0=0) (l : ℕ) :
    (∑' k : ℕ, w k*hillIntrinsicFrequencyMoment
      (nativeHillPhysicalSource m (0 : ScalarSobolev m) (by intro j; simp)).val
      (nativeHillPhysicalSource m (0 : ScalarSobolev m) (by intro j; simp)).property.1
      (nativeHillPhysicalSource m (0 : ScalarSobolev m) (by intro j; simp)).property.2 n n.pos k (l+1))=0 := by
  let p := nativeHillPhysicalSource m (0 : ScalarSobolev m) (by intro j; simp)
  have hc : ∀ (k : ℕ) (_hk : 1≤k), 0<k → hillRealGapHalfLength p.val p.property.1 p.property.2 k=0 :=
    fun k hk _ => D.zero_source_all_gaps_closed m ⟨k,by omega⟩
  simpa using (hasSum_hillIntrinsicFrequencyMoment_closed_tail p.val p.property.1 p.property.2 n n.pos 0 hc w hw l).tsum_eq

/-- The actual intrinsic KdV frequency at the completely collapsed source has the exact free cube. -/
theorem nativeKdVFrequency_zero (D : GlobalRoughAbelianForwardData) (n : ℕ+) :
    (D.nativeSourceHierarchyFrequency 1 3 (by norm_num) 0 n : ℂ)=(2*(n : ℂ)*Real.pi)^3 := by
  have h := D.native_finiteGap_kdv_frequency_moments_all_gaps 0 ∅
    (fun k _ => D.zero_source_all_gaps_closed 1 k) n
  simp only [Submodule.coe_zero] at h
  rw [D.zero_source_moment_sum 1 n (fun k => (k : ℂ)) (by norm_num) 1,mul_zero] at h
  exact sub_eq_zero.mp h

/-- The actual intrinsic KdV2 frequency at zero has the exact fifth power and zero mass correction. -/
theorem nativeKdV2Frequency_zero (D : GlobalRoughAbelianForwardData) (n : ℕ+) :
    (D.nativeSourceHierarchyFrequency 2 5 (by norm_num) 0 n : ℂ)=(2*(n : ℂ)*Real.pi)^5 := by
  have h := D.native_finiteGap_kdv2_frequency_moments_all_gaps 0 ∅
    (fun k _ => D.zero_source_all_gaps_closed 2 k) n
  simp only [Submodule.coe_zero] at h
  have hm : nativeMiuraMass 2 0=0 := by
    simp [nativeMiuraMass,sobolevOddKinetic]
  rw [D.zero_source_moment_sum 2 n (fun k => (k : ℂ)^3) (by norm_num) 1,
    D.zero_source_moment_sum 2 n (fun k => (k : ℂ)) (by norm_num) 3,hm] at h
  simpa only [mul_zero,zero_add,sub_zero,sub_eq_zero] using h

/-- Exact free normalization on the ORIGINAL positive action cone of order three. -/
theorem originalKdVFrequency_zero (D : GlobalRoughAbelianForwardData) (n : ℕ+) :
    D.originalKdVFrequency ⟨0,WeightedCoeff.zero_mem_positiveActionLocus _ _⟩ n=(2*(n : ℝ)*Real.pi)^3 := by
  have h := D.nativeKdVFrequency_zero n
  simp only [nativeSourceHierarchyFrequency,D.rawIntegerForwardHomeomorph_zero,originalPositiveActions_zero] at h
  apply Complex.ofReal_injective
  simpa only [originalKdVFrequency,ofReal_pow,ofReal_mul,ofReal_ofNat,ofReal_natCast] using h

/-- Exact free normalization on the ORIGINAL positive action cone of order five. -/
theorem originalKdV2Frequency_zero (D : GlobalRoughAbelianForwardData) (n : ℕ+) :
    D.originalKdV2Frequency ⟨0,WeightedCoeff.zero_mem_positiveActionLocus _ _⟩ n=(2*(n : ℝ)*Real.pi)^5 := by
  have h := D.nativeKdV2Frequency_zero n
  simp only [nativeSourceHierarchyFrequency,D.rawIntegerForwardHomeomorph_zero,originalPositiveActions_zero] at h
  apply Complex.ofReal_injective
  simpa only [originalKdV2Frequency,ofReal_pow,ofReal_mul,ofReal_ofNat,ofReal_natCast] using h

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
