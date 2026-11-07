import NLS.Articles.KdVKdV2Frequencies.OriginalL2ActionTrace
import NLS.Articles.KdVKdV2Frequencies.OriginalKdVBirkhoffFlow
import NLS.SequenceSpaces.PhysicalRealPositiveEnergy

/-! Exact L2 conservation and target norm bounds for the ACTUAL KdV
Birkhoff flow. The physical action trace supplies the source energy. -/
noncomputable section
open Set Complex NLS.KdV NLS.Articles.KdVConvexity
open scoped ENNReal ComplexConjugate
namespace NLS.Articles.KdVKdV2Frequencies

theorem native_l2_target_positive_sq (D : GlobalRoughAbelianForwardData)
    (a : physicalRealDeletedSubmodule) (n : ℕ+) :
    ‖(D.realNativeForward 1 (by norm_num) a).val.val (n:ℤ)‖^2=
      Weight.sobolev 1 (n:ℤ)*‖D.roughActionCoordinate n
        (GlobalRoughAbelianForwardData.realNativeSource 1 (by norm_num) a)‖ := by
  let b := D.realNativeForward 1 (by norm_num) a
  have hr := (periodOneL2Conjugation_fixed_iff _).mp
    ((deletedL2Conjugation_fixed_iff _).mp b.property)
  have he : positiveIndexInjection actionIndexEquiv (actionIndexEquiv.symm n)=(n:ℤ) :=
    congrArg (fun m : ℕ+ => (m:ℤ)) (actionIndexEquiv.apply_symm_apply n)
  have hprod : nativeActionCoordinates D 1 (by norm_num) a (actionIndexEquiv.symm n)=
      b.val.val (n:ℤ)*conj (b.val.val (n:ℤ)) := by
    rw [nativeActionCoordinates,quadraticActions_deletedToSignedPair_apply,he]
    exact congrArg (fun z : ℂ => b.val.val (n:ℤ)*z) (hr (n:ℤ))
  have hi := nativeActionCoordinates_raw_product D 1 (by norm_num) a n
  have hw : (2:ℝ)*1-1=1 := by norm_num
  simp only [hw] at hi
  have hn := congrArg norm hi
  rw [hprod,norm_div,norm_mul,norm_conj,Complex.norm_real,
    Real.norm_of_nonneg (Weight.sobolev 1 |>.positive (n:ℤ)).le] at hn
  have h := (div_eq_iff (Weight.sobolev 1 |>.positive (n:ℤ)).ne').mp hn
  simpa only [pow_two,mul_comm] using h

theorem norm_native_l2_forward_le (D : GlobalRoughAbelianForwardData)
    (a : physicalRealDeletedSubmodule) : ‖D.realNativeForward 1 (by norm_num) a‖≤‖a‖ := by
  have hs := hasSum_physicalRealDeleted_positive_sq (D.realNativeForward 1 (by norm_num) a)
  have ht := hasSum_native_l2_rough_actions D a
  have hb (j : ℕ) : ‖(D.realNativeForward 1 (by norm_num) a).val.val ((j+1:ℕ):ℤ)‖^2≤
      (2*Real.pi*(j+1:ℕ))*‖D.roughActionCoordinate ⟨j+1,by omega⟩
        (GlobalRoughAbelianForwardData.realNativeSource 1 (by norm_num) a)‖ := by
    let n : ℕ+ := ⟨j+1,by omega⟩
    have h := native_l2_target_positive_sq D a n
    calc
      _ = Weight.sobolev 1 (n:ℤ)*‖D.roughActionCoordinate n
          (GlobalRoughAbelianForwardData.realNativeSource 1 (by norm_num) a)‖ := h
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        change Weight.sobolev 1 ((j+1:ℕ):ℤ)≤2*Real.pi*(j+1:ℕ)
        simp only [Weight.sobolev_apply,Real.rpow_one,Int.cast_natCast,
          abs_of_nonneg (by positivity : (0:ℝ)≤(j+1:ℕ))]
        have hj : (1:ℝ)≤(j+1:ℕ) := by exact_mod_cast (show 1≤j+1 by omega)
        nlinarith [Real.pi_gt_three]
  have hm := hs.summable.tsum_le_tsum hb ht.summable
  rw [hs.tsum_eq,ht.tsum_eq] at hm
  nlinarith [norm_nonneg (D.realNativeForward 1 (by norm_num) a),norm_nonneg a]

theorem norm_native_l2_raw_target_le (D : GlobalRoughAbelianForwardData)
    (a : physicalRealDeletedSubmodule) : ‖D.realNativeTarget 1 (by norm_num) a‖≤‖a‖ := by
  rw [←D.realNativeForward_target_lift]
  rw [WeightedCoeff.meanZeroWeightedLift_norm]
  exact norm_native_l2_forward_le D a

theorem nativeKdVSourceFlow_rough_actions (D : GlobalRoughAbelianForwardData)
    (t : ℝ) (ht : 0≤t) (G : ℕ+ → Coeff 1 → ℂ) (time : ℝ)
    (a : physicalRealDeletedSubmodule) (n : ℕ+) :
    D.roughActionCoordinate n (GlobalRoughAbelianForwardData.realNativeSource t ht
      (nativeKdVSourceFlow D t ht G time a))=
      D.roughActionCoordinate n (GlobalRoughAbelianForwardData.realNativeSource t ht a) := by
  calc
    _=nativeActionCoordinates D t ht (nativeKdVSourceFlow D t ht G time a) (actionIndexEquiv.symm n)/
        (Weight.sobolev (2*t-1) (n:ℤ):ℂ) := (nativeActionCoordinates_raw_product D t ht _ n).symm
    _=nativeActionCoordinates D t ht a (actionIndexEquiv.symm n)/(Weight.sobolev (2*t-1) (n:ℤ):ℂ) := by
      rw [nativeKdVSourceFlow_actions]
    _=_ := nativeActionCoordinates_raw_product D t ht a n

theorem norm_nativeKdVSourceFlow_l2 (D : GlobalRoughAbelianForwardData)
    (G : ℕ+ → Coeff 1 → ℂ) (time : ℝ) (a : physicalRealDeletedSubmodule) :
    ‖nativeKdVSourceFlow D 1 (by norm_num) G time a‖=‖a‖ := by
  have hs := hasSum_native_l2_rough_actions D (nativeKdVSourceFlow D 1 (by norm_num) G time a)
  have ht := hasSum_native_l2_rough_actions D a
  have hf : (fun j : ℕ => (2*Real.pi*(j+1:ℕ))*
      ‖D.roughActionCoordinate ⟨j+1,by omega⟩
        (GlobalRoughAbelianForwardData.realNativeSource 1 (by norm_num)
          (nativeKdVSourceFlow D 1 (by norm_num) G time a))‖)=
      (fun j : ℕ => (2*Real.pi*(j+1:ℕ))*
        ‖D.roughActionCoordinate ⟨j+1,by omega⟩
          (GlobalRoughAbelianForwardData.realNativeSource 1 (by norm_num) a)‖) := by
    funext j
    exact congrArg (fun z : ℂ => (2*Real.pi*(j+1:ℕ))*‖z‖)
      (nativeKdVSourceFlow_rough_actions D 1 (by norm_num) G time a ⟨j+1,by omega⟩)
  rw [hf] at hs
  have he := hs.unique ht
  nlinarith [norm_nonneg (nativeKdVSourceFlow D 1 (by norm_num) G time a),norm_nonneg a]

theorem norm_originalKdVBirkhoffFlow_l2 (D : GlobalRoughAbelianForwardData)
    (G : ℕ+ → Coeff 1 → ℂ) (time : ℝ)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((0:ℕ):ℝ))) :
    ‖originalKdVBirkhoffFlow D ((0:ℕ):ℝ) (by norm_num) G time q‖=‖q‖ := by
  unfold originalKdVBirkhoffFlow
  dsimp only
  rw [LinearIsometryEquiv.norm_map]
  have h := norm_nativeKdVSourceFlow_l2 D G time
    ((physicalRealMeanZeroWeightedIsometry (Weight.sobolev ((0:ℕ):ℝ))
      (Weight.sobolev_neg ((0:ℕ):ℝ))).symm q)
  simpa only [Nat.cast_zero,zero_add,LinearIsometryEquiv.norm_map] using h

end NLS.Articles.KdVKdV2Frequencies
