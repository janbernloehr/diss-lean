import NLS.Articles.KdVKdV2Frequencies.OriginalL2ActionBound
import NLS.Articles.KdVKdV2Frequencies.NativeActionPhysicalCounterterm
import NLS.SequenceSpaces.HilbertCoordinateContinuity

/-! Exact original L2 action trace and the norm of the ACTUAL native target.
No bounded-image assertion for an arbitrary analytic map is used. -/
noncomputable section
open Set Complex NLS.KdV NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.Articles.KdVKdV2Frequencies

theorem norm_nativeHillPhysicalSource_zero
    (q : ScalarSobolev 0) (hq : ∀ j : ℤ, q.val (-j)=conj (q.val j)) :
    ‖(nativeHillPhysicalSource 0 q hq).val‖=‖q‖ := by
  have hp : WeightedCoeff.weightEquiv SpectralWeight.one.toWeight 2
      (nativeHillPhysicalSource 0 q hq).val=
      Coeff.periodDouble (WeightedCoeff.sobolevToL2 (Nat.cast_nonneg 0) q) := by
    ext j
    have h := congrArg (fun a : Coeff 2 => a j) (nativeHillPhysicalSource_toCoeff 0 q hq)
    simpa only [WeightedCoeff.weightEquiv_apply,SpectralWeight.toCoeff_apply,
      SpectralWeight.one_apply,Complex.ofReal_one,one_mul] using h
  have hqnorm : WeightedCoeff.sobolevToL2 (Nat.cast_nonneg 0) q=
      WeightedCoeff.weightEquiv (Weight.sobolev ((0:ℕ):ℝ)) 2 q := by
    ext j
    simp only [WeightedCoeff.sobolevToL2_apply,WeightedCoeff.weightEquiv_apply,
      Weight.sobolev_apply,Nat.cast_zero,Real.rpow_zero,Complex.ofReal_one,one_mul]
  rw [WeightedCoeff.norm_eq,hp,Coeff.norm_periodDouble,hqnorm]
  rfl

theorem hasSum_original_l2_rough_actions
    (D : GlobalRoughAbelianForwardData)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((0:ℕ):ℝ))) :
    HasSum (fun j : ℕ => (2*Real.pi*(j+1 : ℕ))*
      ‖D.roughActionCoordinate ⟨j+1,by omega⟩ (nativeHillSource 0 q.val)‖)
      ((1/2:ℝ)*‖q‖^2) := by
  let p := nativeHillPhysicalSource 0 q.val q.property.1
  have hp0 : p.val.val 0=0 := by
    have h := nativeHillPhysicalSource_coefficients 0 q.val q.property.1 0
    simpa only [mul_zero,SpectralWeight.toCoeff_apply,q.property.2] using h
  have hs := hasSum_hillRealGapIntegrals_quadratic_even_l2 p hp0
  have hsrc : nativeHillSource 0 q.val=hillOriginalHminusSource p.val := by
    rw [hillOriginalHminusSource_eq_physical]
    exact nativeHillSource_eq_physical 0 q.val q.property.1
  have he (j : ℕ) : ‖D.roughActionCoordinate ⟨j+1,by omega⟩ (nativeHillSource 0 q.val)‖=
      hillRealGapIntegral p.val p.property.1 p.property.2 (j+1) 0 := by
    let n : ℕ+ := ⟨j+1,by omega⟩
    have h := congrArg norm (D.roughActionCoordinate_physical p n)
    rw [Complex.norm_real,Real.norm_of_nonneg (by
      simpa only [mul_zero] using hillRealGapIntegral_nonneg_even p.val p.property.1 p.property.2
        n n.pos 0)] at h
    simpa only [hsrc] using! h
  have hn : ‖p.val‖=‖q‖ := norm_nativeHillPhysicalSource_zero q.val q.property.1
  simpa only [he,hn] using hs

theorem hasSum_native_l2_rough_actions
    (D : GlobalRoughAbelianForwardData) (a : physicalRealDeletedSubmodule) :
    HasSum (fun j : ℕ => (2*Real.pi*(j+1 : ℕ))*
      ‖D.roughActionCoordinate ⟨j+1,by omega⟩
        (GlobalRoughAbelianForwardData.realNativeSource 1 (by norm_num) a)‖)
      ((1/2:ℝ)*‖a‖^2) := by
  let e := physicalRealMeanZeroWeightedIsometry (Weight.sobolev ((0:ℕ):ℝ))
    (Weight.sobolev_neg ((0:ℕ):ℝ))
  have hs := hasSum_original_l2_rough_actions D (e a)
  have hsrc := realNativeSource_original_l2 (e a)
  change GlobalRoughAbelianForwardData.realNativeSource 1 (by norm_num) (e.symm (e a))=_ at hsrc
  rw [e.symm_apply_apply] at hsrc
  simpa only [←hsrc,e.norm_map] using hs

end NLS.Articles.KdVKdV2Frequencies
