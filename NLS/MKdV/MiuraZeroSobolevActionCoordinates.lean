import NLS.MKdV.MiuraNativeHamiltonianFrequencies
import NLS.MKdV.MiuraJointFiberSobolevRegularity

/-! # The native H⁰ data retain the literal original L² coefficients -/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

theorem miuraPhysicalSobolevL2SourceInclusion_zero_surjective :
    Function.Surjective (miuraPhysicalSobolevL2SourceInclusion 0) := by
  intro b
  apply exists_miuraSobolev_representative_of_mem 0 b
  simpa only [Nat.cast_zero,Weight.sobolev_apply,Real.rpow_zero,Complex.ofReal_one,one_mul] using lp.memℓp b.val

theorem miuraNativeActionMeanEquiv_zero_single (n : ℤ) :
    miuraNativeActionMeanEquiv 0 (WeightedCoeff.single (p := 1) (miuraSpectralActionWeight 0) n 1,0) =
      (WeightedCoeff.single (p := 1) (Weight.sobolev 1) n 1,0) := by
  apply Prod.ext
  · apply Subtype.ext
    funext k
    rw [miuraNativeActionMeanEquiv_fst,WeightedCoeff.single_val,WeightedCoeff.single_val]
    simp only [miuraSpectralActionWeight,Nat.mul_zero,Nat.zero_add,Nat.cast_one]
    exact mul_div_cancel_left₀ _ ((Weight.sobolev 1).complex_ne_zero k)
  · exact miuraNativeActionMeanEquiv_mean 0 _

theorem miuraNativeActionMeanEquiv_zero_symm_single (n : ℤ) :
    (miuraNativeActionMeanEquiv 0).symm (WeightedCoeff.single (p := 1) (Weight.sobolev 1) n 1,0) =
      (WeightedCoeff.single (p := 1) (miuraSpectralActionWeight 0) n 1,0) := by
  rw [← miuraNativeActionMeanEquiv_zero_single,ContinuousLinearEquiv.symm_apply_apply]

theorem miuraNativeActionMean_zero_of_L2_representative (a : MiuraRealSobolevSource 0) (b : MiuraRealL2)
    (hb : miuraPhysicalSobolevL2SourceInclusion 0 a = b) :
    (miuraNativeActionMeanEquiv 0).symm (miuraRealL2ActionMeanMap b) = miuraNativeActionMeanMap 0 a.val := by
  have he := miuraNormalizedNativeActionMeanMap_zero_L2 a
  rw [hb] at he
  change miuraNativeActionMeanEquiv 0 (miuraNativeActionMeanMap 0 a.val) = miuraRealL2ActionMeanMap b at he
  rw [← he,ContinuousLinearEquiv.symm_apply_apply]

theorem miuraSpectralHillHamiltonian_zero_of_L2_representative (a : MiuraRealSobolevSource 0) (b : MiuraRealL2)
    (hb : miuraPhysicalSobolevL2SourceInclusion 0 a = b) :
    miuraSpectralHillHamiltonian 0 a.val = miuraL2Mass b.val := by
  rw [miuraSpectralHillHamiltonian_eq_native,nativeMiuraHillHamiltonian_zero_eq_L2Mass]
  have he := congrArg Subtype.val hb
  change hierarchySobolevJetL2 0 0 le_rfl a.val = b.val at he
  rw [he]

end NLS.MKdV
