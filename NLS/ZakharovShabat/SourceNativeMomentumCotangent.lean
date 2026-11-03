import NLS.ZakharovShabat.SourceNativeMomentumActionDerivatives
import NLS.ZakharovShabat.SourceSobolevFourthActionDifferential
import NLS.ZakharovShabat.SourceWeightedHolomorphicRealGerm
import NLS.ZakharovShabat.SourceWeightedCotangentUniqueness
import NLS.ZakharovShabat.SourceSobolevMomentumDifferential
import NLS.ZakharovShabat.SourceMassActionDifferential

/-! # Physical momentum is the finite signed action cotangent

The actual momentum action factor and its independently calibrated open
partials determine the full cotangent at every finite-gap source. Closed
actions have zero full cotangent. Original weighted restriction is injective
on Hilbert cotangents, so the signed sum equals physical H₂ itself.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The complex H¹ and Hilbert inclusions retain exactly the same original
native coefficients in both components. -/
theorem sobolevSourceInclusion_fourthNativeComplexH1PairCLM
    (a : WeightedCoeffPair (sourceFrequencyWeight fourthSobolevSpectralWeight) 2) :
    sobolevSourceInclusion (fourthNativeComplexH1PairCLM a) = originalWeightedSourceCLM fourthSobolevSpectralWeight a := by
  apply (CoeffPair.toMax 2).injective
  apply Prod.ext <;> ext n
  · change (sobolevSourceInclusion (fourthNativeComplexH1PairCLM a)).fst n =
      (originalWeightedSourceCLM fourthSobolevSpectralWeight a).fst n
    rw [sobolevSourceInclusion_fst,originalWeightedSourceCLM_fst]
    change (hierarchySobolevToScalarDomain 1 le_rfl (fourthSobolevToH1 (fourthNativeFieldCLM a.fst))).val n = a.fst.val n
    rw [hierarchySobolevToScalarDomain_apply,fourthSobolevToH1_apply,fourthNativeFieldCLM_apply]
  · change (sobolevSourceInclusion (fourthNativeComplexH1PairCLM a)).snd n =
      (originalWeightedSourceCLM fourthSobolevSpectralWeight a).snd n
    rw [sobolevSourceInclusion_snd,originalWeightedSourceCLM_snd]
    change (hierarchySobolevToScalarDomain 1 le_rfl (fourthSobolevToH1 (fourthNativeFieldCLM a.snd))).val n = a.snd.val n
    rw [hierarchySobolevToScalarDomain_apply,fourthSobolevToH1_apply,fourthNativeFieldCLM_apply]

/-- The native complex momentum has the restriction of the independently
defined physical H¹ momentum cotangent. -/
theorem hasFDerivAt_sourceComplexNativeMomentum
    (a : WeightedCoeffPair (sourceFrequencyWeight fourthSobolevSpectralWeight) 2) :
    HasFDerivAt sourceComplexNativeMomentum
      ((sourceSobolevMomentumCotangent (fourthNativeComplexH1PairCLM a)).comp
        (originalWeightedSourceCLM fourthSobolevSpectralWeight)) a := by
  have hd := (hasFDerivAt_periodOneSobolevMomentum (fourthNativeComplexH1PairCLM a)).comp a
    fourthNativeComplexH1PairCLM.hasFDerivAt
  have he : sobolevSourceInclusion.comp fourthNativeComplexH1PairCLM =
      originalWeightedSourceCLM fourthSobolevSpectralWeight :=
    ContinuousLinearMap.ext sobolevSourceInclusion_fourthNativeComplexH1PairCLM
  change HasFDerivAt sourceComplexNativeMomentum _ a at hd
  rw [ContinuousLinearMap.comp_assoc,he] at hd
  exact hd

theorem sourceComplexNativeMomentum_fderiv_real (a h : NativeFourthSobolevSource) :
    fderiv ℂ sourceComplexNativeMomentum a.val h.val = fderiv ℝ sourceFourthSobolevMomentum a h := by
  have hd := ((analyticAt_sourceComplexNativeMomentum a.val).differentiableAt.hasFDerivAt.restrictScalars ℝ).comp a
    (weightedRealSourceSubmodule (p := 2) fourthSobolevSpectralWeight).subtypeL.hasFDerivAt
  change HasFDerivAt sourceFourthSobolevMomentum _ a at hd
  exact (congrArg (fun L => L h) hd.fderiv).symm

/-- Native physical mass is the independently defined Hilbert mass of the
same original two Fourier fields. -/
theorem sourceFourthSobolevMass_eq_sourceHilbertMass (a : NativeFourthSobolevSource) :
    sourceFourthSobolevMass a = sourceHilbertMass (originalWeightedRealSource fourthSobolevSpectralWeight a).val := by
  unfold sourceFourthSobolevMass
  rw [periodOneSobolevMass_eq_sourceHilbertMass]
  exact congrArg sourceHilbertMass (sobolevSourceInclusion_fourthNativeComplexH1PairCLM a.val)

namespace SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

/-- The actual physical momentum differential on all native real directions
is the finite signed original action sum, including every closed mode. -/
theorem sourceFourthSobolevMomentum_fderiv_eq_finite_sum
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (a : NativeFourthSobolevSource)
    (hf : originalWeightedRealSource fourthSobolevSpectralWeight a ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (S : Finset ℤ)
    (hS : ∀ n ∉ S, fderiv ℂ (sourceComplexAction (by simp) (by norm_num) n)
      (originalWeightedRealSource fourthSobolevSpectralWeight a).val = 0)
    (h : NativeFourthSobolevSource) :
    fderiv ℝ sourceFourthSobolevMomentum a h = ∑ n ∈ S, (2*(Real.pi:ℂ)*n)*
      ((fderiv ℂ (sourceComplexAction (by simp) (by norm_num) n)
        (originalWeightedRealSource fourthSobolevSpectralWeight a).val)
          (originalWeightedRealSource fourthSobolevSpectralWeight h).val) := by
  obtain ⟨V,T,H,hV,ha,hT,hmap,hH,hrec⟩ := D.exists_nativeMomentum_local_action_factor
    (D.originalWeightedRealMap fourthSobolevSpectralWeight a)
  have he : (fun b : NativeFourthSobolevSource => H (D.nativeFourthActions b)) =ᶠ[𝓝 a]
      sourceFourthSobolevMomentum := by
    filter_upwards [(D.originalWeightedRealMap_continuous fourthSobolevSpectralWeight).continuousAt.tendsto.eventually
      (hV.mem_nhds ha)] with b hb
    exact (hrec _ hb).trans (D.nativeMomentumBirkhoff_map b)
  have hd := ((hH _ (hmap ha)).differentiableAt.hasFDerivAt.restrictScalars ℝ).comp a
    (D.analyticAt_nativeFourthActions a).differentiableAt.hasFDerivAt
  change HasFDerivAt (fun b => H (D.nativeFourthActions b)) _ a at hd
  rw [← he.fderiv_eq,hd.fderiv]
  change (fderiv ℂ H (D.nativeFourthActions a)) (fderiv ℝ D.nativeFourthActions a h) = _
  rw [D.nativeFourthActions_fderiv_eq_finite_sum a S hS h,map_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [map_smul,smul_eq_mul]
  by_cases hn : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (originalWeightedRealSource fourthSobolevSpectralWeight a).val)
      (periodOnePotential_mem _) n = 0
  · have hz := sourceComplexAction_fderiv_eq_zero_of_closed_gap (by simp) (by norm_num)
      (originalWeightedRealSource fourthSobolevSpectralWeight a).val
      (originalWeightedRealSource fourthSobolevSpectralWeight a).property n
      (by simpa only [sourcePeriodicGapDisplacement_apply] using hn)
    simp only [hz,zero_apply,zero_mul,mul_zero]
  · rw [nativeFourthActions,D.nativeMomentum_action_factor_derivative a hf V hV ha H (hH _ (hmap ha)) hrec n hn,mul_comm]

/-- The entire complex physical native momentum cotangent is the weighted
restriction of the finite signed original action cotangent. -/
theorem sourceComplexNativeMomentum_fderiv_eq_finite_sum
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (a : NativeFourthSobolevSource)
    (hf : originalWeightedRealSource fourthSobolevSpectralWeight a ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (S : Finset ℤ)
    (hS : ∀ n ∉ S, fderiv ℂ (sourceComplexAction (by simp) (by norm_num) n)
      (originalWeightedRealSource fourthSobolevSpectralWeight a).val = 0) :
    fderiv ℂ sourceComplexNativeMomentum a.val =
      (∑ n ∈ S, (2*(Real.pi:ℂ)*n) • fderiv ℂ (sourceComplexAction (by simp) (by norm_num) n)
        (originalWeightedRealSource fourthSobolevSpectralWeight a).val).comp
          (originalWeightedSourceCLM fourthSobolevSpectralWeight) := by
  apply weightedSourceCLM_ext_real (by simp) fourthSobolevSpectralWeight
  intro h
  rw [sourceComplexNativeMomentum_fderiv_real,D.sourceFourthSobolevMomentum_fderiv_eq_finite_sum a hf S hS h]
  simp only [ContinuousLinearMap.comp_apply,sum_apply,smul_apply,smul_eq_mul,originalWeightedSourceCLM_real]

/-- The full signed original action sum is the actual physical momentum
cotangent itself, not merely a functional with the same value on actions. -/
theorem finite_action_sum_eq_physicalMomentumCotangent
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (a : NativeFourthSobolevSource)
    (hf : originalWeightedRealSource fourthSobolevSpectralWeight a ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (S : Finset ℤ)
    (hS : ∀ n ∉ S, fderiv ℂ (sourceComplexAction (by simp) (by norm_num) n)
      (originalWeightedRealSource fourthSobolevSpectralWeight a).val = 0) :
    (∑ n ∈ S, (2*(Real.pi:ℂ)*n) • fderiv ℂ (sourceComplexAction (by simp) (by norm_num) n)
      (originalWeightedRealSource fourthSobolevSpectralWeight a).val) =
        sourceSobolevMomentumCotangent (fourthNativeH1PairCLM a) := by
  apply sourceHilbertCotangent_eq_of_weighted_restriction fourthSobolevSpectralWeight
  exact (D.sourceComplexNativeMomentum_fderiv_eq_finite_sum a hf S hS).symm.trans
    (hasFDerivAt_sourceComplexNativeMomentum a.val).fderiv

end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
