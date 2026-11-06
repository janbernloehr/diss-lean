import NLS.Articles.KdVKdV2Frequencies.NativeFiniteGapSpectralFrequencies
import NLS.Articles.KdVKdV2Frequencies.FiniteGapKdVMomentIdentity
import NLS.Articles.KdVKdV2Frequencies.FiniteGapKdV2MomentIdentity

/-! # Original physical Hamiltonian frequencies have the exact finite-gap moments

The intrinsic action derivatives of the independently defined physical
Hamiltonians are identified with the actual contour moments, rather than
with an auxiliary spectral definition. The selected gap is assumed open.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology NLS.KdV NLS.ZakharovShabat NLS.Fourier NLS.MKdV
open scoped ContDiff
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData

/-- The actual intrinsic physical kdv frequency has the source moment
formula on EVERY real mean-zero native finite-gap source at every open mode. -/
theorem native_finiteGap_kdv_frequency_moments (D : GlobalRoughAbelianForwardData)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1 : ℕ) : ℝ))) (S : Finset ℕ+)
    (hq : ∀ n : ℕ+, n ∉ S → hillRealGapHalfLength
      (nativeHillPhysicalSource 1 q.val q.property.1).val
      (nativeHillPhysicalSource 1 q.val q.property.1).property.1
      (nativeHillPhysicalSource 1 q.val q.property.1).property.2 n=0)
    (n : ℕ+)
    (hopen : hillRealGapHalfLength (nativeHillPhysicalSource 1 q.val q.property.1).val
      (nativeHillPhysicalSource 1 q.val q.property.1).property.1
      (nativeHillPhysicalSource 1 q.val q.property.1).property.2 n≠0) :
    (D.nativeSourceHierarchyFrequency 1 3 (by norm_num) q n : ℂ)-(2*(n : ℂ)*Real.pi)^3 =
      -12*∑' k : ℕ, (k : ℂ)*hillIntrinsicFrequencyMoment
        (nativeHillPhysicalSource 1 q.val q.property.1).val
        (nativeHillPhysicalSource 1 q.val q.property.1).property.1
        (nativeHillPhysicalSource 1 q.val q.property.1).property.2 n n.pos k 2 := by
  classical
  let Q := nativeHillContinuousSource 1 (by decide) q.val
  let p := nativeHillPhysicalSource 1 q.val q.property.1
  have hf := nativeHillContinuousSource_finiteGap_smooth 1 (by decide) q S hq
  have hp := nativeHillContinuousSource_periodic 1 (by decide) q.val
  have hr := nativeHillContinuousSource_real 1 (by decide) q.val q.property.1
  let pQ : RealPeriodOneHillPotential := ⟨hillContinuousCoefficients Q,
    hillContinuousCoefficients_mem_even Q hp,isRealHillPotential_hillContinuousCoefficients Q hr⟩
  have heq : pQ=p := Subtype.ext (hillContinuousCoefficients_nativeHillContinuousSource 1 (by decide) q.val q.property.1)
  have hmean : (∫ x in (0 : ℝ)..1, Q (x : AddCircle (2 : ℝ)))=0 := by
    have h := nativeHillContinuousSource_coefficient 1 (by decide) q.val 0
    simp only [periodOneCoefficient,←unitFourierCoefficient_eq_fourierCoeffOn,unitFourierCoefficient,
      mul_zero,neg_zero,wave_zero,mul_one] at h
    exact h.trans q.property.2
  let N := max (S.sup (fun k : ℕ+ => (k : ℕ))) (n : ℕ)
  have hSN (k : ℕ+) (hk : k∈S) : (k : ℕ)≤N :=
    (Finset.le_sup (f := fun j : ℕ+ => (j : ℕ)) hk).trans (le_max_left _ _)
  have hnN : (n : ℕ)≤N := le_max_right _ _
  have hc : ∀ (k : ℕ) (_hk : 1≤k), N<k → hillRealGapHalfLength p.val p.property.1 p.property.2 k=0 := by
    intro k hk hNk
    apply hq ⟨k,by omega⟩
    intro hmem
    have h := hSN ⟨k,by omega⟩ hmem
    change k≤N at h
    omega
  have hcQ : ∀ (k : ℕ) (_hk : 1≤k), N<k → hillRealGapHalfLength pQ.val pQ.property.1 pQ.property.2 k=0 := by
    simpa only [heq] using hc
  have hspec := kdvDirichletVelocitySum_eq_intrinsicMoment_tsum Q hr hf hp hmean n n.pos N hnN hcQ
  change kdvDirichletVelocitySum Q pQ n n.pos N-(2*(n : ℂ)*Real.pi)^3 = -12*∑' k : ℕ, (k : ℂ)*hillIntrinsicFrequencyMoment pQ.val pQ.property.1 pQ.property.2 n n.pos k 2 at hspec
  rw [heq] at hspec
  have he := D.native_finiteGap_kdv_frequency_eq_dirichlet q S hq N hSN n hopen
  change (D.nativeSourceHierarchyFrequency 1 3 (by norm_num) q n : ℂ) = kdvDirichletVelocitySum Q p n n.pos N at he
  rw [←he] at hspec
  exact hspec

/-- The actual intrinsic physical kdv2 frequency has the source moment
formula on EVERY real mean-zero native finite-gap source at every open mode. -/
theorem native_finiteGap_kdv2_frequency_moments (D : GlobalRoughAbelianForwardData)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((2 : ℕ) : ℝ))) (S : Finset ℕ+)
    (hq : ∀ n : ℕ+, n ∉ S → hillRealGapHalfLength
      (nativeHillPhysicalSource 2 q.val q.property.1).val
      (nativeHillPhysicalSource 2 q.val q.property.1).property.1
      (nativeHillPhysicalSource 2 q.val q.property.1).property.2 n=0)
    (n : ℕ+)
    (hopen : hillRealGapHalfLength (nativeHillPhysicalSource 2 q.val q.property.1).val
      (nativeHillPhysicalSource 2 q.val q.property.1).property.1
      (nativeHillPhysicalSource 2 q.val q.property.1).property.2 n≠0) :
    (D.nativeSourceHierarchyFrequency 2 5 (by norm_num) q n : ℂ)-
      20*(2*(n : ℂ)*Real.pi)*nativeMiuraMass 2 q.val-(2*(n : ℂ)*Real.pi)^5 =
      -160*(Real.pi : ℂ)^2*(∑' k : ℕ, (k : ℂ)^3*hillIntrinsicFrequencyMoment
        (nativeHillPhysicalSource 2 q.val q.property.1).val
        (nativeHillPhysicalSource 2 q.val q.property.1).property.1
        (nativeHillPhysicalSource 2 q.val q.property.1).property.2 n n.pos k 2)+
      80*(∑' k : ℕ, (k : ℂ)*hillIntrinsicFrequencyMoment
        (nativeHillPhysicalSource 2 q.val q.property.1).val
        (nativeHillPhysicalSource 2 q.val q.property.1).property.1
        (nativeHillPhysicalSource 2 q.val q.property.1).property.2 n n.pos k 4) := by
  classical
  let Q := nativeHillContinuousSource 2 (by decide) q.val
  let p := nativeHillPhysicalSource 2 q.val q.property.1
  have hf := nativeHillContinuousSource_finiteGap_smooth 2 (by decide) q S hq
  have hp := nativeHillContinuousSource_periodic 2 (by decide) q.val
  have hr := nativeHillContinuousSource_real 2 (by decide) q.val q.property.1
  let pQ : RealPeriodOneHillPotential := ⟨hillContinuousCoefficients Q,
    hillContinuousCoefficients_mem_even Q hp,isRealHillPotential_hillContinuousCoefficients Q hr⟩
  have heq : pQ=p := Subtype.ext (hillContinuousCoefficients_nativeHillContinuousSource 2 (by decide) q.val q.property.1)
  have hmean : (∫ x in (0 : ℝ)..1, Q (x : AddCircle (2 : ℝ)))=0 := by
    have h := nativeHillContinuousSource_coefficient 2 (by decide) q.val 0
    simp only [periodOneCoefficient,←unitFourierCoefficient_eq_fourierCoeffOn,unitFourierCoefficient,
      mul_zero,neg_zero,wave_zero,mul_one] at h
    exact h.trans q.property.2
  let N := max (S.sup (fun k : ℕ+ => (k : ℕ))) (n : ℕ)
  have hSN (k : ℕ+) (hk : k∈S) : (k : ℕ)≤N :=
    (Finset.le_sup (f := fun j : ℕ+ => (j : ℕ)) hk).trans (le_max_left _ _)
  have hnN : (n : ℕ)≤N := le_max_right _ _
  have hc : ∀ (k : ℕ) (_hk : 1≤k), N<k → hillRealGapHalfLength p.val p.property.1 p.property.2 k=0 := by
    intro k hk hNk
    apply hq ⟨k,by omega⟩
    intro hmem
    have h := hSN ⟨k,by omega⟩ hmem
    change k≤N at h
    omega
  have hcQ : ∀ (k : ℕ) (_hk : 1≤k), N<k → hillRealGapHalfLength pQ.val pQ.property.1 pQ.property.2 k=0 := by
    simpa only [heq] using hc
  have hspec := kdv2DirichletVelocitySum_eq_intrinsicMoment_tsum Q hr hf hp hmean n n.pos N hnN hcQ
  change kdv2DirichletVelocitySum Q pQ n n.pos N-20*(2*(n : ℂ)*Real.pi)*classicalQuadraticInvariant (fun x : ℝ => Q (x : AddCircle (2 : ℝ)))-
    (2*(n : ℂ)*Real.pi)^5 =
    -160*(Real.pi : ℂ)^2*(∑' k : ℕ, (k : ℂ)^3*hillIntrinsicFrequencyMoment pQ.val pQ.property.1 pQ.property.2 n n.pos k 2)+
      80*(∑' k : ℕ, (k : ℂ)*hillIntrinsicFrequencyMoment pQ.val pQ.property.1 pQ.property.2 n n.pos k 4) at hspec
  rw [heq] at hspec
  have he := D.native_finiteGap_kdv2_frequency_eq_dirichlet q S hq N hSN n hopen
  change (D.nativeSourceHierarchyFrequency 2 5 (by norm_num) q n : ℂ) = kdv2DirichletVelocitySum Q p n n.pos N at he
  rw [←he] at hspec
  have hm : nativeMiuraMass 2 q.val = classicalQuadraticInvariant (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) := by
    rw [nativeMiuraMass_eq_classical 2 q.val _ hf hp (fun k =>
      (nativeHillContinuousSource_coefficient 2 (by decide) q.val k).symm),
      classicalMiuraHillHamiltonian_one _ hf hp]
    rfl
  rw [←hm] at hspec
  exact hspec

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
