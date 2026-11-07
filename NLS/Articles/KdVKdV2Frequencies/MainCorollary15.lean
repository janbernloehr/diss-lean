import NLS.Articles.KdVKdV2Frequencies.Corollary15Decay
import NLS.Articles.KdVKdV2Frequencies.Corollary15Sharpness
import NLS.Articles.KdVKdV2Frequencies.Corollary15BoundedL2

/-! COMPLETE Corollary 1.5: ONE actual physical frequency family satisfies
all three clauses in the ORIGINAL source norms and normalizations. -/
noncomputable section
open Set Complex Filter Topology NLS.KdV NLS.Articles.KdVConvexity
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies

def OriginalPhysicalFrequencyDecay (D : GlobalRoughAbelianForwardData)
    (G : ℕ+ → Coeff 1 → ℂ) : Prop :=
  ∀ (s : ℝ) (hs0 : -1≤s) (_hs1 : s≤0)
    (q₀ : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev s)),
    ∃ T : Set (physicalRealMeanZeroWeightedSubmodule (Weight.sobolev s)), IsOpen T ∧ q₀∈T ∧
      ∃ B : ℝ, 0≤B ∧
        (∀ q∈T, ∀ n : ℕ+, (n:ℝ)^(2*s+1)*
          ‖roughKdVFrequency D G n (WeightedCoeff.sobolevInclusion hs0 q.val)-
            8*(n:ℂ)^3*(Real.pi:ℂ)^3‖≤B) ∧
        (s<0 → ∀ q∈T, Tendsto (fun m : ℕ => (m+1:ℝ)^(2*s+1)*
          ‖roughKdVFrequency D G ⟨m+1,by omega⟩ (WeightedCoeff.sobolevInclusion hs0 q.val)-
            8*((m+1:ℕ):ℂ)^3*(Real.pi:ℂ)^3‖) atTop (𝓝 0))

theorem roughKdVFrequency_eq_of_physical_calibration
    (D : GlobalRoughAbelianForwardData) (G H : ℕ+ → Coeff 1 → ℂ)
    (hG : ∀ (B : PhysicalMiuraFrequencyChart) (q : PeriodOneHminusOne),
      IsRealPeriodOneHminusOne q → q.val 0=0 → q∈B.domain → ∀ n : ℕ+,
        roughKdVFrequency D G n q=(2*(n:ℂ)*Real.pi)^3+B.correction n q)
    (hH : ∀ (B : PhysicalMiuraFrequencyChart) (q : PeriodOneHminusOne),
      IsRealPeriodOneHminusOne q → q.val 0=0 → q∈B.domain → ∀ n : ℕ+,
        roughKdVFrequency D H n q=(2*(n:ℂ)*Real.pi)^3+B.correction n q)
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (hm : q.val 0=0) (n : ℕ+) :
    roughKdVFrequency D G n q=roughKdVFrequency D H n q := by
  obtain ⟨B,hqB,_⟩ := exists_physicalMiuraFrequencyChart q hr 0
  exact (hG B q hr hm hqB n).trans (hH B q hr hm hqB n).symm

theorem GlobalRoughAbelianForwardData.corollary_1_5 (D : GlobalRoughAbelianForwardData) :
    ∃ V : Set (Coeff 1), ∃ G : ℕ+ → Coeff 1 → ℂ,
      IsOpen V ∧ Coeff.nonnegativeLocus 1⊆V ∧ (∀ n, AnalyticOnNhd ℂ (G n) V) ∧
      (∀ (B : PhysicalMiuraFrequencyChart) (q : PeriodOneHminusOne),
        IsRealPeriodOneHminusOne q → q.val 0=0 → q∈B.domain → ∀ n : ℕ+,
          roughKdVFrequency D G n q=(2*(n:ℂ)*Real.pi)^3+B.correction n q) ∧
      (∀ q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1:ℕ):ℝ)), ∀ n : ℕ+,
        roughKdVFrequency D G n (nativeHillSource 1 q.val)=
          (D.nativeSourceHierarchyFrequency 1 3 (by norm_num) q n:ℂ)) ∧
      OriginalPhysicalFrequencyDecay D G ∧ OriginalPhysicalFrequencySharpness D G ∧
      OriginalPhysicalFrequencyBoundedL2 D G ∧
      ∀ (s : ℝ) (hs0 : -1<s) (_hs1 : s< -1/2)
        (q₀ : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev s))
        (T : Set (physicalRealMeanZeroWeightedSubmodule (Weight.sobolev s))), IsOpen T → q₀∈T →
        ∀ M : ℝ, 0≤M → ∀ K : ℕ, ∃ q∈T, ∃ n : ℕ+, K≤(n:ℤ).natAbs ∧
          M<‖roughKdVFrequency D G n (WeightedCoeff.sobolevInclusion hs0.le q.val)-
            8*(n:ℂ)^3*(Real.pi:ℂ)^3‖ := by
  obtain ⟨V,G,hV,hCV,hG,hcal,hnative,hdec⟩ := D.corollary_1_5_i
  obtain ⟨_V₂,G₂,_hV₂,_hCV₂,_hG₂,hcal₂,_hnative₂,hsharp₂,_⟩ := D.corollary_1_5_ii
  obtain ⟨_V₃,G₃,_hV₃,_hCV₃,_hG₃,hcal₃,_hnative₃,hbound₃⟩ := D.corollary_1_5_iii
  have hsharp : OriginalPhysicalFrequencySharpness D G := by
    intro s hs0 hs1 γ hγ q₀ T hT hqT M hM K
    obtain ⟨q,hq,n,hn,hlarge⟩ := hsharp₂ s hs0 hs1 γ hγ q₀ T hT hqT M hM K
    have hr : IsRealPeriodOneHminusOne (WeightedCoeff.sobolevInclusion hs0.le q.val) := by
      intro j
      simpa only [WeightedCoeff.sobolevInclusion_apply] using q.property.1 j
    have hm : (WeightedCoeff.sobolevInclusion hs0.le q.val).val 0=0 :=
      (WeightedCoeff.sobolevInclusion_apply _ _ 0).trans q.property.2
    rw [roughKdVFrequency_eq_of_physical_calibration D G₂ G hcal₂ hcal _ hr hm n] at hlarge
    exact ⟨q,hq,n,hn,hlarge⟩
  have hbound : OriginalPhysicalFrequencyBoundedL2 D G := by
    intro S hS
    obtain ⟨B,hB,hb⟩ := hbound₃ S hS
    refine ⟨B,hB,?_⟩
    intro q hq n
    have hr := nativeHillSource_real 0 q.val q.property.1
    have hm : (nativeHillSource 0 q.val).val 0=0 :=
      (nativeHillSource_apply 0 q.val 0).trans q.property.2
    rw [←roughKdVFrequency_eq_of_physical_calibration D G₃ G hcal₃ hcal _ hr hm n]
    exact hb q hq n
  refine ⟨V,G,hV,hCV,hG,hcal,hnative,hdec,hsharp,hbound,?_⟩
  intro s hs0 hs1 q₀ T hT hqT M hM K
  have h := hsharp s hs0 (by linarith) 0 (by linarith) q₀ T hT hqT M hM K
  simpa only [neg_zero,Real.rpow_zero,one_mul] using h

end NLS.Articles.KdVKdV2Frequencies
