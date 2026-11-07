import NLS.Articles.KdVKdV2Frequencies.RoughFrequencySourceRecovery
import NLS.Articles.KdVKdV2Frequencies.UncorrectedSobolevActionFrequencyDecay
import NLS.SequenceSpaces.PositiveSobolevPowerComparison

/-! Corollary 1.5(i): the actual physical frequency on the ORIGINAL
real mean-zero H^s source for every -1≤s≤0. One local constant controls
ALL positive labels. The little-o limit is pointwise for s<0; s=0 has
the stated O(1/n) bound. Sharpness and bounded-L2 uniformity are separate. -/
noncomputable section
open Set Complex Filter Topology NLS.KdV NLS.Articles.KdVConvexity
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies

theorem GlobalRoughAbelianForwardData.corollary_1_5_i (D : GlobalRoughAbelianForwardData) :
    ∃ V : Set (Coeff 1), ∃ G : ℕ+ → Coeff 1 → ℂ,
      IsOpen V ∧ Coeff.nonnegativeLocus 1⊆V ∧ (∀ n, AnalyticOnNhd ℂ (G n) V) ∧
      (∀ (B : PhysicalMiuraFrequencyChart) (q : PeriodOneHminusOne),
        IsRealPeriodOneHminusOne q → q.val 0=0 → q∈B.domain → ∀ n : ℕ+,
          roughKdVFrequency D G n q=(2*(n:ℂ)*Real.pi)^3+B.correction n q) ∧
      (∀ q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1:ℕ):ℝ)), ∀ n : ℕ+,
        roughKdVFrequency D G n (nativeHillSource 1 q.val)=
          (D.nativeSourceHierarchyFrequency 1 3 (by norm_num) q n:ℂ)) ∧
      ∀ (s : ℝ) (hs0 : -1≤s) (_hs1 : s≤0)
        (q₀ : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev s)),
        ∃ T : Set (physicalRealMeanZeroWeightedSubmodule (Weight.sobolev s)), IsOpen T ∧ q₀∈T ∧
          ∃ B : ℝ, 0≤B ∧
            (∀ q∈T, ∀ n : ℕ+, (n:ℝ)^(2*s+1)*
              ‖roughKdVFrequency D G n (WeightedCoeff.sobolevInclusion hs0 q.val)-
                8*(n:ℂ)^3*(Real.pi:ℂ)^3‖≤B) ∧
            (s<0 → ∀ q∈T, Tendsto (fun m : ℕ => (m+1:ℝ)^(2*s+1)*
              ‖roughKdVFrequency D G ⟨m+1,by omega⟩ (WeightedCoeff.sobolevInclusion hs0 q.val)-
                8*((m+1:ℕ):ℂ)^3*(Real.pi:ℂ)^3‖) atTop (𝓝 0)) := by
  obtain ⟨V,G,hV,hCV,hG,hrec⟩ := exists_global_physical_frequency_action_corrections D
  refine ⟨V,G,hV,hCV,hG,?_,roughKdVFrequency_native_recovery D G hrec,?_⟩
  · intro B q hr hm hq n
    rw [roughKdVFrequency,roughKdVFrequencyCorrection_eq_physical D G hrec B q hr hm hq n]
  intro s hs0 hs1 q₀
  let t := s+1
  have ht : 0≤t := by dsimp only [t];linarith
  have ht1 : t≤1 := by dsimp only [t];linarith
  let e := physicalRealMeanZeroWeightedIsometry (Weight.sobolev s) (Weight.sobolev_neg s)
  let N := fun q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev s) =>
    nativeActionCoordinates D t ht (e.symm q)
  have hN : Continuous N := (continuous_nativeActionCoordinates D t ht).comp e.symm.continuous
  have ha₀ : N q₀∈Coeff.nonnegativeLocus 1 := nativeActionCoordinates_nonnegative D t ht (e.symm q₀)
  obtain ⟨U,hU,haU,_,M,hM,hb,hd⟩ := exists_uncorrected_sobolev_action_frequency_decay D t ht ht1
    G V hV hCV hG hrec (N q₀) ha₀
  let κ := normalizedSobolevWeakActionInclusion (2*t-1) (by linarith)
  have hα : 2*t-1=2*s+1 := by dsimp only [t];ring
  have hr0 : -1≤2*t-1 := by linarith
  have hr1 : 2*t-1≤1 := by linarith
  have heq (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev s)) (n : ℕ+) :
      roughKdVFrequency D G n (WeightedCoeff.sobolevInclusion hs0 q.val)-8*(n:ℂ)^3*(Real.pi:ℂ)^3=
        G n (κ (N q)) := by
    have h := nativeActionCoordinates_weak D t ht (e.symm q)
    rw [realNativeSource_original_weighted_coordinates s hs0 q] at h
    rw [roughKdVFrequency,roughKdVFrequencyCorrection,← h]
    ring
  refine ⟨N ⁻¹' U,hU.preimage hN,haU,2*M,mul_nonneg (by norm_num) hM,?_,?_⟩
  · intro q hq n
    rw [heq,← hα]
    have h := mul_le_mul_of_nonneg_right (Coeff.positive_power_le_two_sobolev (2*t-1) hr0 hr1 n)
      (norm_nonneg (G n (κ (N q))))
    exact h.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hb (N q) hq n) (by norm_num : (0:ℝ)≤2))
  · intro hslt q hq
    have htlt : t<1 := by dsimp only [t];linarith
    have h := Coeff.tendsto_positive_power_of_sobolev (2*t-1) hr0 hr1
      (fun n : ℕ+ => G n (κ (N q))) (hd htlt (N q) hq)
    have heq' (m : ℕ) :
        roughKdVFrequency D G ⟨m+1,by omega⟩ (WeightedCoeff.sobolevInclusion hs0 q.val)-
          8*((m+1:ℕ):ℂ)^3*(Real.pi:ℂ)^3=G ⟨m+1,by omega⟩ (κ (N q)) :=
      heq q ⟨m+1,by omega⟩
    simp_rw [heq']
    simpa only [hα] using h

end NLS.Articles.KdVKdV2Frequencies
