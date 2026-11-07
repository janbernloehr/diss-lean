import NLS.Articles.KdVKdV2Frequencies.NativeFrequencySharpness
import NLS.Articles.KdVKdV2Frequencies.RoughFrequencySourceRecovery
import NLS.SequenceSpaces.LiteralPowerSharpness

/-! Corollary 1.5(ii): every strictly better literal frequency power
bound fails locally uniformly on the ORIGINAL real mean-zero H^s space.
The witnesses occur in EVERY source neighborhood and beyond EVERY cutoff. -/
noncomputable section
open Set Metric Complex NLS.KdV NLS.Articles.KdVConvexity
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies

def OriginalPhysicalFrequencySharpness (D : GlobalRoughAbelianForwardData)
    (G : ℕ+ → Coeff 1 → ℂ) : Prop :=
  ∀ (s : ℝ) (hs0 : -1<s) (_hs1 : s<0) (γ : ℝ), γ< -2*s-1 →
    ∀ (q₀ : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev s))
      (T : Set (physicalRealMeanZeroWeightedSubmodule (Weight.sobolev s))), IsOpen T → q₀∈T →
      ∀ M : ℝ, 0≤M → ∀ K : ℕ, ∃ q∈T, ∃ n : ℕ+, K≤(n:ℤ).natAbs ∧
        M<(n:ℝ)^(-γ)*‖roughKdVFrequency D G n (WeightedCoeff.sobolevInclusion hs0.le q.val)-
          8*(n:ℂ)^3*(Real.pi:ℂ)^3‖

theorem exists_original_physical_frequency_sharpness
    (D : GlobalRoughAbelianForwardData)
    (G : ℕ+ → Coeff 1 → ℂ) (V : Set (Coeff 1)) (hV : IsOpen V)
    (hCV : Coeff.nonnegativeLocus 1⊆V) (hG : ∀ n, AnalyticOnNhd ℂ (G n) V)
    (hrec : ∀ (P : PhysicalFrequencyPairChart D) (z : Coeff 2 × Coeff 2),
      z∈P.domain → z∈Coeff.realPairLocus 2 → ∀ n, G n (quadraticActionsExponent (q := 1) z)=P.correction n z) :
    OriginalPhysicalFrequencySharpness D G := by
  intro s hs0 hs1 γ hγ q₀ T hT hqT M hM K
  let t := s+1
  have ht : 0<t := by dsimp only [t];linarith
  have ht1 : t<1 := by dsimp only [t];linarith
  let e := physicalRealMeanZeroWeightedIsometry (Weight.sobolev s) (Weight.sobolev_neg s)
  let S := e ⁻¹' T
  have hS : IsOpen S := hT.preimage e.continuous
  have haS : e.symm q₀∈S := by change e (e.symm q₀)∈T;rwa [e.apply_symm_apply]
  let κ := normalizedSobolevWeakActionInclusion (2*t-1) (by linarith)
  let f := fun n a => G n (κ (nativeActionCoordinates D t ht.le a))
  have hsharp : ∀ r : ℝ, 2*t-1<r → ∀ B : ℝ, 0≤B → ∀ J : ℕ,
      ∃ a∈S, ∃ n : ℕ+, J≤(n:ℤ).natAbs ∧ B<Weight.sobolev r (n:ℤ)*‖f n a‖ := by
    intro r hr B hB J
    exact exists_native_frequency_sharpness D t ht ht1 G V hV hCV hG hrec
      (e.symm q₀) S hS haS r hr B hB J
  obtain ⟨a,ha,n,hn,hlarge⟩ := Coeff.exists_literal_power_frequency_lower_bound S f (2*t-1)
    (by linarith) (by linarith) hsharp γ (by dsimp only [t];linarith) M hM K
  have hs : GlobalRoughAbelianForwardData.realNativeSource t ht.le a=
      WeightedCoeff.sobolevInclusion hs0.le (e a).val := by
    have h := realNativeSource_original_weighted_coordinates s hs0.le (e a)
    change GlobalRoughAbelianForwardData.realNativeSource t ht.le (e.symm (e a))=_ at h
    rwa [e.symm_apply_apply] at h
  have hw := nativeActionCoordinates_weak D t ht.le a
  rw [hs] at hw
  have he : roughKdVFrequency D G n (WeightedCoeff.sobolevInclusion hs0.le (e a).val)-
      8*(n:ℂ)^3*(Real.pi:ℂ)^3=f n a := by
    rw [roughKdVFrequency,roughKdVFrequencyCorrection,← hw]
    dsimp only [f,κ]
    ring
  exact ⟨e a,ha,n,hn,by rwa [he]⟩

theorem GlobalRoughAbelianForwardData.corollary_1_5_ii (D : GlobalRoughAbelianForwardData) :
    ∃ V : Set (Coeff 1), ∃ G : ℕ+ → Coeff 1 → ℂ,
      IsOpen V ∧ Coeff.nonnegativeLocus 1⊆V ∧ (∀ n, AnalyticOnNhd ℂ (G n) V) ∧
      (∀ (B : PhysicalMiuraFrequencyChart) (q : PeriodOneHminusOne),
        IsRealPeriodOneHminusOne q → q.val 0=0 → q∈B.domain → ∀ n : ℕ+,
          roughKdVFrequency D G n q=(2*(n:ℂ)*Real.pi)^3+B.correction n q) ∧
      (∀ q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1:ℕ):ℝ)), ∀ n : ℕ+,
        roughKdVFrequency D G n (nativeHillSource 1 q.val)=
          (D.nativeSourceHierarchyFrequency 1 3 (by norm_num) q n:ℂ)) ∧
      OriginalPhysicalFrequencySharpness D G ∧
      ∀ (s : ℝ) (hs0 : -1<s) (_hs1 : s< -1/2)
        (q₀ : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev s))
        (T : Set (physicalRealMeanZeroWeightedSubmodule (Weight.sobolev s))), IsOpen T → q₀∈T →
        ∀ M : ℝ, 0≤M → ∀ K : ℕ, ∃ q∈T, ∃ n : ℕ+, K≤(n:ℤ).natAbs ∧
          M<‖roughKdVFrequency D G n (WeightedCoeff.sobolevInclusion hs0.le q.val)-
            8*(n:ℂ)^3*(Real.pi:ℂ)^3‖ := by
  obtain ⟨V,G,hV,hCV,hG,hrec⟩ := exists_global_physical_frequency_action_corrections D
  have hsharp := exists_original_physical_frequency_sharpness D G V hV hCV hG hrec
  refine ⟨V,G,hV,hCV,hG,?_,roughKdVFrequency_native_recovery D G hrec,hsharp,?_⟩
  · intro B q hr hm hq n
    rw [roughKdVFrequency,roughKdVFrequencyCorrection_eq_physical D G hrec B q hr hm hq n]
  · intro s hs0 hs1 q₀ T hT hqT M hM K
    have h := hsharp s hs0 (by linarith) 0 (by linarith) q₀ T hT hqT M hM K
    simpa only [neg_zero,Real.rpow_zero,one_mul] using h

end NLS.Articles.KdVKdV2Frequencies
