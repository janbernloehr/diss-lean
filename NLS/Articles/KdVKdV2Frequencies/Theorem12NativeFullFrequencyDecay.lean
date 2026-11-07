import NLS.KdV.PhysicalHighRegularityFrequencyDecay

/-! The FULL corrected physical-frequency dependency of Theorem
1.2(iii), in the ORIGINAL native H^(t-1) norm. The uniform complex
bound and pointwise little-o are explicit; full source-uniform little-o
and original action-space transfer remain further obligations. -/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.KdV
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies

theorem theorem_1_2_iii_native_full_frequency_dependency
    (t : ℝ) (ht : 0≤t) (ht1 : t≤2/3)
    (q : WeightedCoeff (Weight.sobolev (t-1)) 2)
    (hq : IsRealPeriodOneHminusOne (periodOneSobolevImageInclusion t ht q)) :
    ∃ A : PhysicalNativeFrequencyParameterization t ht, q∈A.domain ∧ A.HasSharpFrequencyDecay q := by
  obtain ⟨A,hqA⟩ := exists_physicalNativeFrequencyParameterization t ht q hq
  exact ⟨A,hqA,A.exists_sharp_frequency_decay ht1 q hqA hq⟩

theorem theorem_1_2_iii_native_highRegularity_dependency
    (s : ℝ) (hs : -1/3≤s)
    (q : WeightedCoeff (Weight.sobolev s) 2)
    (hq : IsRealPeriodOneHminusOne (WeightedCoeff.sobolevInclusion (by linarith : -1≤s) q)) :
    let J := WeightedCoeff.sobolevInclusion (p := 2) (by linarith : -1≤s)
    ∃ B : PhysicalMiuraFrequencyChart, ∃ T : Set (WeightedCoeff (Weight.sobolev s) 2),
      IsOpen T ∧ q∈T ∧ T⊆J ⁻¹' B.domain ∧ ∃ K : ℕ, ∃ M : ℝ, 0≤M ∧
        ∀ a∈T, ∀ n : ℕ+, K≤(n:ℤ).natAbs →
          (Weight.sobolev 1 (n:ℤ)*‖B.correction n (J a)+
            12*NLS.ZakharovShabat.sourceComplexHigherAction (by norm_num) (by norm_num) (n:ℤ) 1
              (hillMiuraDiagonal (B.psi.miura.lift (J a)))‖≤M) ∧
          ∀ p : RealPeriodOneHillPotential, J a=hillOriginalHminusSource p.val →
            Weight.sobolev 1 (n:ℤ)*‖B.correction n (hillOriginalHminusSource p.val)+
              6*(hillRealGapIntegral p.val p.property.1 p.property.2 (n:ℕ) 0 : ℂ)‖≤M :=
  exists_physical_highRegularity_frequency_decay s hs q hq

end NLS.Articles.KdVKdV2Frequencies
