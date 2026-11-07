import NLS.KdV.PhysicalNativeFrequencyParameterization
import NLS.KdV.PhysicalUniformFrequencyDecay

/-! Sharp uniform little-o of the FULL corrected actual frequency in
the original native H^(t-1) norm for 0<t<2/3. Original action-topology
transfer and the weak t=0 endpoint remain separate obligations. -/
noncomputable section
open Set Complex NLS.KdV
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies

theorem theorem_1_2_iii_native_uniform_frequency_dependency
    (t : ℝ) (ht : 0<t) (ht1 : t<2/3) (q : WeightedCoeff (Weight.sobolev (t-1)) 2)
    (hq : IsRealPeriodOneHminusOne (periodOneSobolevImageInclusion t ht.le q)) :
    ∃ A : PhysicalNativeFrequencyParameterization t ht.le, q∈A.domain ∧
      ∃ T : Set (WeightedCoeff (Weight.sobolev (t-1)) 2), IsOpen T ∧ q∈T ∧ T⊆A.domain ∧
        ∀ ε > (0:ℝ), ∃ K : ℕ, ∀ a∈T, ∀ n : ℕ+, K≤(n:ℤ).natAbs →
          Weight.sobolev (3*t-1) (n:ℤ)*‖A.renormalizedCorrection n a‖≤ε := by
  obtain ⟨A,hqA⟩ := exists_physicalNativeFrequencyParameterization t ht.le q hq
  exact ⟨A,hqA,A.exists_uniform_renormalized_frequency_decay ht ht1 q hqA hq⟩

end NLS.Articles.KdVKdV2Frequencies
