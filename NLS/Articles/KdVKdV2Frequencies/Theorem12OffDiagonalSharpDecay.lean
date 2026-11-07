import NLS.KdV.PhysicalSharpOffDiagonalDecay

/-! The off-diagonal dependency of Theorem 1.2(iii), in the ORIGINAL
native source order s. The full frequency and uniform little-o clause
still require the sharp diagonal expansion and action-space transfer. -/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology NLS.KdV
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies

theorem theorem_1_2_iii_offDiagonal_sharp_dependency
    (s : ℝ) (hs0 : -1≤s) (hs1 : s≤ -1/3)
    (q : WeightedCoeff (Weight.sobolev s) 2)
    (hq : IsRealPeriodOneHminusOne (WeightedCoeff.sobolevInclusion hs0 q)) :
    ∃ B : PhysicalMiuraFrequencyChart,
      ∃ T : Set (WeightedCoeff (Weight.sobolev s) 2), IsOpen T ∧ q∈T ∧
        T⊆WeightedCoeff.sobolevInclusion hs0 ⁻¹' B.domain ∧
        ∃ K : ℝ, 0≤K ∧
          (∀ a∈T, ∀ n : ℕ+, Weight.sobolev (3*s+2) (n : ℤ)*
            ‖B.offDiagonalCorrection n (WeightedCoeff.sobolevInclusion hs0 a)‖≤K) ∧
          (s< -1/3 → ∀ a∈T,
            Tendsto (fun n : ℕ => Weight.sobolev (3*s+2) ((n+1 : ℕ) : ℤ)*
              ‖B.offDiagonalCorrection ⟨n+1,by omega⟩ (WeightedCoeff.sobolevInclusion hs0 a)‖)
              atTop (𝓝 0)) := by
  obtain ⟨t,rfl⟩ : ∃ t : ℝ, s=t-1 := ⟨s+1,by ring⟩
  have ht : 0≤t := by linarith
  have ht1 : t≤2/3 := by linarith
  have hq' : IsRealPeriodOneHminusOne (periodOneSobolevImageInclusion t ht q) := hq
  have H := exists_physicalMiuraFrequencyChart_with_sharp_offDiagonal_decay t ht ht1 q hq'
  have he : t-1< -1/3 ↔ t<2/3 := by constructor <;> intro h <;> linarith
  simpa only [periodOneSobolevImageInclusion,show 3*(t-1)+2=3*t-1 by ring,he] using H

end NLS.Articles.KdVKdV2Frequencies
