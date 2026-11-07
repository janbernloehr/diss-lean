import NLS.KdV.PhysicalFrequencyDecayPullback
import NLS.KdV.PhysicalNativeFrequencyParameterization

/-! The FULL corrected physical frequency is O(1/n) at every native
Sobolev order s>=-1/3. Pullback along the literal coefficient inclusion
preserves the ORIGINAL stronger source norm and SAME physical chart. -/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV

theorem exists_physical_highRegularity_frequency_decay
    (s : ℝ) (hs : -1/3≤s)
    (q : WeightedCoeff (Weight.sobolev s) 2)
    (hq : IsRealPeriodOneHminusOne (WeightedCoeff.sobolevInclusion (by linarith : -1≤s) q)) :
    let J := WeightedCoeff.sobolevInclusion (p := 2) (by linarith : -1≤s)
    ∃ B : PhysicalMiuraFrequencyChart, ∃ T : Set (WeightedCoeff (Weight.sobolev s) 2),
      IsOpen T ∧ q∈T ∧ T⊆J ⁻¹' B.domain ∧ ∃ K : ℕ, ∃ M : ℝ, 0≤M ∧
        ∀ a∈T, ∀ n : ℕ+, K≤(n:ℤ).natAbs →
          (Weight.sobolev 1 (n:ℤ)*‖B.correction n (J a)+
            12*sourceComplexHigherAction (by norm_num) (by norm_num) (n:ℤ) 1
              (hillMiuraDiagonal (B.psi.miura.lift (J a)))‖≤M) ∧
          ∀ p : RealPeriodOneHillPotential, J a=hillOriginalHminusSource p.val →
            Weight.sobolev 1 (n:ℤ)*‖B.correction n (hillOriginalHminusSource p.val)+
              6*(hillRealGapIntegral p.val p.property.1 p.property.2 (n:ℕ) 0 : ℂ)‖≤M := by
  intro J
  let t₀ : ℝ := 2/3
  have ht₀ : 0≤t₀ := by norm_num [t₀]
  let I : WeightedCoeff (Weight.sobolev s) 2 →L[ℂ] WeightedCoeff (Weight.sobolev (t₀-1)) 2 :=
    WeightedCoeff.sobolevInclusion (by dsimp only [t₀];linarith)
  have hJ (a : WeightedCoeff (Weight.sobolev s) 2) : periodOneSobolevImageInclusion t₀ ht₀ (I a)=J a := by
    apply Subtype.ext
    funext n
    simp only [periodOneSobolevImageInclusion_apply,I,J,WeightedCoeff.sobolevInclusion_apply]
  have hq' : IsRealPeriodOneHminusOne (periodOneSobolevImageInclusion t₀ ht₀ (I q)) := by
    rw [hJ]
    exact hq
  obtain ⟨A,hqA⟩ := exists_physicalNativeFrequencyParameterization t₀ ht₀ (I q) hq'
  have hsharp := A.exists_sharp_frequency_decay le_rfl (I q) hqA hq'
  exact A.exists_inverse_index_decay_of_pullback I J hJ q hsharp (by norm_num [t₀])

end NLS.KdV
