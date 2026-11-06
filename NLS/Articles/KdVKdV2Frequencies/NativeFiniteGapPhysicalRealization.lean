import NLS.Articles.KdVKdV2Frequencies.FiniteGapPhysicalHamiltonianVectors
import NLS.KdV.HillHminusFiniteGapSmooth
import NLS.KdV.HillHminusOriginalLabels

/-! # Actual finite-gap sources have the printed smooth Hamiltonian vectors

Spectral finite-gap regularity supplies the smooth physical representative;
it is not a hypothesis. Thus the independent physical KdV and KdV2 vector
identities apply to every original real mean-zero native finite-gap source.
-/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.KdV NLS.ZakharovShabat NLS.Fourier
open scoped ContDiff
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData

/-- Actual spectral finite-gap native sources admit smooth physical Fourier
realizations, with the literal original unit-period coefficients. -/
theorem native_finiteGap_exists_smooth (m : ℕ)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (m : ℝ))) (S : Finset ℕ+)
    (hq : ∀ n : ℕ+, n ∉ S → hillRealGapHalfLength
      (nativeHillPhysicalSource m q.val q.property.1).val
      (nativeHillPhysicalSource m q.val q.property.1).property.1
      (nativeHillPhysicalSource m q.val q.property.1).property.2 n = 0) :
    ∃ f : ℝ → ℂ, ContDiff ℝ ∞ f ∧ Function.Periodic f 1 ∧
      ∀ n : ℤ, q.val.val n=periodOneCoefficient f n := by
  classical
  let N := S.sup (fun n : ℕ+ => (n : ℕ))+1
  let p := nativeHillPhysicalSource m q.val q.property.1
  have hp : nativeHillSource m q.val=hillOriginalHminusSource p.val := by
    rw [hillOriginalHminusSource_eq_physical]
    exact nativeHillSource_eq_physical m q.val q.property.1
  have hc : ∀ n : ℕ, N≤n → hillHminusRealLabels (nativeHillSource m q.val)
      (nativeHillSource_real m q.val q.property.1) (2*n) =
        hillHminusRealLabels (nativeHillSource m q.val)
          (nativeHillSource_real m q.val q.property.1) (2*n-1) := by
    intro n hn
    have hnpos : 0<n := by dsimp only [N] at hn; omega
    have hnS : (⟨n,hnpos⟩ : ℕ+) ∉ S := by
      intro his
      have he := Finset.le_sup (f := fun j : ℕ+ => (j : ℕ)) his
      dsimp only [N] at hn
      change n ≤ S.sup (fun j : ℕ+ => (j : ℕ)) at he
      omega
    have hg := hq ⟨n,hnpos⟩ hnS
    change (hillRealLabels p.val p.property.1 p.property.2 (2*n)-
      hillRealLabels p.val p.property.1 p.property.2 (2*n-1))/2=0 at hg
    have hl : hillRealLabels p.val p.property.1 p.property.2 (2*n) =
        hillRealLabels p.val p.property.1 p.property.2 (2*n-1) := by linarith
    rw [←hillHminusRealLabels_original_source p] at hl
    simpa only [←hp] using hl
  simpa only [nativeHillSource_apply] using
    hillHminus_real_finiteGap_exists_smooth (nativeHillSource m q.val)
      (nativeHillSource_real m q.val q.property.1) N (by dsimp only [N]; omega) hc

/-- Every ACTUAL native KdV finite-gap source has the printed third-order
Hamiltonian vector, with no extra smoothness assumption. -/
theorem native_finiteGap_kdv_physical_vector (D : GlobalRoughAbelianForwardData)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1 : ℕ) : ℝ))) (S : Finset ℕ+)
    (hq : ∀ n : ℕ+, n ∉ S → hillRealGapHalfLength
      (nativeHillPhysicalSource 1 q.val q.property.1).val
      (nativeHillPhysicalSource 1 q.val q.property.1).property.1
      (nativeHillPhysicalSource 1 q.val q.property.1).property.2 n = 0) :
    ∃ f : ℝ → ℂ, ContDiff ℝ ∞ f ∧ Function.Periodic f 1 ∧
      (∀ n : ℤ, q.val.val n=periodOneCoefficient f n) ∧ ∀ k : ℤ,
        (NLS.Poisson.gardnerHamiltonianVector (D.finiteGapActionCombination 1 3 (by norm_num) q S)
          (nativeHillSource 1 q.val)).val k = periodOneCoefficient (kdvRHS f) k := by
  obtain ⟨f,hf,hp,hc⟩ := native_finiteGap_exists_smooth 1 q S hq
  exact ⟨f,hf,hp,hc,D.finiteGapActionCombination_kdv_vector q S hq f hf hp hc⟩

/-- The same unconditional physical realization for every actual native
KdV2 finite-gap source, retaining all printed fifth-order coefficients. -/
theorem native_finiteGap_kdv2_physical_vector (D : GlobalRoughAbelianForwardData)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((2 : ℕ) : ℝ))) (S : Finset ℕ+)
    (hq : ∀ n : ℕ+, n ∉ S → hillRealGapHalfLength
      (nativeHillPhysicalSource 2 q.val q.property.1).val
      (nativeHillPhysicalSource 2 q.val q.property.1).property.1
      (nativeHillPhysicalSource 2 q.val q.property.1).property.2 n = 0) :
    ∃ f : ℝ → ℂ, ContDiff ℝ ∞ f ∧ Function.Periodic f 1 ∧
      (∀ n : ℤ, q.val.val n=periodOneCoefficient f n) ∧ ∀ k : ℤ,
        (NLS.Poisson.gardnerHamiltonianVector (D.finiteGapActionCombination 2 5 (by norm_num) q S)
          (nativeHillSource 2 q.val)).val k = periodOneCoefficient (kdv2RHS f) k := by
  obtain ⟨f,hf,hp,hc⟩ := native_finiteGap_exists_smooth 2 q S hq
  exact ⟨f,hf,hp,hc,D.finiteGapActionCombination_kdv2_vector q S hq f hf hp hc⟩

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
