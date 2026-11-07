import NLS.KdV.HillMiuraSobolevNormalizedSource
import NLS.ZakharovShabat.SourceWeightedAbsoluteBetaDecay

/-! The SAME original root family has absolute inverse-index beta decay
on a complex H1 neighborhood of every actual real Miura source. -/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV

theorem exists_hillMiuraH1_absolute_beta_decay
    {W0 W : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
    (H : SourceLemma12_12Data (by norm_num) (by norm_num) W0 W s)
    (a0 : WeightedCoeff (Weight.sobolev 1) 2)
    (hr : periodOneL2Conjugation (WeightedCoeff.sobolevToL2 (by norm_num : (0:ℝ)≤1) a0)=
      WeightedCoeff.sobolevToL2 (by norm_num : (0:ℝ)≤1) a0) :
    ∃ V : Set (WeightedCoeff (Weight.sobolev 1) 2), IsOpen V ∧ a0∈V ∧
      ∃ K : ℝ, 0≤K ∧ ∀ a∈V, ∀ n : ℤ,
        Summable (fun m : ℤ => ‖sourceAngularBetaSeriesTerm (by norm_num) (by norm_num) n s
          (sourcePhase (hillMiuraDiagonal (WeightedCoeff.sobolevToL2 (by norm_num : (0:ℝ)≤1) a))) m‖) ∧
        (1+|(n:ℝ)|)*(∑' m : ℤ, ‖sourceAngularBetaSeriesTerm (by norm_num) (by norm_num) n s
          (sourcePhase (hillMiuraDiagonal (WeightedCoeff.sobolevToL2 (by norm_num : (0:ℝ)≤1) a))) m‖)≤K := by
  obtain ⟨B,D,_hactions⟩ := H.exists_original_birkhoff_map
  let J := hillMiuraNormalizedSobolevDirichletSource 1
  let φ : realTypeSourceLocus 2 :=
    ⟨J a0,isRealType_hillMiuraNormalizedSobolevDirichletSource 1 (by norm_num) a0 hr⟩
  have hw (m : ℤ) : 1+|(m:ℝ)|≤sourceSobolevSpectralWeight 1 (by norm_num) (2*m) := by
    rw [sourceSobolevSpectralWeight_even]
    simp only [Weight.sobolev_apply,Real.rpow_one,le_refl]
  obtain ⟨U,hU,hφU,K,hK,hbound⟩ :=
    D.exists_local_normalizedWeighted_absolute_beta_decay (sourceSobolevSpectralWeight 1 (by norm_num)) hw φ
  refine ⟨J ⁻¹' U,hU.preimage J.continuous,hφU,K,hK,?_⟩
  intro a ha n
  have h := hbound (J a) ha n
  simpa only [J,normalizedWeightedSource_hillMiuraSobolev] using h

end NLS.KdV
