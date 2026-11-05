import NLS.KdV.HillPrimitiveMomentsClosedGap
import NLS.KdV.HillPrimitiveMomentsEnergyContour
import NLS.Articles.KdVPseudomeasures.OriginalHillH1FrequencyAtZero

/-! The actual original rough Fourier source has local centered primitive
moments of every positive gap and every even order on ONE complex source
neighborhood. These are spectral ingredients for rough KdV frequencies;
the infinite frequency series and its physical identification remain separate. -/
noncomputable section
open Set NLS.KdV NLS.WeightedCoeff NLS.ZakharovShabat
namespace NLS.Articles.KdVPseudomeasures

theorem originalHill_exists_frequency_moment_neighborhood (q : HillRealMeanZeroSource) :
    ∃ P : HillProductEquationPatch, ∃ W : Set (CoeffPair 2),
      ∃ C : SourceFullAbelianUniformCauchyFamily (by simp) (by norm_num) W,
        hillRealMeanZeroInclusion q ∈ P.momentSource C ∧ IsOpen (P.momentSource C) ∧
        ∀ n m : ℕ+, ∀ d : ℕ,
          AnalyticOnNhd ℂ (P.centeredMoment W n m d) (P.momentSource C) := by
  have hr : IsRealPeriodOneHminusOne (hillRealMeanZeroInclusion q) := by intro k; exact q.property k
  obtain ⟨P,hq,_⟩ := exists_hillProductEquationPatch (hillRealMeanZeroInclusion q) hr
  obtain ⟨W,C,hC,hMom⟩ := P.exists_centeredMoment_neighborhood (hillRealMeanZeroInclusion q) hq hr
  exact ⟨P,W,C,hC,P.momentSource_open C,hMom⟩

end NLS.Articles.KdVPseudomeasures
