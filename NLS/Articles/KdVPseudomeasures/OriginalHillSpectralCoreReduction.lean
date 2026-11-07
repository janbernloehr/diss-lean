import NLS.Articles.KdVPseudomeasures.OriginalHillIntrinsicJacobianCompact
import NLS.KdV.HillSpectralCoreNeighborhood

/-! Actual spectral-core reduction at every original physical source.
The patch and its common complex neighborhood are constructed, including
all collapsed gaps. The remaining core/Fourier derivative estimate is open. -/
noncomputable section
open Set NLS.KdV
namespace NLS.Articles.KdVPseudomeasures

theorem original_Hill_spectral_core_reduction (q : OriginalHminusOnePotential) :
    ∃ P : HillProductEquationPatch, ∃ U : Set PeriodOneHminusOne,
      IsOpen U ∧ originalPeriodOneCoefficients q ∈ U ∧
      U ⊆ P.physicalDirichletSource ∩ hillHminusActionAngleNativeDomain ∧
      AnalyticOnNhd ℂ P.physicalSpectralCoreMap U ∧
      (∀ a ∈ U, ∀ n : ℕ+,
        (P.physicalSpectralCoreMap a).val ((n:ℕ):ℤ) = P.physicalSpectralFactorMinus n a/
          (((2*Real.sqrt Real.pi*Real.sqrt (n:ℕ):ℝ):ℂ)*(Real.sqrt 2:ℂ)) ∧
        (P.physicalSpectralCoreMap a).val (-((n:ℕ):ℤ)) = P.physicalSpectralFactorPlus n a/
          (((2*Real.sqrt Real.pi*Real.sqrt (n:ℕ):ℝ):ℂ)*(Real.sqrt 2:ℂ))) ∧
      IsCompactOperator (P.physicalMeanZeroSpectralCoreRemainder (originalHillRealMeanZeroSource q).val) := by
  obtain ⟨P,U,hU,hqU,hUP,ha,hcoords,_,hc⟩ := exists_hillSpectralCoreNeighborhood
    (originalPeriodOneCoefficients q) (originalPeriodOneCoefficients_real q)
  exact ⟨P,U,hU,hqU,hUP,ha,hcoords,hc (originalHillRealMeanZeroSource q).val hqU⟩

end NLS.Articles.KdVPseudomeasures
