import NLS.Articles.KdVPseudomeasures.OriginalHillMiuraDerivative
import NLS.KdV.HillDiracSpectralTerminal
import NLS.KdV.HillRotatedDiracSource

/-! The original Hill spectral core is identified with the actual
Dirac spectral terminal at the phase-rotated SAME Miura source. The
physical sheet sign and original normalizations are proved explicitly;
the remaining spectral Jacobian estimate is not assumed here. -/
noncomputable section
open Set NLS.KdV NLS.ZakharovShabat
namespace NLS.Articles.KdVPseudomeasures

theorem original_Hill_Dirac_terminal_sheet (q : OriginalHminusOnePotential) :
    ∃ P : HillProductEquationPatch, originalPeriodOneCoefficients q ∈ P.source ∧
      ∀ n : ℕ+,
        hillHminusDirichletSheet n (originalPeriodOneCoefficients q) =
          -sourceAntiDiscriminantCandidate (by simp) (by norm_num)
            (P.rotatedDiracSource (originalPeriodOneCoefficients q))
            (P.physicalDirichletFrequency ((n:ℕ):ℤ) (originalPeriodOneCoefficients q)) ∧
        P.physicalDirichletRootCoefficient n (originalPeriodOneCoefficients q) =
          Complex.I*sourceDirichletEtaSineNumerator (by simp) (by norm_num) ((n:ℕ):ℤ)
            (P.rotatedDiracSource (originalPeriodOneCoefficients q)) := by
  obtain ⟨P,hP,_⟩ := exists_hillProductEquationPatch (originalPeriodOneCoefficients q)
    (originalPeriodOneCoefficients_real q)
  exact ⟨P,hP,fun n => ⟨P.physicalDirichletSheet_eq_rotatedAntiDiscriminant n _ hP,
    P.physicalDirichletRootCoefficient_eq_rotatedSineNumerator n _ hP⟩⟩

theorem original_Hill_Dirac_spectral_core (q : OriginalHminusOnePotential) :
    ∃ P : HillProductEquationPatch, ∃ U : Set PeriodOneHminusOne,
      IsOpen U ∧ originalPeriodOneCoefficients q ∈ U ∧
      U ⊆ P.physicalDirichletSource ∩ hillHminusActionAngleNativeDomain ∧
      AnalyticOnNhd ℂ P.physicalSpectralCoreMap U ∧
      AnalyticOnNhd ℂ P.rotatedDiracSource U ∧
      (∀ a ∈ U, ∀ n : ℕ+,
        (P.physicalSpectralCoreMap a).val ((n:ℕ):ℤ) =
          (2*sourceStandardRootMidpoint (by simp) (by norm_num) (P.sourcePsi a) ((n:ℕ):ℤ)*
            sourceGapWeightedEtaTerminalCoordinate (by simp) (by norm_num) ((n:ℕ):ℤ) 1 (P.rotatedDiracSource a))/
              (((2*Real.sqrt Real.pi*Real.sqrt (n:ℕ):ℝ):ℂ)*(Real.sqrt 2:ℂ)) ∧
        (P.physicalSpectralCoreMap a).val (-((n:ℕ):ℤ)) =
          (2*sourceStandardRootMidpoint (by simp) (by norm_num) (P.sourcePsi a) ((n:ℕ):ℤ)*
            sourceGapWeightedEtaTerminalCoordinate (by simp) (by norm_num) ((n:ℕ):ℤ) (-1) (P.rotatedDiracSource a))/
              (((2*Real.sqrt Real.pi*Real.sqrt (n:ℕ):ℝ):ℂ)*(Real.sqrt 2:ℂ))) ∧
      IsRealType (CoeffPair.toMax 2 (P.rotatedDiracSource (originalPeriodOneCoefficients q))) ∧
      IsCompactOperator (fderiv ℂ P.rotatedDiracSource (originalPeriodOneCoefficients q)-
        (sourcePhase.comp hillMiuraDiagonal).comp (periodOneMassInverse 0)) ∧
      IsCompactOperator (P.physicalMeanZeroSpectralCoreRemainder (originalHillRealMeanZeroSource q).val) := by
  obtain ⟨P,U,hU,hqU,hUP,ha,hcoords,_,hc⟩ := exists_hillSpectralCoreNeighborhood
    (originalPeriodOneCoefficients q) (originalPeriodOneCoefficients_real q)
  have hP : originalPeriodOneCoefficients q ∈ P.source := (hUP hqU).1.1
  refine ⟨P,U,hU,hqU,hUP,ha,(P.analytic_rotatedDiracSource).mono (fun _ h => (hUP h).1.1),?_,
    P.isRealType_rotatedDiracSource _ hP (originalPeriodOneCoefficients_real q),
    P.isCompactOperator_rotatedDiracSourceDerivative_sub_massInverse _ hP,
    hc (originalHillRealMeanZeroSource q).val hqU⟩
  intro a ha n
  constructor
  · rw [(hcoords a ha n).1,P.physicalSpectralFactorMinus_eq_rotatedTerminal n a (hUP ha).1.1]
    rfl
  · rw [(hcoords a ha n).2,P.physicalSpectralFactorPlus_eq_rotatedTerminal n a (hUP ha).1.1]
    rfl

end NLS.Articles.KdVPseudomeasures
