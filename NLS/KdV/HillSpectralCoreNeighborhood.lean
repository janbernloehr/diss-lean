import NLS.KdV.HillMeanZeroSpectralCore
import NLS.KdV.HillProductEquationFamilyFactory

/-! A common actual spectral-core neighborhood at EVERY native real
source. The patch, infinite-family estimates and scalar identifications
are constructed from the verified original family, not supplied as
assumptions. Every coefficient and compact operator uses one neighborhood. -/
noncomputable section
open Set Metric NLS.ZakharovShabat
namespace NLS.KdV

theorem exists_hillSpectralCoreNeighborhood (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) :
    ∃ P : HillProductEquationPatch, ∃ U : Set PeriodOneHminusOne,
      IsOpen U ∧ q ∈ U ∧ U ⊆ P.physicalDirichletSource ∩ hillHminusActionAngleNativeDomain ∧
      AnalyticOnNhd ℂ P.physicalSpectralCoreMap U ∧
      (∀ a ∈ U, ∀ n : ℕ+,
        (P.physicalSpectralCoreMap a).val ((n:ℕ):ℤ) = P.physicalSpectralFactorMinus n a/
          (((2*Real.sqrt Real.pi*Real.sqrt (n:ℕ):ℝ):ℂ)*(Real.sqrt 2:ℂ)) ∧
        (P.physicalSpectralCoreMap a).val (-((n:ℕ):ℤ)) = P.physicalSpectralFactorPlus n a/
          (((2*Real.sqrt Real.pi*Real.sqrt (n:ℕ):ℝ):ℂ)*(Real.sqrt 2:ℂ))) ∧
      (∀ a ∈ U, IsCompactOperator (fderiv ℂ hillHminusIntrinsicDiagonalMap a-fderiv ℂ P.physicalSpectralCoreMap a)) ∧
      (∀ a : HillMeanZeroSource, a.val ∈ U → IsCompactOperator (P.physicalMeanZeroSpectralCoreRemainder a)) := by
  obtain ⟨A,H⟩ := exists_miuraHillPsiFamily_with_original_estimates
  obtain ⟨P,hqP,_,hPA⟩ := exists_hillProductEquationPatch_with_family A q hr
  have HP : SourceLemma12_12Data (by norm_num) (by norm_num) P.parent.family.originalDomain
      P.parent.family.domain P.parent.family.roots := by rw [hPA]; exact H
  obtain ⟨r,hrpos,hsub,heq⟩ := exists_common_intrinsic_diagonal_Cartesian_patch_ball P q hqP hr
  let U := ball q r ∩ hillHminusActionAngleNativeDomain
  have hUsub : U ⊆ P.physicalDirichletSource ∩ hillHminusActionAngleNativeDomain :=
    fun _ h => ⟨(hsub h.1).1,h.2⟩
  refine ⟨P,U,isOpen_ball.inter isOpen_hillHminusActionAngleNativeDomain,
    ⟨mem_ball_self hrpos,real_mem_hillHminusActionAngleNativeDomain q hr⟩,
    hUsub,(P.analytic_physicalSpectralCoreMap HP).mono hUsub,?_,?_,?_⟩
  · intro a ha n
    exact ⟨P.physicalSpectralCoreMap_positive HP a (hUsub ha).1 (hUsub ha).2 n (heq n a ha.1).2,
      P.physicalSpectralCoreMap_negative HP a (hUsub ha).1 (hUsub ha).2 n (heq n a ha.1).1⟩
  · intro a ha
    exact P.isCompactOperator_physicalOnIndexJacobianDifference HP a (hUsub ha).1 (hUsub ha).2
  · intro a ha
    exact P.isCompactOperator_physicalMeanZeroSpectralCoreRemainder HP a (hUsub ha)

end NLS.KdV
