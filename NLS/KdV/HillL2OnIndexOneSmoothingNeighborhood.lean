import NLS.KdV.HillL2OnIndexSobolevExponent
import NLS.KdV.HillProductEquationFamilyFactory
import NLS.KdV.MiuraHillPsiOriginalEstimates
import NLS.KdV.HillCanonicalDiagonalCartesian

/-! Unconditional construction of a common complex L2 neighborhood
where the ACTUAL signed on-index exponent is analytic in the one-order
weighted infinity norm. The patch and retained estimates are constructed
from the verified family, not assumed as an external premise. -/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV

theorem exists_hillL2OnIndex_one_smoothing_neighborhood (q : Coeff 2)
    (hr : IsRealPeriodOneHminusOne (periodOneL2Inclusion q)) :
    ∃ P : HillProductEquationPatch, ∃ U : Set (Coeff 2), IsOpen U ∧ q ∈ U ∧
      (∀ r ∈ U, periodOneL2Inclusion r ∈ P.physicalDirichletSource) ∧
      ∃ C : ℝ, 0 < C ∧ AnalyticOnNhd ℂ P.l2OnIndexSobolevExponent U ∧
        ∀ r ∈ U, ‖P.l2OnIndexSobolevExponent r‖ ≤ C ∧ ∀ k : ℤ,
          (P.l2OnIndexSobolevExponent r).val k = P.physicalOnIndexSignedExponent (periodOneL2Inclusion r) k := by
  obtain ⟨A,H⟩ := exists_miuraHillPsiFamily_with_original_estimates
  obtain ⟨P,hqP,_,hPA⟩ := exists_hillProductEquationPatch_with_family A (periodOneL2Inclusion q) hr
  have HP : SourceLemma12_12Data (by norm_num) (by norm_num) P.parent.family.originalDomain
      P.parent.family.domain P.parent.family.roots := by rw [hPA]; exact H
  obtain ⟨r,hrpos,hsub,_⟩ := exists_common_intrinsic_diagonal_Cartesian_patch_ball
    P (periodOneL2Inclusion q) hqP hr
  have hqPhys : periodOneL2Inclusion q ∈ P.physicalDirichletSource :=
    (hsub (Metric.mem_ball_self hrpos)).1
  obtain ⟨U,hU,hqU,hUP,C,hC,ha,hraw⟩ := P.exists_local_l2OnIndexSobolevExponent_data HP q hqPhys hr
  exact ⟨P,U,hU,hqU,hUP,C,hC,ha,hraw⟩

end NLS.KdV
