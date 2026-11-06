import NLS.KdV.HillOriginalAllGapCartesianGardner
import NLS.KdV.HillMeanZeroOpenGapDensity
import NLS.KdV.HillHminusOriginalOpenCartesianMatrix

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
namespace NLS.KdV

/-- The FULL ORIGINAL complex Cartesian Gardner matrix holds at EVERY
original mean-zero real L2 source, INCLUDING closed selected gaps. The
actual selected-open locus is dense within the original mean-zero space,
and every genuine Gardner entry is continuous through those gaps. -/
theorem hillOriginalCartesianGardnerEntry_eq_matrix
    (q : RealPeriodOneHillPotential) (hmean : q.val.val 0 = 0)
    (n m : ℕ+) (σ τ : Bool) :
    hillOriginalCartesianGardnerEntry n m σ τ q = hillOriginalComplexGardnerMatrixEntry σ τ n m := by
  let S := {p : RealPeriodOneHillPotential | p.val.val 0 = 0 ∧
    hillRealGapHalfLength p.val p.property.1 p.property.2 n ≠ 0 ∧
    hillRealGapHalfLength p.val p.property.1 p.property.2 m ≠ 0}
  have hS : S ⊆ {p : RealPeriodOneHillPotential |
      hillOriginalCartesianGardnerEntry n m σ τ p = hillOriginalComplexGardnerMatrixEntry σ τ n m} := by
    intro p hp
    obtain ⟨hF,hFM⟩ := hillOriginalSignedCartesianHminusGerm_spec p n σ
    obtain ⟨hG,hGM⟩ := hillOriginalSignedCartesianHminusGerm_spec p m τ
    exact hillSignedCartesians_hminus_Gardner_original_open_matrix p hp.1 n m σ τ hp.2.1 hp.2.2
      _ _ hF hG hFM hGM
  have hclosed : IsClosed {p : RealPeriodOneHillPotential |
      hillOriginalCartesianGardnerEntry n m σ τ p = hillOriginalComplexGardnerMatrixEntry σ τ n m} :=
    isClosed_eq (continuous_hillOriginalCartesianGardnerEntry n m σ τ) continuous_const
  exact closure_minimal hS hclosed (hillMeanZero_mem_closure_selectedOpen q n m hmean)

/-- ALL FOUR genuine ORIGINAL signed Cartesian Gardner entries, with the
exact positive-2i mixed normalization, hold at EVERY mean-zero original
real source and EVERY positive pair of indices. Low and closed selected
gaps are included. Any analytic H-minus-one representatives matching the
ORIGINAL real L2 germs give the same matrix. -/
theorem hillSignedCartesians_hminus_Gardner_original_matrix
    (q : RealPeriodOneHillPotential) (hmean : q.val.val 0 = 0)
    (n m : ℕ+) (σ τ : Bool)
    (F G : PeriodOneHminusOne → ℂ)
    (hF : AnalyticAt ℂ F (hillOriginalHminusSource q.val))
    (hG : AnalyticAt ℂ G (hillOriginalHminusSource q.val))
    (hFM : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      F (hillOriginalHminusSource p.val) = hillSignedSpectralCartesian σ n p)
    (hGM : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      G (hillOriginalHminusSource p.val) = hillSignedSpectralCartesian τ m p) :
    NLS.Poisson.hminusGardnerBracket F G (hillOriginalHminusSource q.val) =
      hillOriginalComplexGardnerMatrixEntry σ τ n m := by
  rw [←hillOriginalCartesianGardnerEntry_eq_of_physical_germs q n m σ τ F G hF hG hFM hGM]
  exact hillOriginalCartesianGardnerEntry_eq_matrix q hmean n m σ τ

end NLS.KdV
