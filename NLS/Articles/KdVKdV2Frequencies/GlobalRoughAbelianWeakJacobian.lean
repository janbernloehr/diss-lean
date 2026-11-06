import NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianCanonical
import NLS.Articles.KdVKdV2Frequencies.ActualNativeJacobianUnit
import NLS.KdV.HillRoughAbelianHamiltonianRange
import NLS.FunctionalAnalysis.CompactEquivDenseRange
import NLS.SequenceSpaces.MeanZeroSobolevIdentities

/-! # Full mean-zero weak Jacobian units at every real rough source -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies
open NLS.KdV
namespace GlobalRoughAbelianForwardData

def meanZeroDomain (D : GlobalRoughAbelianForwardData) : Set (DeletedCoeff 2 0) :=
  (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1))) ⁻¹' D.domain

def meanZeroForward (D : GlobalRoughAbelianForwardData) : DeletedCoeff 2 0 → DeletedCoeff 2 0 :=
  weakMeanZeroAbelianMap D.signed

theorem meanZeroDomain_open (D : GlobalRoughAbelianForwardData) : IsOpen D.meanZeroDomain :=
  D.domain_open.preimage (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1))).continuous

theorem meanZeroForward_analytic (D : GlobalRoughAbelianForwardData) :
    AnalyticOnNhd ℂ D.meanZeroForward D.meanZeroDomain := by
  intro a ha
  exact ((WeightedCoeff.meanZeroWeightedProjectionCLM (Weight.sobolev (-1/2))).analyticAt _).comp
    ((D.signed_analytic _ ha).comp
      ((WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1))).analyticAt a))

theorem fderiv_meanZeroForward (D : GlobalRoughAbelianForwardData)
    (a : DeletedCoeff 2 0) (ha : a ∈ D.meanZeroDomain) :
    fderiv ℂ D.meanZeroForward a = hillMeanZeroAbelianDerivative D.signed
      (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1)) a) := by
  exact ((WeightedCoeff.meanZeroWeightedProjectionCLM (Weight.sobolev (-1/2))).hasFDerivAt.comp a
    ((D.signed_analytic _ ha).differentiableAt.hasFDerivAt.comp a
      (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1))).hasFDerivAt)).fderiv

/-- Actual canonical Hamiltonian directions give dense range of the FULL
Jacobian at every real mean-zero rough source, including non-L2 bases. -/
theorem denseRange_fderiv_meanZeroForward (D : GlobalRoughAbelianForwardData)
    (a : DeletedCoeff 2 0)
    (hr : IsRealPeriodOneHminusOne (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1)) a)) :
    DenseRange (fderiv ℂ D.meanZeroForward a) := by
  have ha := D.real_mem_domain _ hr
  rw [D.fderiv_meanZeroForward a ha]
  exact denseRange_hillMeanZeroAbelianDerivative_of_Gardner_matrix D.signed _
    (D.signed_analytic _ ha).differentiableAt
    (D.gardner_matrix_real_meanZero _ hr (WeightedCoeff.meanZeroWeightedLift_zero _ a))

/-- At every real rough source the FULL weak derivative is a compact
perturbation of an ACTUAL bounded equivalence, with no injectivity premise. -/
theorem exists_compact_principal_fderiv_meanZeroForward (D : GlobalRoughAbelianForwardData)
    (a : DeletedCoeff 2 0)
    (hr : IsRealPeriodOneHminusOne (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1)) a)) :
    ∃ Q : DeletedCoeff 2 0 ≃L[ℂ] DeletedCoeff 2 0,
      IsCompactOperator (fderiv ℂ D.meanZeroForward a-Q.toContinuousLinearMap) := by
  let L := WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev ((0 : ℝ)-1))
  let P := WeightedCoeff.meanZeroWeightedProjectionCLM (Weight.sobolev ((0 : ℝ)-1/2))
  let J := WeightedCoeff.meanZeroSobolevInclusion (by linarith : (-1 : ℝ) ≤ 0-1)
  let I := WeightedCoeff.meanZeroSobolevInclusion (by linarith : (-1/2 : ℝ) ≤ 0-1/2)
  have hJ : J = ContinuousLinearMap.id ℂ (DeletedCoeff 2 0) := by
    dsimp only [J]
    simpa only [zero_sub] using WeightedCoeff.meanZeroSobolevInclusion_self (-1) le_rfl
  have hI : I = ContinuousLinearMap.id ℂ (DeletedCoeff 2 0) := by
    dsimp only [I]
    simpa only [zero_sub,neg_div] using WeightedCoeff.meanZeroSobolevInclusion_self (-1/2) le_rfl
  have heL (x : DeletedCoeff 2 0) : periodOneSobolevImageInclusion 0 le_rfl (L x) =
      WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1)) x := by
    have h := WeightedCoeff.meanZeroSobolevInclusion_lift (by linarith : (-1 : ℝ) ≤ 0-1) x
    change WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1)) (J x) = _ at h
    rw [hJ] at h
    exact h.symm
  have hqr : IsRealPeriodOneHminusOne (periodOneSobolevImageInclusion 0 le_rfl (L a)) := by
    rw [heL]
    exact hr
  obtain ⟨V,hV,haV,_hclosed,C,g,_hC,hga,hd⟩ := D.exists_all_native_signed_germ 0 le_rfl (L a) hqr
  have hnear : nativeMeanZeroAbelianMap 0 g =ᶠ[𝓝 a] D.meanZeroForward := by
    filter_upwards [(hV.preimage L.continuous).mem_nhds haV] with x hx
    have hcomm := congrArg (WeightedCoeff.meanZeroWeightedProjectionCLM (Weight.sobolev (-1/2)))
      (hd (L x) hx).2.2.2.1
    rw [←WeightedCoeff.meanZeroSobolevInclusion_projection] at hcomm
    change I (nativeMeanZeroAbelianMap 0 g x) = _ at hcomm
    rw [hI,heL] at hcomm
    exact hcomm
  have hder : fderiv ℂ (nativeMeanZeroAbelianMap 0 g) a = fderiv ℂ D.meanZeroForward a :=
    hnear.fderiv_eq
  have hc := ((hd (L a) haV).2.2.2.2.2 hqr).1
  obtain ⟨Q,hQ⟩ := ((hd (L a) haV).2.2.2.2.2 hqr).2
  refine ⟨Q,?_⟩
  have hc' := isCompactOperator_fderiv_clm_pre_post_sub L P g a (hga (L a) haV).differentiableAt _ hc
  change IsCompactOperator (fderiv ℂ (nativeMeanZeroAbelianMap 0 g) a-
    packetMeanZeroFourierPrincipalAt _ _ 0 le_rfl (L a)) at hc'
  rw [hder,←hQ] at hc'
  exact hc'

/-- The full actual weak mean-zero Jacobian is a bounded isomorphism at
EVERY real rough source. Dense canonical range and the actual compact
principal supply bijectivity; it is not assumed from principal ellipticity. -/
theorem isUnit_fderiv_meanZeroForward (D : GlobalRoughAbelianForwardData)
    (a : DeletedCoeff 2 0)
    (hr : IsRealPeriodOneHminusOne (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1)) a)) :
    IsUnit (fderiv ℂ D.meanZeroForward a) := by
  obtain ⟨Q,hQ⟩ := D.exists_compact_principal_fderiv_meanZeroForward a hr
  exact ContinuousLinearMap.isUnit_iff_bijective.mpr
    (bijective_of_compact_sub_equiv_of_denseRange _ Q hQ (D.denseRange_fderiv_meanZeroForward a hr))

end GlobalRoughAbelianForwardData
end NLS.Articles.KdVKdV2Frequencies
