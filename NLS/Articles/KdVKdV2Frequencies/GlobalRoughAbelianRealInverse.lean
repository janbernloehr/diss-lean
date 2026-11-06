import NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianInverseCharts
import NLS.ComplexAnalysis.RealInverseNeighborhoodAt
import NLS.SequenceSpaces.MeanZeroWeightedReality

/-! # Actual inverse branches preserve reality at every real rough base -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal ComplexConjugate
namespace NLS.Articles.KdVKdV2Frequencies
open NLS.KdV
namespace GlobalRoughAbelianForwardData

theorem signed_conjugation (D : GlobalRoughAbelianForwardData) (q : PeriodOneHminusOne) :
    WeightedCoeff.conjugateReflection (Weight.sobolev (-1/2)) (Weight.sobolev_neg (-1/2)) (D.signed q) =
      D.signed (periodOneHminusConjugation q) := by
  let w := Weight.sobolev (-1/2)
  have hnormal (p : PeriodOneHminusOne) : (WeightedCoeff.weightIsometry w 2) (D.signed p) =
      D.positive p+periodOneL2Conjugation (D.positive (periodOneHminusConjugation p)) := by
    change (WeightedCoeff.weightIsometry w 2) ((WeightedCoeff.weightIsometry w 2).symm
      (WeightedCoeff.normalizedSignedCompletion (Weight.sobolev (-1)) D.positive p)) = _
    rw [LinearIsometryEquiv.apply_symm_apply,
      WeightedCoeff.normalizedSignedCompletion_eq _ (Weight.sobolev_neg (-1))]
    ext j
    simp only [lp.coeFn_add,Pi.add_apply,Coeff.reflection_apply,lp.star_apply,
      periodOneL2Conjugation_apply,starRingEnd_apply]
    rfl
  apply (WeightedCoeff.weightIsometry w 2).injective
  rw [←WeightedCoeff.weightIsometry_conjugateReflection _ (Weight.sobolev_neg (-1/2)),hnormal,hnormal,
    periodOneL2Conjugation_add,periodOneL2Conjugation_involutive,periodOneHminusConjugation_involutive]
  exact add_comm _ _

theorem meanZeroForward_conjugation (D : GlobalRoughAbelianForwardData) (a : DeletedCoeff 2 0) :
    D.meanZeroForward (deletedL2Conjugation a) = deletedL2Conjugation (D.meanZeroForward a) := by
  change WeightedCoeff.meanZeroWeightedProjectionCLM (Weight.sobolev (-1/2))
    (D.signed (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1)) (deletedL2Conjugation a))) = _
  rw [WeightedCoeff.meanZeroWeightedLift_conjugation _ (Weight.sobolev_neg (-1))]
  change WeightedCoeff.meanZeroWeightedProjectionCLM (Weight.sobolev (-1/2))
    (D.signed (periodOneHminusConjugation (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1)) a))) = _
  rw [←D.signed_conjugation,WeightedCoeff.meanZeroWeightedProjection_conjugation]
  rfl

/-- At EVERY real mean-zero rough base, an actual analytic inverse
branch on an OPEN target neighborhood preserves the physical real form.
The full raw right identity belongs to THAT SAME global signed map. -/
theorem exists_real_weak_inverse_germ (D : GlobalRoughAbelianForwardData)
    (a : DeletedCoeff 2 0)
    (hr : IsRealPeriodOneHminusOne (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1)) a)) :
    ∃ U : Set (DeletedCoeff 2 0), IsOpen U ∧ D.meanZeroForward a ∈ U ∧
      ∃ G : DeletedCoeff 2 0 → DeletedCoeff 2 0,
        AnalyticOnNhd ℂ G U ∧ G (D.meanZeroForward a) = a ∧ ∀ z ∈ U,
          G z ∈ D.meanZeroDomain ∧ D.meanZeroForward (G z) = z ∧
          D.signed (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1)) (G z)) =
            WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1/2)) z ∧
          (deletedL2Conjugation z = z →
            IsRealPeriodOneHminusOne (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1)) (G z))) := by
  obtain ⟨P,hP,haP,hsub,_hPa,hPia,_hrawleft,hrawright⟩ := D.exists_weak_analytic_inverse_at a hr
  have hJa : deletedL2Conjugation a = a :=
    (WeightedCoeff.meanZeroWeightedLift_real_iff _ (Weight.sobolev_neg (-1)) a).mp hr
  have hFa : D.meanZeroForward a ∈ P.target := by
    rw [←hP]
    exact P.map_source haP
  obtain ⟨U,hU,hFaU,hUP,hreal⟩ := NLS.ComplexAnalysis.exists_fixed_inverse_neighborhood_at
    D.meanZeroForward P.symm deletedL2Conjugation deletedL2Conjugation isometry_deletedL2Conjugation
    P.source P.target P.open_source P.open_target a haP hJa hFa hPia.continuousOn
    (by rw [←hP]; exact P.injOn)
    (fun x hx => by rw [←hP]; exact P.left_inv hx)
    (fun z hz => ⟨P.map_target hz,by rw [←hP]; exact P.right_inv hz⟩)
    (fun x _ => D.meanZeroForward_conjugation x)
  refine ⟨U,hU,hFaU,P.symm,hPia.mono hUP,?_,?_⟩
  · rw [←hP]
    exact P.left_inv haP
  · intro z hz
    refine ⟨hsub (P.map_target (hUP hz)),?_,hrawright z (hUP hz),?_⟩
    · rw [←hP]
      exact P.right_inv (hUP hz)
    · intro hJz
      exact (WeightedCoeff.meanZeroWeightedLift_real_iff _ (Weight.sobolev_neg (-1)) _).mpr (hreal z hz hJz)

end GlobalRoughAbelianForwardData
end NLS.Articles.KdVKdV2Frequencies
