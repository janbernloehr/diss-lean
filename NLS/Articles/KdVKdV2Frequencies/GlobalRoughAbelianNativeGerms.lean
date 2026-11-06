import NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForward
import NLS.KdV.HillAbelianSignedPhysicalValues

/-! # All native forward germs of the ONE global rough Abelian map

There is no smallness or L2 condition on the real rough base. Exact
physical signed coordinates, reality, zero central slots and the SAME
actual compact Fourier principal comparison are retained.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal ComplexConjugate
namespace NLS.Articles.KdVKdV2Frequencies
open NLS.KdV
namespace GlobalRoughAbelianForwardData

/-- Full literal original signed coordinates at EVERY physical source,
including low and closed gaps, arbitrary means and unbounded L2 norms. -/
theorem signed_physical (D : GlobalRoughAbelianForwardData)
    (p : RealPeriodOneHillPotential) (j : ℤ) :
    (D.signed (hillPhysicalHminusEmbedding p).val).val j =
      hillAbelianRawCoordinateSequence SpectralWeight.one (hillUnitRealSourceUnembed p) j := by
  exact hillAbelian_signedTargetLift_physical_of_values D.positive p
    (fun k hk => D.positive_zero _ (D.real_mem_domain _ (hillPhysicalHminusEmbedding p).property) k hk)
    (D.positive_physical p) j

/-- Every real rough source has the literal signed target reality. -/
theorem signed_real (D : GlobalRoughAbelianForwardData)
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) :
    ∀ j : ℤ, (D.signed q).val (-j) = conj ((D.signed q).val j) := by
  intro j
  have hJ : WeightedCoeff.conjugateReflection (Weight.sobolev (-1)) (Weight.sobolev_neg (-1)) q = q :=
    (periodOneHminusConjugation_fixed_iff q).mpr hr
  simp only [signed,WeightedCoeff.signedTargetLift_eq_weightedSourceSignedCompletion,
    WeightedCoeff.weightedSourceSignedCompletion_apply _ _ (Weight.sobolev_neg (-1))
      (Weight.sobolev_neg (-1/2)),hJ,neg_neg,map_add,conj_conj]
  exact add_comm _ _

/-- The SAME global signed map has a genuine native analytic forward
germ at EVERY real native base and EVERY nonnegative Sobolev order.
All complex inclusions and both zero slots are literal. At every real
point the full derivative is the actual Fourier principal plus compact,
and the actual mean-zero principal is a bounded equivalence. -/
theorem exists_all_native_signed_germ (D : GlobalRoughAbelianForwardData)
    (t : ℝ) (ht : 0 ≤ t) (q : WeightedCoeff (Weight.sobolev (t-1)) 2)
    (hqr : IsRealPeriodOneHminusOne (periodOneSobolevImageInclusion t ht q)) :
    let q0 : PeriodOneRealHminusOne := ⟨periodOneSobolevImageInclusion t ht q,hqr⟩
    let E := D.chart q0
    ∃ V : Set (WeightedCoeff (Weight.sobolev (t-1)) 2), IsOpen V ∧ q ∈ V ∧
      (∀ p ∈ V, WeightedCoeff.conjugateReflection (Weight.sobolev (t-1))
        (Weight.sobolev_neg (t-1)) p ∈ V) ∧
      ∃ C : ℝ, ∃ g : WeightedCoeff (Weight.sobolev (t-1)) 2 → WeightedCoeff (Weight.sobolev (t-1/2)) 2,
        0 ≤ C ∧ AnalyticOnNhd ℂ g V ∧ ∀ p ∈ V,
          periodOneSobolevImageInclusion t ht p ∈ ball q0.val E.data.radius ∧
          periodOneSobolevImageInclusion t ht p ∈ D.domain ∧ ‖g p‖ ≤ C ∧
          WeightedCoeff.sobolevInclusion (by linarith : (-1/2 : ℝ) ≤ t-1/2) (g p) =
            D.signed (periodOneSobolevImageInclusion t ht p) ∧ (g p).val 0 = 0 ∧
          (IsRealPeriodOneHminusOne (periodOneSobolevImageInclusion t ht p) →
            IsCompactOperator (fderiv ℂ g p-packetSignedFourierPrincipalAt E.data E.signs t ht p) ∧
            ∃ A : DeletedCoeff 2 0 ≃L[ℂ] DeletedCoeff 2 0,
              A.toContinuousLinearMap = packetMeanZeroFourierPrincipalAt E.data E.signs t ht p) := by
  let q0 : PeriodOneRealHminusOne := ⟨periodOneSobolevImageInclusion t ht q,hqr⟩
  let E := D.chart q0
  obtain ⟨V,hV,hqV,hJ,C,g,hC,hga,hd⟩ :=
    E.data.exists_native_signed_packet_fourier_germ q0.property E.signs t ht q hqr
      (mem_ball_self E.data.radius_pos)
  refine ⟨V,hV,hqV,hJ,C,g,hC,hga,?_⟩
  intro p hp
  have h := hd p hp
  refine ⟨h.1,D.chart_subset_domain q0 h.1,h.2.1,?_,h.2.2.2.1,?_⟩
  · exact h.2.2.1.trans (D.signed_local q0 h.1).symm
  · intro hr
    exact ⟨h.2.2.2.2 hr,exists_packetMeanZeroFourierPrincipalAt_equiv E.data E.signs t ht p h.1 hr⟩

end GlobalRoughAbelianForwardData
end NLS.Articles.KdVKdV2Frequencies
