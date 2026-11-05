import NLS.KdV.HillAllGapMultiplicities
import NLS.KdV.HillHminusRelativeAction
import NLS.KdV.HillHminusOneCentralCounting
import NLS.ComplexAnalysis.ZeroCountHomotopy
import NLS.ComplexAnalysis.ZeroMultiset

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



theorem continuous_hillHminusRadicand_parameter_energy :
    Continuous (Function.uncurry (fun p : PeriodOneHminusOne => hillHminusRadicand p)) := by
  have hC : Continuous (fun t : ℂ × PeriodOneHminusOne => hillHminusRadicand t.2 t.1) :=
    continuous_iff_continuousAt.mpr
      (fun t => (analyticOnNhd_hillHminusRadicand_joint t (mem_univ _)).continuousAt)
  apply (hC.comp (continuous_swap : Continuous (Prod.swap : PeriodOneHminusOne × ℂ → ℂ × PeriodOneHminusOne))).congr
  intro t
  rfl

variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

theorem exists_hillHminusIntrinsicGapPair_neighborhood (k : ℕ) (hk : 1 ≤ k) :
    ∃ V : Set (PeriodOneHminusOne), IsOpen V ∧ hillOriginalHminusSource q ∈ V ∧
      ∀ p ∈ V,
        (∀ z ∈ sphere (hillRealGapCenter q hq hr k : ℂ)
          (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k), hillHminusRadicand p z ≠ 0) ∧
        ∃ a ∈ ball (hillRealGapCenter q hq hr k : ℂ)
          (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k),
        ∃ b ∈ ball (hillRealGapCenter q hq hr k : ℂ)
          (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k),
          hillHminusRadicand p a = 0 ∧ hillHminusRadicand p b = 0 ∧
          ∀ z ∈ closedBall (hillRealGapCenter q hq hr k : ℂ)
            (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k),
            analyticOrderNatAt (hillHminusRadicand p) z = ({a,b} : Multiset ℂ).count z := by
  let c : ℂ := hillRealGapCenter q hq hr k
  let R := hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k
  have hR : 0 < R := add_pos_of_nonneg_of_pos (hillRealGapContour_geometry q hq hr k hk).1
    (hillRealGapContour_geometry q hq hr k hk).2.1
  have hbase (z : ℂ) (hz : z ∈ sphere c R) : hillHminusRadicand (hillOriginalHminusSource q) z ≠ 0 :=
    by
      rw [hillHminusRadicand_original_source_agreement q hq]
      exact hillL2Radicand_ne_zero_on_realCutDomain q hq hr z
        (hillRealGapContour_sphere_subset q hq hr k hk hz)
  have hcount := eventually_analyticZeroCount_eq_of_continuous_family
    (fun p : PeriodOneHminusOne => hillHminusRadicand p) c R hR continuous_hillHminusRadicand_parameter_energy.continuousOn
      (fun p => (analyticOnNhd_hillHminusRadicand p).mono (subset_univ _)) (hillOriginalHminusSource q) hbase
  obtain ⟨V,hV,hqV,_,hdom⟩ := exists_hillHminusRelativeAction_analytic_neighborhood q hq hr k hk
  obtain ⟨W,hWsub,hW,hqW⟩ := _root_.mem_nhds_iff.mp hcount
  refine ⟨V ∩ W,hV.inter hW,⟨hqV,hqW⟩,?_⟩
  intro p hp
  have hbound (z : ℂ) (hz : z ∈ sphere c R) : hillHminusRadicand p z ≠ 0 := by
    rw [← hillHminusRelativeRoot_sq q hq hr _ (hdom p hp.1 z hz)]
    exact pow_ne_zero 2 (hillHminusRelativeRoot_ne_zero q hq hr _ (hdom p hp.1 z hz))
  have hagree : hillHminusRadicand (hillOriginalHminusSource q) = hillL2Radicand (SpectralWeight.one.toCoeff q) :=
    funext (hillHminusRadicand_original_source_agreement q hq)
  have htwo : analyticZeroCount (hillHminusRadicand p) (closedBall c R) = 2 := by
    rw [(hWsub hp.2),hagree]
    exact analyticZeroCount_hillL2Radicand_intrinsic_gap q hq hr k hk
  obtain ⟨z,hz⟩ := (NormedSpace.sphere_nonempty (E := ℂ) (x := c)).mpr hR.le
  have ha := (analyticOnNhd_hillHminusRadicand p).mono (subset_univ (closedBall c R))
  obtain ⟨a,haK,b,hbK,haz,hbz,horders⟩ := exists_two_analytic_zeros
    (analyticZeroCount_hasFiniteSupport (isCompact_closedBall c R) (isConnected_closedBall hR.le) ha
      (sphere_subset_closedBall hz) (hbound z hz)) htwo
  have haB : a ∈ ball c R := lt_of_le_of_ne haK (fun he => hbound a he haz)
  have hbB : b ∈ ball c R := lt_of_le_of_ne hbK (fun he => hbound b he hbz)
  refine ⟨hbound,a,haB,b,hbB,haz,hbz,?_⟩
  intro z hz
  have hz' : z ∈ closedBall c R := hz
  simpa only [if_pos hz'] using horders z

end NLS.KdV
