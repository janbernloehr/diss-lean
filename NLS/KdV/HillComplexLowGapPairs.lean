import NLS.KdV.HillAllGapMultiplicities
import NLS.KdV.HillAbelianComplexPeriods
import NLS.ComplexAnalysis.ZeroCountHomotopy
import NLS.ComplexAnalysis.ZeroMultiset

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



theorem continuous_hillL2Radicand_parameter_energy :
    Continuous (Function.uncurry (fun p : Coeff 2 => hillL2Radicand p)) := by
  have hC : Continuous (fun t : ℂ × Coeff 2 => hillL2Radicand t.2 t.1) :=
    continuous_iff_continuousAt.mpr
      (fun t => (analyticOnNhd_hillL2Radicand_joint t (mem_univ _)).continuousAt)
  apply (hC.comp (continuous_swap : Continuous (Prod.swap : Coeff 2 × ℂ → ℂ × Coeff 2))).congr
  intro t
  rfl

variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

theorem exists_hillComplexGapPair_neighborhood (k : ℕ) (hk : 1 ≤ k) :
    ∃ V : Set (Coeff 2), IsOpen V ∧ SpectralWeight.one.toCoeff q ∈ V ∧
      ∀ p ∈ V,
        (∀ z ∈ sphere (hillRealGapCenter q hq hr k : ℂ)
          (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k), hillL2Radicand p z ≠ 0) ∧
        ∃ a ∈ ball (hillRealGapCenter q hq hr k : ℂ)
          (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k),
        ∃ b ∈ ball (hillRealGapCenter q hq hr k : ℂ)
          (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k),
          hillL2Radicand p a = 0 ∧ hillL2Radicand p b = 0 ∧
          ∀ z ∈ closedBall (hillRealGapCenter q hq hr k : ℂ)
            (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k),
            analyticOrderNatAt (hillL2Radicand p) z = ({a,b} : Multiset ℂ).count z := by
  let c : ℂ := hillRealGapCenter q hq hr k
  let R := hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k
  have hR : 0 < R := add_pos_of_nonneg_of_pos (hillRealGapContour_geometry q hq hr k hk).1
    (hillRealGapContour_geometry q hq hr k hk).2.1
  have hbase (z : ℂ) (hz : z ∈ sphere c R) : hillL2Radicand (SpectralWeight.one.toCoeff q) z ≠ 0 :=
    hillL2Radicand_ne_zero_on_realCutDomain q hq hr z (hillRealGapContour_sphere_subset q hq hr k hk hz)
  have hcount := eventually_analyticZeroCount_eq_of_continuous_family
    (fun p : Coeff 2 => hillL2Radicand p) c R hR continuous_hillL2Radicand_parameter_energy.continuousOn
      (fun p => (analyticOnNhd_hillL2Radicand p).mono (subset_univ _)) (SpectralWeight.one.toCoeff q) hbase
  obtain ⟨V,hV,hqV,hdom⟩ := exists_hillAbelianComplexRoot_contour_neighborhood q hq hr k hk
  obtain ⟨W,hWsub,hW,hqW⟩ := _root_.mem_nhds_iff.mp hcount
  refine ⟨V ∩ W,hV.inter hW,⟨hqV,hqW⟩,?_⟩
  intro p hp
  have hbound (z : ℂ) (hz : z ∈ sphere c R) : hillL2Radicand p z ≠ 0 := by
    rw [← hillAbelianComplexRoot_sq q hq hr _ (hdom p hp.1 z hz)]
    exact pow_ne_zero 2 (hillAbelianComplexRoot_ne_zero q hq hr _ (hdom p hp.1 z hz))
  have htwo : analyticZeroCount (hillL2Radicand p) (closedBall c R) = 2 :=
    (hWsub hp.2).trans (analyticZeroCount_hillL2Radicand_intrinsic_gap q hq hr k hk)
  obtain ⟨z,hz⟩ := (NormedSpace.sphere_nonempty (E := ℂ) (x := c)).mpr hR.le
  have ha := (analyticOnNhd_hillL2Radicand p).mono (subset_univ (closedBall c R))
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
