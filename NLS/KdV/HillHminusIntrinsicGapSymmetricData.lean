import NLS.KdV.HillHminusIntrinsicGapPairs
import NLS.KdV.HillLocalGapPhysicalMatching
import NLS.ComplexAnalysis.AnalyticLogarithmicMoments

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

def hillHminusIntrinsicGapMidpoint (k : ℕ) (p : PeriodOneHminusOne) : ℂ :=
  logarithmicCircleMoment (fun t : ℂ × PeriodOneHminusOne => hillHminusRadicand t.2 t.1)
    (hillRealGapCenter q hq hr k : ℂ)
    (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k) 1 p / 2

def hillHminusIntrinsicGapSquare (k : ℕ) (p : PeriodOneHminusOne) : ℂ :=
  2*logarithmicCircleMoment (fun t : ℂ × PeriodOneHminusOne => hillHminusRadicand t.2 t.1)
    (hillRealGapCenter q hq hr k : ℂ)
    (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k) 2 p -
  (logarithmicCircleMoment (fun t : ℂ × PeriodOneHminusOne => hillHminusRadicand t.2 t.1)
    (hillRealGapCenter q hq hr k : ℂ)
    (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k) 1 p)^2

theorem hillHminusIntrinsicGapSymmetricData_eq_of_pair (k : ℕ) (hk : 1 ≤ k) (p : PeriodOneHminusOne)
    (hb : ∀ z ∈ sphere (hillRealGapCenter q hq hr k : ℂ)
      (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k), hillHminusRadicand p z ≠ 0)
    {a b : ℂ}
    (ha : a ∈ ball (hillRealGapCenter q hq hr k : ℂ)
      (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k))
    (hb' : b ∈ ball (hillRealGapCenter q hq hr k : ℂ)
      (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k))
    (hm : ∀ z ∈ closedBall (hillRealGapCenter q hq hr k : ℂ)
      (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k),
      analyticOrderNatAt (hillHminusRadicand p) z = ({a,b} : Multiset ℂ).count z) :
    hillHminusIntrinsicGapMidpoint q hq hr k p = (a+b)/2 ∧
    hillHminusIntrinsicGapSquare q hq hr k p = (b-a)^2 := by
  have hR := add_pos_of_nonneg_of_pos (hillRealGapContour_geometry q hq hr k hk).1
    (hillRealGapContour_geometry q hq hr k hk).2.1
  have hF := (analyticOnNhd_hillHminusRadicand p).mono
    (subset_univ (closedBall (hillRealGapCenter q hq hr k : ℂ)
      (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k)))
  have h1 := logarithmicCircleMoment_eq_two_root_powers
    (fun t : ℂ × PeriodOneHminusOne => hillHminusRadicand t.2 t.1) p hR 1 hF hb ha hb' hm
  have h2 := logarithmicCircleMoment_eq_two_root_powers
    (fun t : ℂ × PeriodOneHminusOne => hillHminusRadicand t.2 t.1) p hR 2 hF hb ha hb' hm
  constructor
  · simp only [hillHminusIntrinsicGapMidpoint, h1, pow_one]
  · simp only [hillHminusIntrinsicGapSquare, h1, h2, pow_one]
    ring

theorem exists_hillHminusIntrinsicGapSymmetricData_analytic_neighborhood (k : ℕ) (hk : 1 ≤ k) :
    ∃ V : Set (PeriodOneHminusOne), IsOpen V ∧ hillOriginalHminusSource q ∈ V ∧
      AnalyticOnNhd ℂ (hillHminusIntrinsicGapMidpoint q hq hr k) V ∧
      AnalyticOnNhd ℂ (hillHminusIntrinsicGapSquare q hq hr k) V ∧
      ∀ p ∈ V, ∃ a b : ℂ, hillHminusRadicand p a = 0 ∧ hillHminusRadicand p b = 0 ∧
        hillHminusIntrinsicGapMidpoint q hq hr k p = (a+b)/2 ∧
        hillHminusIntrinsicGapSquare q hq hr k p = (b-a)^2 := by
  obtain ⟨V,hV,hqV,hpair⟩ := exists_hillHminusIntrinsicGapPair_neighborhood q hq hr k hk
  have hR := (add_pos_of_nonneg_of_pos (hillRealGapContour_geometry q hq hr k hk).1
    (hillRealGapContour_geometry q hq hr k hk).2.1).le
  have hm (j : ℕ) := analyticOnNhd_logarithmicCircleMoment_of_isOpen
    (fun t : ℂ × PeriodOneHminusOne => hillHminusRadicand t.2 t.1) analyticOnNhd_hillHminusRadicand_joint
    (hillRealGapCenter q hq hr k : ℂ)
    (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k) hR j hV
    (fun p hp => (hpair p hp).1)
  refine ⟨V,hV,hqV,(hm 1).div_const (c := 2),?_,?_⟩
  · exact (analyticOnNhd_const.mul (hm 2)).sub ((hm 1).pow 2)
  · intro p hp
    obtain ⟨hb,a,ha,b,hb',haz,hbz,horders⟩ := hpair p hp
    exact ⟨a,b,haz,hbz,hillHminusIntrinsicGapSymmetricData_eq_of_pair q hq hr k hk p hb ha hb' horders⟩

/-- The intrinsic midpoint retains the literal ORIGINAL coefficient
restriction at EVERY original even source, with no closeness assumption. -/
theorem hillHminusIntrinsicGapMidpoint_original_source (k : ℕ)
    (p : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hp : SpectralWeight.one.toCoeff p ∈ Coeff.paritySubspace 0) :
    hillHminusIntrinsicGapMidpoint q hq hr k (hillOriginalHminusSource p) =
      hillLocalGapMidpoint q hq hr k (SpectralWeight.one.toCoeff p) := by
  have he : hillHminusRadicand (hillOriginalHminusSource p) = hillL2Radicand (SpectralWeight.one.toCoeff p) :=
    funext (hillHminusRadicand_original_source_agreement p hp)
  simp only [hillHminusIntrinsicGapMidpoint,hillLocalGapMidpoint,logarithmicCircleMoment]
  simp_rw [he]

/-- The squared FULL gap has the same exact all-source restriction. -/
theorem hillHminusIntrinsicGapSquare_original_source (k : ℕ)
    (p : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hp : SpectralWeight.one.toCoeff p ∈ Coeff.paritySubspace 0) :
    hillHminusIntrinsicGapSquare q hq hr k (hillOriginalHminusSource p) =
      hillLocalGapSquare q hq hr k (SpectralWeight.one.toCoeff p) := by
  have he : hillHminusRadicand (hillOriginalHminusSource p) = hillL2Radicand (SpectralWeight.one.toCoeff p) :=
    funext (hillHminusRadicand_original_source_agreement p hp)
  simp only [hillHminusIntrinsicGapSquare,hillLocalGapSquare,logarithmicCircleMoment]
  simp_rw [he]

theorem exists_hillHminusIntrinsicGapSymmetricData_physical_neighborhood (k : ℕ) (hk : 1 ≤ k) :
    ∃ W : Set RealPeriodOneHillPotential, IsOpen W ∧
      (⟨q,hq,hr⟩ : RealPeriodOneHillPotential) ∈ W ∧ ∀ p ∈ W,
        hillHminusIntrinsicGapMidpoint q hq hr k (hillOriginalHminusSource p.val) =
          (hillRealGapCenter p.val p.property.1 p.property.2 k : ℂ) ∧
        hillHminusIntrinsicGapSquare q hq hr k (hillOriginalHminusSource p.val) =
          (2*(hillRealGapHalfLength p.val p.property.1 p.property.2 k : ℂ))^2 := by
  obtain ⟨W,hW,hqW,hM⟩ := exists_hillLocalGapSymmetricData_physical_neighborhood q hq hr k hk
  refine ⟨W,hW,hqW,?_⟩
  intro p hp
  rw [hillHminusIntrinsicGapMidpoint_original_source q hq hr k p.val p.property.1,
    hillHminusIntrinsicGapSquare_original_source q hq hr k p.val p.property.1]
  exact hM p hp

end NLS.KdV
