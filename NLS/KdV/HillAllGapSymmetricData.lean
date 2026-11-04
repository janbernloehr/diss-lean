import NLS.KdV.HillComplexLowGapPairs
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

def hillLocalGapMidpoint (k : ℕ) (p : Coeff 2) : ℂ :=
  logarithmicCircleMoment (fun t : ℂ × Coeff 2 => hillL2Radicand t.2 t.1)
    (hillRealGapCenter q hq hr k : ℂ)
    (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k) 1 p / 2

def hillLocalGapSquare (k : ℕ) (p : Coeff 2) : ℂ :=
  2*logarithmicCircleMoment (fun t : ℂ × Coeff 2 => hillL2Radicand t.2 t.1)
    (hillRealGapCenter q hq hr k : ℂ)
    (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k) 2 p -
  (logarithmicCircleMoment (fun t : ℂ × Coeff 2 => hillL2Radicand t.2 t.1)
    (hillRealGapCenter q hq hr k : ℂ)
    (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k) 1 p)^2

theorem hillLocalGapSymmetricData_eq_of_pair (k : ℕ) (hk : 1 ≤ k) (p : Coeff 2)
    (hb : ∀ z ∈ sphere (hillRealGapCenter q hq hr k : ℂ)
      (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k), hillL2Radicand p z ≠ 0)
    {a b : ℂ}
    (ha : a ∈ ball (hillRealGapCenter q hq hr k : ℂ)
      (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k))
    (hb' : b ∈ ball (hillRealGapCenter q hq hr k : ℂ)
      (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k))
    (hm : ∀ z ∈ closedBall (hillRealGapCenter q hq hr k : ℂ)
      (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k),
      analyticOrderNatAt (hillL2Radicand p) z = ({a,b} : Multiset ℂ).count z) :
    hillLocalGapMidpoint q hq hr k p = (a+b)/2 ∧
    hillLocalGapSquare q hq hr k p = (b-a)^2 := by
  have hR := add_pos_of_nonneg_of_pos (hillRealGapContour_geometry q hq hr k hk).1
    (hillRealGapContour_geometry q hq hr k hk).2.1
  have hF := (analyticOnNhd_hillL2Radicand p).mono
    (subset_univ (closedBall (hillRealGapCenter q hq hr k : ℂ)
      (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k)))
  have h1 := logarithmicCircleMoment_eq_two_root_powers
    (fun t : ℂ × Coeff 2 => hillL2Radicand t.2 t.1) p hR 1 hF hb ha hb' hm
  have h2 := logarithmicCircleMoment_eq_two_root_powers
    (fun t : ℂ × Coeff 2 => hillL2Radicand t.2 t.1) p hR 2 hF hb ha hb' hm
  constructor
  · simp only [hillLocalGapMidpoint, h1, pow_one]
  · simp only [hillLocalGapSquare, h1, h2, pow_one]
    ring

theorem exists_hillLocalGapSymmetricData_analytic_neighborhood (k : ℕ) (hk : 1 ≤ k) :
    ∃ V : Set (Coeff 2), IsOpen V ∧ SpectralWeight.one.toCoeff q ∈ V ∧
      AnalyticOnNhd ℂ (hillLocalGapMidpoint q hq hr k) V ∧
      AnalyticOnNhd ℂ (hillLocalGapSquare q hq hr k) V ∧
      ∀ p ∈ V, ∃ a b : ℂ, hillL2Radicand p a = 0 ∧ hillL2Radicand p b = 0 ∧
        hillLocalGapMidpoint q hq hr k p = (a+b)/2 ∧
        hillLocalGapSquare q hq hr k p = (b-a)^2 := by
  obtain ⟨V,hV,hqV,hpair⟩ := exists_hillComplexGapPair_neighborhood q hq hr k hk
  have hR := (add_pos_of_nonneg_of_pos (hillRealGapContour_geometry q hq hr k hk).1
    (hillRealGapContour_geometry q hq hr k hk).2.1).le
  have hm (j : ℕ) := analyticOnNhd_logarithmicCircleMoment
    (fun t : ℂ × Coeff 2 => hillL2Radicand t.2 t.1) analyticOnNhd_hillL2Radicand_joint
    (hillRealGapCenter q hq hr k : ℂ)
    (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k) hR j hV
    (fun p hp => (hpair p hp).1)
  refine ⟨V,hV,hqV,(hm 1).div_const (c := 2),?_,?_⟩
  · exact (analyticOnNhd_const.mul (hm 2)).sub ((hm 1).pow 2)
  · intro p hp
    obtain ⟨hb,a,ha,b,hb',haz,hbz,horders⟩ := hpair p hp
    exact ⟨a,b,haz,hbz,hillLocalGapSymmetricData_eq_of_pair q hq hr k hk p hb ha hb' horders⟩

end NLS.KdV
