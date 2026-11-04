import NLS.KdV.HillGapRootHilbertCoordinates
import NLS.KdV.HillAbelianNormalizationProblem
import NLS.ComplexAnalysis.ParametricCircleIntegralHigher

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal

namespace NLS.KdV

variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

def hillAbelianHilbertPeriod (n k : ℕ) (a : Coeff 2) : ℂ :=
  (2*(Real.pi : ℂ))⁻¹ * ∮ z in C((hillRealGapCenter q hq hr k : ℂ),
    hillRealGapHalfLength q hq hr k + hillRealGapCollar q hq hr k),
      hillAbelianHilbertPsi n (z,a)/hillEnergyCanonicalRootProduct q hq hr z

theorem analyticOnNhd_hillAbelianHilbertPeriod (n k : ℕ) (hk : 1 ≤ k) :
    AnalyticOnNhd ℂ (hillAbelianHilbertPeriod q hq hr n k) univ := by
  let D : Set (ℂ × Coeff 2) := hillL2RealCutDomain q hq hr ×ˢ univ
  let F : ℂ × Coeff 2 → ℂ := fun t =>
    hillAbelianHilbertPsi n t / hillEnergyCanonicalRootProduct q hq hr t.1
  have hD : IsOpen D := (isOpen_hillL2RealCutDomain q hq hr).prod isOpen_univ
  have hF : AnalyticOnNhd ℂ F D := by
    intro t ht
    have hd : AnalyticAt ℂ (fun v : ℂ × Coeff 2 =>
        hillEnergyCanonicalRootProduct q hq hr v.1) t :=
      (analyticOnNhd_hillEnergyCanonicalRootProduct q hq hr t.1 ht.1).comp analyticAt_fst
    exact (analyticOnNhd_hillAbelianHilbertPsi n t (mem_univ _)).div hd
      (hillEnergyCanonicalRootProduct_ne_zero_on_realCutDomain q hq hr t.1 ht.1)
  have hR := add_nonneg (hillRealGapContour_geometry q hq hr k hk).1
    (hillRealGapContour_geometry q hq hr k hk).2.1.le
  have hc := analyticOnNhd_circleIntegral_of_jointAnalytic F hD hF
    (hillRealGapCenter q hq hr k : ℂ)
    (hillRealGapHalfLength q hq hr k + hillRealGapCollar q hq hr k) hR isOpen_univ
    (fun _ _ z hz => ⟨hillRealGapContour_sphere_subset q hq hr k hk hz,mem_univ _⟩)
  exact analyticOnNhd_const.mul hc

theorem hillAbelianHilbertPeriod_eq_genuine_period
    (σ : ℕ → ℝ) (hσ : σ ∈ hillGapRootBox q hq hr) (n k : ℕ) :
    hillAbelianHilbertPeriod q hq hr n k (hillGapRootHilbertCoordinates q hq hr σ hσ) =
      hillAbelianCandidatePeriod q hq hr σ n k := by
  unfold hillAbelianHilbertPeriod hillAbelianCandidatePeriod
  congr 1
  congr 1
  funext energy
  rw [hillAbelianHilbertPsi_eq_genuine_candidate q hq hr σ hσ n energy]

end NLS.KdV
