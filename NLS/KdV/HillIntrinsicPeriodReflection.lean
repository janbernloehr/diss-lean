import NLS.KdV.HillEntirePeriodInterpolation
import NLS.KdV.HillGlobalDifferentialReality

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV

variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

theorem hillAbelianNumeratorProduct_conj
    (roots : ℕ → ℝ) (hroots : roots ∈ hillGapRootBox q hq hr) (n : ℕ) (E : ℂ) :
    hillAbelianNumeratorProduct roots n (conj E) = conj (hillAbelianNumeratorProduct roots n E) := by
  let a := hillGapRootHilbertCoordinates q hq hr roots hroots
  have he (z : ℂ) : hillAbelianHilbertProduct n (z,a) = hillAbelianNumeratorProduct roots n z :=
    hillAbelianHilbertProduct_eq_real_numerator n z a roots (hillGapRootHilbertCoordinates_reconstruct q hq hr roots hroots)
  rw [← he (conj E),← he E]
  have ha : star a = a := hillGapRootHilbertCoordinates_star q hq hr roots hroots
  simpa only [ha] using hillAbelianHilbertProduct_conj n E a

theorem hillIntrinsicGapPeriod_reflection (k : ℕ) (hk : 1 ≤ k) (N : ℂ → ℂ) :
    hillIntrinsicGapPeriod q hq hr k (fun E => conj (N (conj E))) =
      conj (hillIntrinsicGapPeriod q hq hr k N) := by
  have hR : 0 < hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k :=
    add_pos_of_nonneg_of_pos (hillRealGapContour_geometry q hq hr k hk).1
      (hillRealGapContour_geometry q hq hr k hk).2.1
  have hi := circleIntegral_eq_conj_of_anti_conj
    (fun E => N E/hillEnergyCanonicalRootProduct q hq hr E)
    (fun E => conj (N (conj E))/hillEnergyCanonicalRootProduct q hq hr E)
    (hillRealGapCenter q hq hr k) _ hR (by
      intro E hE
      rw [conj_conj,hillEnergyCanonicalRootProduct_conj q hq hr E
        (hillRealGapContour_sphere_subset q hq hr k hk hE)]
      simp only [div_neg,map_div₀])
  unfold hillIntrinsicGapPeriod
  rw [hi,map_mul]
  simp only [map_inv₀,map_mul,map_ofNat,conj_ofReal]

end NLS.KdV
