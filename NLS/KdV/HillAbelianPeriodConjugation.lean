import NLS.KdV.HillFreeContourPhysicalRoot
import NLS.KdV.HillL2PrimitiveReflection
import NLS.ComplexAnalysis.RealCircleIntegralReflection

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



theorem hillAbelianComplexNumeratorFactor_conj (n j : ℕ) (E : ℂ) (a : Coeff 2) :
    hillAbelianComplexNumeratorFactor n (conj E,star a) j =
      conj (hillAbelianComplexNumeratorFactor n (E,a) j) := by
  unfold hillAbelianComplexNumeratorFactor
  split_ifs
  · simp only [map_one]
  · simp only [lp.star_apply,map_div₀,map_sub,map_add,map_mul,map_natCast,conj_ofReal]
    rfl

theorem hillAbelianHilbertProduct_conj (n : ℕ) (E : ℂ) (a : Coeff 2) :
    hillAbelianHilbertProduct n (conj E,star a) = conj (hillAbelianHilbertProduct n (E,a)) := by
  rw [hillAbelianHilbertProduct_eq_tprod,hillAbelianHilbertProduct_eq_tprod]
  have h := (multipliable_hillAbelianComplexNumeratorFactors n (E,a)).map_tprod (starRingEnd ℂ) continuous_star
  change conj (∏' j : ℕ,hillAbelianComplexNumeratorFactor n (E,a) j) =
    ∏' j : ℕ,conj (hillAbelianComplexNumeratorFactor n (E,a) j) at h
  rw [h]
  exact tprod_congr (fun j => hillAbelianComplexNumeratorFactor_conj n j E a)

theorem hillAbelianHilbertPsi_conj (n : ℕ) (E : ℂ) (a : Coeff 2) :
    hillAbelianHilbertPsi n (conj E,star a) = conj (hillAbelianHilbertPsi n (E,a)) := by
  rw [hillAbelianHilbertPsi,hillAbelianHilbertPsi,hillAbelianHilbertProduct_conj]
  simp only [map_mul,map_div₀,map_ofNat,map_natCast,conj_ofReal]

variable
    (hq : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem hillAbelianComplexRoot_conj_on_free_contour (ε D : ℝ) (hc : HillComplexPeriodControl hq hr ε D)
    (p : Coeff 2) (hp : ‖p‖ ≤ ε) (hreal : IsRealHillPotential p) (k : ℕ) (hk : 1 ≤ k) (E : ℂ)
    (hE : E ∈ sphere (hillRealGapCenter 0 hq hr k : ℂ)
      (hillRealGapHalfLength 0 hq hr k+hillRealGapCollar 0 hq hr k)) :
    hillAbelianComplexRoot 0 hq hr (conj E,p) = -conj (hillAbelianComplexRoot 0 hq hr (E,p)) := by
  have hEc : conj E ∈ sphere (hillRealGapCenter 0 hq hr k : ℂ)
      (hillRealGapHalfLength 0 hq hr k+hillRealGapCollar 0 hq hr k) := by
    simpa only [mem_sphere,dist_conj_comm,conj_ofReal] using hE
  have hs := hillFreeGapContour_source_compatibility hq hr ε D hc p hp k hk E hE
  rw [(hillFreeGapContour_source_compatibility hq hr ε D hc p hp k hk (conj E) hEc).2,hs.2,
    hillL2ContinuedRoot_conj p hreal E hs.1]

theorem hillAbelianComplexPeriod_conj_roots (ε D : ℝ) (hc : HillComplexPeriodControl hq hr ε D)
    (n k : ℕ) (hk : 1 ≤ k) (a p : Coeff 2) (hp : ‖p‖ ≤ ε) (hreal : IsRealHillPotential p) :
    hillAbelianComplexPeriod 0 hq hr n k (star a,p) = conj (hillAbelianComplexPeriod 0 hq hr n k (a,p)) := by
  have hR : 0 < hillRealGapHalfLength 0 hq hr k+hillRealGapCollar 0 hq hr k :=
    add_pos_of_nonneg_of_pos (hillRealGapContour_geometry 0 hq hr k hk).1
      (hillRealGapContour_geometry 0 hq hr k hk).2.1
  have he := circleIntegral_eq_conj_of_anti_conj
    (fun E => hillAbelianHilbertPsi n (E,a)/hillAbelianComplexRoot 0 hq hr (E,p))
    (fun E => hillAbelianHilbertPsi n (E,star a)/hillAbelianComplexRoot 0 hq hr (E,p))
    (hillRealGapCenter 0 hq hr k) (hillRealGapHalfLength 0 hq hr k+hillRealGapCollar 0 hq hr k) hR (by
      intro E hE
      rw [hillAbelianHilbertPsi_conj,hillAbelianComplexRoot_conj_on_free_contour hq hr ε D hc p hp hreal k hk E hE]
      simp only [map_div₀,div_neg])
  unfold hillAbelianComplexPeriod
  rw [he]
  simp only [map_mul,map_inv₀,map_ofNat,conj_ofReal]

end NLS.KdV
