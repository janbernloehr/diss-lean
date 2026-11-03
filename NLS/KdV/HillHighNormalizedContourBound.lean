import NLS.KdV.HillContourHilbertPsiBounds
import NLS.KdV.HillBoundedComplexTailPeriodControl
import NLS.KdV.HillHighCanonicalRootMatching
import NLS.KdV.HillGlobalNormalizedDifferentials
import NLS.KdV.HillGapRootHilbertCoordinates

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

theorem exists_hillAbelianSelectedGlobalPsi_scaled_high_contour_bound (n : ℕ) (hn : 1 ≤ n) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, N ≤ k → n ≠ k → ∀ E ∈
      sphere (hillRealGapCenter 0 h0q h0r k : ℂ)
        (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k),
      ‖(((freeHillValue k : ℂ)-(freeHillValue n : ℂ))/(n : ℂ))*
        (hillAbelianSelectedGlobalPsi q hq hr n hn E/hillEnergyCanonicalRootProduct q hq hr E)‖ ≤ C/(k : ℝ) := by
  let p := SpectralWeight.one.toCoeff q
  obtain ⟨N,hN,D,hD,hcontrol⟩ := exists_hillAbelianComplexPeriod_bounded_tail_control h0q h0r ‖p‖
  obtain ⟨M,hM,A,hA,hinverse⟩ := exists_hillFreeGapContour_bounded_complex_tail_inverse_bound h0q h0r ‖p‖
  let roots := hillAbelianSelectedGlobalRoots q hq hr n hn
  let a := hillGapRootHilbertCoordinates q hq hr roots.val roots.property
  let P := hillAbelianCandidatePeriod q hq hr roots.val n n
  have hP : P ≠ 0 := (hillAbelianSelectedGlobalRoots_periods q hq hr n hn).1
  refine ⟨max N M, hN.trans (le_max_left _ _),
    4*Real.exp ((8/Real.pi^2)*‖a‖)*(1+A*‖p‖)/‖P‖, by positivity,?_⟩
  intro k hk hnk E hE
  have hk1 := hN.trans ((le_max_left N M).trans hk)
  have hmatch := (hillHighFreeGapContour_physical_root_matching h0q h0r N hN ‖p‖ D hcontrol q hq hr le_rfl k
    ((le_max_left N M).trans hk) E hE).2
  have hinv := (hinverse p le_rfl k ((le_max_right N M).trans hk) E hE).2
  have hkreal : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hratio : ‖hillEnergyCanonicalRootProduct 0 h0q h0r E / hillEnergyCanonicalRootProduct q hq hr E‖ ≤ 1+A*‖p‖ := by
    rw [hmatch] at hinv
    have h := norm_le_norm_sub_add (hillEnergyCanonicalRootProduct 0 h0q h0r E/hillEnergyCanonicalRootProduct q hq hr E) 1
    have hdiv : A*‖p‖/(k : ℝ) ≤ A*‖p‖ := div_le_self (by positivity) hkreal
    rw [norm_one] at h
    exact h.trans (by linarith)
  have hfree := norm_scaled_hillAbelianHilbertPsi_free_root_le h0q h0r n k hn hk1 hnk E hE a
  have hroot : hillEnergyCanonicalRootProduct 0 h0q h0r E ≠ 0 :=
    hillEnergyCanonicalRootProduct_ne_zero_on_realCutDomain 0 h0q h0r E
      (hillRealGapContour_sphere_subset 0 h0q h0r k hk1 hE)
  have he : (((freeHillValue k : ℂ)-(freeHillValue n : ℂ))/(n : ℂ))*
      (hillAbelianSelectedGlobalPsi q hq hr n hn E/hillEnergyCanonicalRootProduct q hq hr E) =
      ((((freeHillValue k : ℂ)-(freeHillValue n : ℂ))/(n : ℂ))*
        (hillAbelianHilbertPsi n (E,a)/hillEnergyCanonicalRootProduct 0 h0q h0r E))*
          (hillEnergyCanonicalRootProduct 0 h0q h0r E/hillEnergyCanonicalRootProduct q hq hr E)/P := by
    rw [hillAbelianSelectedGlobalPsi]
    rw [hillAbelianHilbertPsi_eq_genuine_candidate q hq hr roots.val roots.property n E]
    dsimp only [P,roots]
    field_simp
  rw [he,norm_div,norm_mul]
  apply (div_le_div_of_nonneg_right (mul_le_mul hfree hratio (norm_nonneg _) (by positivity)) (norm_nonneg P)).trans_eq
  ring

end NLS.KdV
