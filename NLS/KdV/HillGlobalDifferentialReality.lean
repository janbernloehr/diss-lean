import NLS.KdV.HillGlobalNormalizedDifferentials

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat NLS.FunctionalAnalysis
open scoped ENNReal ComplexConjugate

namespace NLS.KdV

variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

theorem hillAbelianPsiCandidate_conj
    (roots : ℕ → ℝ) (hroots : roots ∈ hillGapRootBox q hq hr) (n : ℕ) (E : ℂ) :
    hillAbelianPsiCandidate roots n (conj E) = conj (hillAbelianPsiCandidate roots n E) := by
  rw [← hillAbelianHilbertPsi_eq_genuine_candidate q hq hr roots hroots n (conj E),
    ← hillAbelianHilbertPsi_eq_genuine_candidate q hq hr roots hroots n E]
  have h := hillAbelianHilbertPsi_conj n E (hillGapRootHilbertCoordinates q hq hr roots hroots)
  rw [hillGapRootHilbertCoordinates_star q hq hr roots hroots] at h
  exact h

theorem hillAbelianCandidatePeriod_im_eq_zero
    (roots : ℕ → ℝ) (hroots : roots ∈ hillGapRootBox q hq hr) (n k : ℕ) (hk : 1 ≤ k) :
    (hillAbelianCandidatePeriod q hq hr roots n k).im = 0 := by
  change (hillIntrinsicGapPeriod q hq hr k (hillAbelianPsiCandidate roots n)).im = 0
  exact hillIntrinsicGapPeriod_im_eq_zero q hq hr k hk _
    (hillAbelianPsiCandidate_conj q hq hr roots hroots n)

theorem hillAbelianSelectedGlobalPsi_conj (n : ℕ) (hn : 1 ≤ n) (E : ℂ) :
    hillAbelianSelectedGlobalPsi q hq hr n hn (conj E) =
      conj (hillAbelianSelectedGlobalPsi q hq hr n hn E) := by
  have hreal := hillAbelianCandidatePeriod_im_eq_zero q hq hr
    (hillAbelianSelectedGlobalRoots q hq hr n hn).val
    (hillAbelianSelectedGlobalRoots q hq hr n hn).property n n hn
  unfold hillAbelianSelectedGlobalPsi
  rw [hillAbelianPsiCandidate_conj q hq hr _ (hillAbelianSelectedGlobalRoots q hq hr n hn).property n E,
    map_div₀,Complex.conj_eq_iff_im.mpr hreal]

theorem hillAbelianSelectedGlobalPsi_zero_iff (n : ℕ) (hn : 1 ≤ n) (E : ℂ) :
    hillAbelianSelectedGlobalPsi q hq hr n hn E = 0 ↔
      ∃ j : ℕ, j+1 ≠ n ∧ ((hillAbelianSelectedGlobalRoots q hq hr n hn).val j : ℂ) = E := by
  rw [hillAbelianSelectedGlobalPsi,div_eq_zero_iff]
  simp only [(hillAbelianSelectedGlobalRoots_periods q hq hr n hn).1,or_false]
  exact hillAbelianPsiCandidate_zero_iff q hq hr
    (hillAbelianSelectedGlobalRoots q hq hr n hn).val
    (hillAbelianSelectedGlobalRoots q hq hr n hn).property n hn E

end NLS.KdV
