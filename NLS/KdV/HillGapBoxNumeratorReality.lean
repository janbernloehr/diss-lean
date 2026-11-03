import NLS.KdV.HillAbelianNormalizationProblem
import NLS.KdV.HillAbelianProductZeros
import NLS.KdV.HillDeflatedCanonicalRootPhase

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate unitInterval

namespace NLS.KdV

variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

theorem hillAbelianPsiCandidate_im_eq_zero
    (roots : ℕ → ℝ) (hroots : roots ∈ hillGapRootBox q hq hr) (n : ℕ) (x : ℝ) :
    (hillAbelianPsiCandidate roots n x).im = 0 := by
  have hf (j : ℕ) : conj (hillAbelianNumeratorFactor roots n j x) =
      hillAbelianNumeratorFactor roots n j x := by
    unfold hillAbelianNumeratorFactor
    split_ifs
    · exact map_one _
    · simp only [hillGapRootEnergyFactor,← ofReal_sub,← ofReal_div,conj_ofReal]
  have hp := (multipliable_hillAbelianNumeratorFactors q hq hr roots hroots n x).map_tprod
    (starRingEnd ℂ) continuous_star
  change conj (∏' j : ℕ, hillAbelianNumeratorFactor roots n j x) =
    ∏' j : ℕ, conj (hillAbelianNumeratorFactor roots n j x) at hp
  have hc : conj (hillAbelianNumeratorProduct roots n x) = hillAbelianNumeratorProduct roots n x := by
    rw [hillAbelianNumeratorProduct,hp]
    exact tprod_congr hf
  have hψ : conj (hillAbelianPsiCandidate roots n x) = hillAbelianPsiCandidate roots n x := by
    rw [hillAbelianPsiCandidate,map_mul,hc]
    congr 1
    simp only [map_div₀,map_ofNat,map_mul,map_natCast,conj_ofReal]
  have hi := congrArg Complex.im hψ
  simp only [Complex.conj_im] at hi
  linarith

theorem hillAbelianPsiCandidate_ne_zero_on_own_gap
    (roots : ℕ → ℝ) (hroots : roots ∈ hillGapRootBox q hq hr) (n : ℕ) (hn : 1 ≤ n)
    (E : ℂ) (hE : E ∈ segment ℝ (hillRealLabels q hq hr (2*n-1) : ℂ)
      (hillRealLabels q hq hr (2*n) : ℂ)) : hillAbelianPsiCandidate roots n E ≠ 0 := by
  intro hzero
  obtain ⟨j,hj,he⟩ := (hillAbelianPsiCandidate_zero_iff q hq hr roots hroots n hn E).mp hzero
  have hx := re_mem_Icc_of_mem_real_segment _ _
    (monotone_hillRealLabels q hq hr (by omega : 2*n-1 ≤ 2*n)) E hE
  have hroot := hroots j
  have heR : roots j = E.re := by simpa only [ofReal_re] using congrArg Complex.re he
  rcases hillRealGap_exterior_to_other_gap q hq hr n (j+1) hn (by omega) hj E.re hx with hl | hu
  · linarith [hroot.1]
  · linarith [hroot.2]

end NLS.KdV
