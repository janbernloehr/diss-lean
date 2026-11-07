import NLS.KdV.PseudomeasureConjugation
import NLS.KdV.PseudomeasureDiagonalRoot

/-! Physical conjugation of the actual intrinsic diagonal root. -/
noncomputable section
open scoped ENNReal
namespace NLS.KdV

/-- The constructed auxiliary root commutes with physical conjugation,
by uniqueness on the entire corrected strip. No spectral midpoint assertion is used. -/
theorem endpointHillDiagonalRoot_conj (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (n : ℕ) (hn : 1 ≤ n) (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2) :
    endpointHillDiagonalRoot r hr hr1 n hn (endpointConjugate SpectralWeight.one r q) =
      (starRingEnd ℂ) (endpointHillDiagonalRoot r hr hr1 n hn q) := by
  obtain ⟨hstrip, hroot, _⟩ := endpointHillDiagonalRoot_spec r hr hr1 n hn q hs
  symm
  apply endpointHillDiagonalRoot_unique r hr hr1 n hn (endpointConjugate SpectralWeight.one r q)
    (by simpa only [norm_endpointConjugate] using hs) _
    (mem_reducedHillStrip_conj n _ hstrip)
  rw [(endpointCoefficients_conj r hr hr1 n hn _ hstrip q hs).1]
  simpa only [map_add, Complex.conj_ofReal] using congrArg (starRingEnd ℂ) hroot

/-- A real physical potential has a real actual diagonal root. -/
theorem endpointHillDiagonalRoot_im_eq_zero (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (n : ℕ) (hn : 1 ≤ n) (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2)
    (hq : endpointConjugate SpectralWeight.one r q = q) :
    (endpointHillDiagonalRoot r hr hr1 n hn q).im = 0 := by
  have hh := endpointHillDiagonalRoot_conj r hr hr1 n hn q hs
  rw [hq] at hh
  have hi := congrArg Complex.im hh
  simp only [Complex.conj_im] at hi
  linarith

end NLS.KdV
