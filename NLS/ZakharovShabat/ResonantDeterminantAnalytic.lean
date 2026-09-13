import NLS.ZakharovShabat.ResonantAnalytic
import NLS.ZakharovShabat.PeriodicResonantReduction

/-!
# The actual analytic resonant determinant

The scalar expression is the determinant of the reduced matrix, with the
source off-diagonal labels preserved. It is jointly analytic on the existing
correction domain and detects the original periodic spectrum there.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Total scalar extension of the actual reduced determinant. -/
def resonantDeterminantExtension (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) : ℂ :=
  (z - (Real.pi : ℂ)*n - weightedResonantAExtension hp w φ n z)^2 -
    weightedResonantBPlusExtension hp w φ n z * weightedResonantBMinusExtension hp w φ n z

/-- The scalar extension equals the determinant of the actual reduced matrix. -/
theorem resonantDeterminantExtension_eq_det (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1) :
    resonantDeterminantExtension hp w φ n z = (weightedResonantMatrix hp w φ n z hz h).det := by
  rw [resonantDeterminantExtension, weightedResonantAExtension_eq hp w φ n z hz h,
    weightedResonantBPlusExtension_eq hp w φ n z hz h, weightedResonantBMinusExtension_eq hp w φ n z hz h,
    weightedResonantMatrix_form]
  simp only [Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  ring

/-- Joint analyticity of the scalar determinant on the actual correction domain. -/
theorem analyticAt_resonantDeterminantExtension (hp : p ≠ ⊤) (w : SpectralWeight) (n : ℤ)
    (s : WeightedCoeffPair w.toWeight p × ℂ) (hs : s ∈ weightedCorrectionDomain hp w n) :
    AnalyticAt ℂ (fun t : WeightedCoeffPair w.toWeight p × ℂ => resonantDeterminantExtension hp w t.1 n t.2) s := by
  exact (((analyticAt_snd.sub analyticAt_const).sub
    (analyticAt_weightedResonantAExtension hp w n s hs)).pow 2).sub
      ((analyticAt_weightedResonantBPlusExtension hp w n s hs).mul
        (analyticAt_weightedResonantBMinusExtension hp w n s hs))

/-- Restricting the joint determinant to a fixed potential is analytic near each valid strip point. -/
theorem analyticAt_resonantDeterminantExtension_spectral (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ)
    (hs : (φ,z) ∈ weightedCorrectionDomain hp w n) :
    AnalyticAt ℂ (resonantDeterminantExtension hp w φ n) z :=
  (analyticAt_resonantDeterminantExtension hp w n (φ,z) hs).comp (analyticAt_const.prod analyticAt_id)

/-- One open convex neighborhood and cutoff give joint analyticity on every distant full strip. -/
theorem exists_uniform_analyticResonantDeterminant (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ n : ℤ, N ≤ n.natAbs →
        AnalyticOnNhd ℂ (fun s : WeightedCoeffPair w.toWeight p × ℂ => resonantDeterminantExtension hp w s.1 n s.2)
          (U ×ˢ resonantStrip n) := by
  obtain ⟨N,hN,U,ho,hc,hφ,h0,hb⟩ := exists_uniform_weightedCorrectionDomain hp w φ
  exact ⟨N,hN,U,ho,hc,hφ,h0, fun n hn s hs => analyticAt_resonantDeterminantExtension hp w n s (hb n hn hs)⟩

/-- The actual scalar determinant detects nonzero weighted periodic eigenvectors. -/
theorem weighted_eigenvector_iff_resonantDeterminantExtension_zero (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1) :
    (∃ f : WeightedDomain w.toWeight p, f ≠ 0 ∧ weightedFreePencil w.toWeight z f = weightedDomainPotential hp w φ f) ↔
      resonantDeterminantExtension hp w φ n z = 0 := by
  rw [resonantDeterminantExtension_eq_det hp w φ n z hz h]
  exact weighted_eigenvector_iff_resonant_det_zero hp w φ n z hz h

/-- For unit weight the scalar zeros are exactly the original periodic spectral points. -/
theorem mem_periodicSpectrum_iff_resonantDeterminantExtension_zero (hp : p ≠ ⊤) (φ : PairSpace p)
    (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp SpectralWeight.one (unitBaseEquiv.symm φ) n z hz‖ < 1) :
    z ∈ periodicSpectrum hp φ ↔ resonantDeterminantExtension hp SpectralWeight.one (unitBaseEquiv.symm φ) n z = 0 := by
  rw [resonantDeterminantExtension_eq_det hp SpectralWeight.one (unitBaseEquiv.symm φ) n z hz h]
  exact mem_periodicSpectrum_iff_resonant_det_zero hp φ n z hz h

/-- The zero-potential determinant is exactly the centered square, including at the center. -/
@[simp] theorem resonantDeterminantExtension_zero (hp : p ≠ ⊤) (w : SpectralWeight) (n : ℤ) (z : ℂ) :
    resonantDeterminantExtension hp w (0 : WeightedCoeffPair w.toWeight p) n z = (z - (Real.pi : ℂ)*n)^2 := by
  have hsource (i : Fin 2) : weightedResonantSource hp w (0 : WeightedCoeffPair w.toWeight p) n i = 0 := by
    rw [weightedResonantSource, ← weightedDomainPotentialCLM_apply, map_zero, zero_apply]
  have he (i j : Fin 2) : weightedCorrectionEntryExtension hp w (0 : WeightedCoeffPair w.toWeight p) n z i j = 0 := by
    simp [weightedCorrectionEntryExtension, hsource]
  simp [resonantDeterminantExtension, weightedResonantAExtension,
    weightedResonantBPlusExtension, weightedResonantBMinusExtension, he]

end NLS.ZakharovShabat
