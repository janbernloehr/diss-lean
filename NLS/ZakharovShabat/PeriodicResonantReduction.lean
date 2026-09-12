import NLS.ZakharovShabat.WeightedResonantReduction
import NLS.ZakharovShabat.UnitWeightedRealization

/-!
# Section 6, Lemma 6.6: the periodic determinant criterion

The unit-weight realization identifies the resonant determinant criterion with
the original periodic spectrum. The small-square hypothesis holds throughout
all sufficiently distant full closed strips, locally uniformly in the potential.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The small-square condition in the exact source norm for an original periodic potential. -/
def PeriodicReductionSmall (hp : p ≠ ⊤) (φ : PairSpace p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) : Prop :=
  ‖weightedPotentialSquareInShift hp SpectralWeight.one (unitBaseEquiv.symm φ) n z hz‖ < 1

/-- The source's matrix `S_n` for the original periodic potential. -/
def periodicResonantMatrix (hp : p ≠ ⊤) (φ : PairSpace p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : PeriodicReductionSmall hp φ n z hz) : Matrix (Fin 2) (Fin 2) ℂ :=
  weightedResonantMatrix hp SpectralWeight.one (unitBaseEquiv.symm φ) n z hz h

/-- Lemma 6.6: an original periodic spectral parameter is an eigenvalue exactly when `det S_n=0`. -/
theorem mem_periodicSpectrum_iff_resonant_det_zero (hp : p ≠ ⊤) (φ : PairSpace p)
    (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) (h : PeriodicReductionSmall hp φ n z hz) :
    z ∈ periodicSpectrum hp φ ↔ (periodicResonantMatrix hp φ n z hz h).det = 0 := by
  have hφ : weightedBaseToPair SpectralWeight.one (unitBaseEquiv.symm φ) = φ := by
    rw [← unitBaseEquiv_eq, ContinuousLinearEquiv.apply_symm_apply]
  have he := unit_weighted_eigenvector_iff_periodicSpectrum hp (unitBaseEquiv.symm φ) z
  rw [hφ] at he
  exact he.symm.trans (weighted_eigenvector_iff_resonant_det_zero hp SpectralWeight.one (unitBaseEquiv.symm φ) n z hz h)

/-- The determinant criterion holds with one common cutoff on an open convex potential neighborhood. -/
theorem exists_uniform_periodicResonantReduction (hp : p ≠ ⊤) (φ : PairSpace p) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ U : Set (PairSpace p), IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, ∀ n : ℤ, N ≤ n.natAbs → ∀ z : ℂ, ∀ hz : z ∈ resonantStrip n,
        ∃ h : PeriodicReductionSmall hp ψ n z hz,
          z ∈ periodicSpectrum hp ψ ↔ (periodicResonantMatrix hp ψ n z hz h).det = 0 := by
  obtain ⟨N, hN, U, ho, hc, hφ, h0, _, hsmall⟩ :=
    exists_uniform_complementarySquare_half hp SpectralWeight.one (unitBaseEquiv.symm φ)
  let V : Set (PairSpace p) := unitBaseEquiv.symm ⁻¹' U
  refine ⟨N, hN, V, ho.preimage unitBaseEquiv.symm.continuous,
    hc.linear_preimage (unitBaseEquiv.symm.toContinuousLinearMap.restrictScalars ℝ).toLinearMap,
    hφ, ?_, ?_⟩
  · change unitBaseEquiv.symm 0 ∈ U
    simpa only [map_zero] using h0
  · intro ψ hψ n hn z hz
    have h : PeriodicReductionSmall hp ψ n z hz :=
      ((hsmall (unitBaseEquiv.symm ψ) hψ n hn z hz).1).trans_lt (by norm_num)
    exact ⟨h, mem_periodicSpectrum_iff_resonant_det_zero hp ψ n z hz h⟩

/-- The frequency-threshold formulation of Lemma 6.6 for every finite Banach exponent. -/
theorem exists_periodicResonantReduction (hp : p ≠ ⊤) (φ : PairSpace p) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℤ, N ≤ n.natAbs → ∀ z : ℂ, ∀ hz : z ∈ resonantStrip n,
      ∃ h : PeriodicReductionSmall hp φ n z hz,
        z ∈ periodicSpectrum hp φ ↔ (periodicResonantMatrix hp φ n z hz h).det = 0 := by
  obtain ⟨N, hN, U, _, _, hφ, _, h⟩ := exists_uniform_periodicResonantReduction hp φ
  exact ⟨N, hN, h φ hφ⟩

end NLS.ZakharovShabat
