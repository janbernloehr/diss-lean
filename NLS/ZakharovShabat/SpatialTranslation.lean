import NLS.SequenceSpaces.SpatialTranslation
import NLS.ZakharovShabat.PeriodicSpectrum

/-! # Translation conjugacy of the periodic operator

Translate both potential components and both domain components by the same
spatial displacement. The original domain-to-base pencil is intertwined
exactly, at every finite Banach exponent.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Spatial translation of a period-two coefficient pair, in its actual base norm. -/
def pairSpatialTranslation (t : ℝ) : PairSpace p ≃ₗᵢ[ℂ] PairSpace p where
  __ := (Coeff.spatialTranslation Real.pi t).toLinearEquiv.prodCongr
    (Coeff.spatialTranslation Real.pi t).toLinearEquiv
  norm_map' a := by simp [Prod.norm_def]

@[simp] theorem pairSpatialTranslation_apply (t : ℝ) (a : PairSpace p) :
    pairSpatialTranslation t a =
      (Coeff.spatialTranslation Real.pi t a.1, Coeff.spatialTranslation Real.pi t a.2) := rfl

/-- Spatial translation preserves the full one-derivative domain. -/
def domainSpatialTranslation (t : ℝ) : Domain p ≃ₗᵢ[ℂ] Domain p where
  __ := (WeightedCoeff.spatialTranslation (Weight.sobolev 1) Real.pi t).toLinearEquiv.prodCongr
    (WeightedCoeff.spatialTranslation (Weight.sobolev 1) Real.pi t).toLinearEquiv
  norm_map' f := by simp [Prod.norm_def]

@[simp] theorem domainSpatialTranslation_apply (t : ℝ) (f : Domain p) :
    domainSpatialTranslation t f =
      (WeightedCoeff.spatialTranslation (Weight.sobolev 1) Real.pi t f.1,
       WeightedCoeff.spatialTranslation (Weight.sobolev 1) Real.pi t f.2) := rfl

/-- Domain inclusion commutes with spatial translation. -/
theorem domainInclusion_spatialTranslation (t : ℝ) (f : Domain p) :
    domainInclusion (domainSpatialTranslation t f) =
      pairSpatialTranslation t (domainInclusion f) := by
  apply Prod.ext <;> ext n <;> simp

/-- Exact translation covariance of the convolution defining the potential. -/
theorem potentialMul_spatialTranslation (hp : p ≠ ⊤) (t : ℝ)
    (a : Coeff p) (f : ScalarDomain p) :
    potentialMul hp (Coeff.spatialTranslation Real.pi t a)
      (WeightedCoeff.spatialTranslation (Weight.sobolev 1) Real.pi t f) =
        Coeff.spatialTranslation Real.pi t (potentialMul hp a f) := by
  ext n
  simp only [potentialMul_apply, Coeff.spatialTranslation_apply,
    WeightedCoeff.spatialTranslation_apply]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro k
  have he := spatialTranslation_phase_add Real.pi t (n-k) k
  rw [sub_add_cancel] at he
  rw [he]
  ring

/-- The translated potential intertwines the original differential operators. -/
theorem operator_spatialTranslation (hp : p ≠ ⊤) (t : ℝ)
    (φ : PairSpace p) (f : Domain p) :
    operator hp (pairSpatialTranslation t φ) (domainSpatialTranslation t f) =
      pairSpatialTranslation t (operator hp φ f) := by
  apply Prod.ext <;> ext n
  · simp only [operator_fst_apply, pairSpatialTranslation_apply, domainSpatialTranslation_apply,
      Coeff.spatialTranslation_apply, WeightedCoeff.spatialTranslation_apply]
    rw [mul_add, ← tsum_mul_left]
    congr 1
    · ring
    · apply tsum_congr
      intro k
      have he := spatialTranslation_phase_add Real.pi t (n-k) k
      rw [sub_add_cancel] at he
      rw [he]
      ring
  · simp only [operator_snd_apply, pairSpatialTranslation_apply, domainSpatialTranslation_apply,
      Coeff.spatialTranslation_apply, WeightedCoeff.spatialTranslation_apply]
    rw [mul_add, ← tsum_mul_left]
    congr 1
    · ring
    · apply tsum_congr
      intro k
      have he := spatialTranslation_phase_add Real.pi t (n-k) k
      rw [sub_add_cancel] at he
      rw [he]
      ring

/-- Translation conjugates the actual pencil `z-L`, with its derivative domain. -/
theorem spectralPencil_spatialTranslation (hp : p ≠ ⊤) (t : ℝ)
    (φ : PairSpace p) (z : ℂ) (f : Domain p) :
    spectralPencil hp (pairSpatialTranslation t φ) z (domainSpatialTranslation t f) =
      pairSpatialTranslation t (spectralPencil hp φ z f) := by
  simp only [spectralPencil_apply, domainInclusion_spatialTranslation,
    operator_spatialTranslation, map_sub, map_smul]

end NLS.ZakharovShabat
