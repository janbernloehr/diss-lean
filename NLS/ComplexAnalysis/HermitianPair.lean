import Mathlib.Analysis.Normed.Lp.ProdLp
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Tactic.Linarith

/-! # Hermitian norms for two complex coordinates

Use the Euclidean norm directly, rather than transporting norm estimates
through the supremum-norm equivalence on pairs. Coordinate transport is
used only for algebra, continuity, and integration.
-/
noncomputable section
open Complex
namespace NLS.ComplexAnalysis

abbrev HermitianPair := WithLp 2 (ℂ × ℂ)

/-- Coordinate equivalence; this is deliberately not asserted to be an isometry. -/
def hermitianPairEquiv : HermitianPair ≃L[ℂ] ℂ × ℂ :=
  WithLp.prodContinuousLinearEquiv 2 ℂ ℂ ℂ

/-- Regard a coordinate pair as a vector with its Hermitian norm. -/
def hermitianPair (v : ℂ × ℂ) : HermitianPair := hermitianPairEquiv.symm v

@[simp] theorem hermitianPair_norm_sq (v : ℂ × ℂ) :
    ‖hermitianPair v‖^2 = ‖v.1‖^2+‖v.2‖^2 :=
  WithLp.prod_norm_sq_eq_of_L2 _

@[simp] theorem hermitianPair_norm (v : ℂ × ℂ) :
    ‖hermitianPair v‖ = Real.sqrt (‖v.1‖^2+‖v.2‖^2) :=
  WithLp.prod_norm_eq_of_L2 _

/-- Swapping the coordinates preserves the Hermitian norm. -/
theorem hermitianPair_norm_swap (v : ℂ × ℂ) :
    ‖hermitianPair (v.2,v.1)‖ = ‖hermitianPair v‖ := by
  simp only [hermitianPair_norm,add_comm]

/-- A diagonal multiplier is bounded by the maximum of its two scalar norms,
with no dimension-dependent factor. -/
theorem hermitianPair_norm_diagonal_le (a b : ℂ) (v : ℂ × ℂ) (M : ℝ)
    (hM : 0 ≤ M) (ha : ‖a‖ ≤ M) (hb : ‖b‖ ≤ M) :
    ‖hermitianPair (a*v.1,b*v.2)‖ ≤ M*‖hermitianPair v‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hM (norm_nonneg _))).mp
  rw [hermitianPair_norm_sq,mul_pow,hermitianPair_norm_sq]
  simp only [norm_mul,mul_pow]
  have h₁ := mul_le_mul_of_nonneg_right ((sq_le_sq₀ (norm_nonneg a) hM).mpr ha) (sq_nonneg ‖v.1‖)
  have h₂ := mul_le_mul_of_nonneg_right ((sq_le_sq₀ (norm_nonneg b) hM).mpr hb) (sq_nonneg ‖v.2‖)
  nlinarith

/-- A matrix presented by its two columns, acting on Hermitian vectors. -/
def hermitianColumns (u v : ℂ × ℂ) : HermitianPair →L[ℂ] HermitianPair :=
  hermitianPairEquiv.symm.toContinuousLinearMap.comp
    (((ContinuousLinearMap.fst ℂ ℂ ℂ).smulRight u +
      (ContinuousLinearMap.snd ℂ ℂ ℂ).smulRight v).comp hermitianPairEquiv.toContinuousLinearMap)

@[simp] theorem hermitianColumns_apply (u v w : ℂ × ℂ) :
    hermitianColumns u v (hermitianPair w) = hermitianPair (w.1 • u+w.2 • v) := by
  simp [hermitianColumns,hermitianPair]

/-- Continuity is transported algebraically, without comparing the two norms. -/
theorem continuous_hermitianColumns :
    Continuous (fun uv : (ℂ × ℂ) × (ℂ × ℂ) => hermitianColumns uv.1 uv.2) := by
  unfold hermitianColumns
  apply Continuous.clm_comp continuous_const
  apply Continuous.clm_comp _ continuous_const
  exact ((ContinuousLinearMap.smulRightL ℂ (ℂ × ℂ) (ℂ × ℂ)
    (ContinuousLinearMap.fst ℂ ℂ ℂ)).continuous.comp continuous_fst).add
    ((ContinuousLinearMap.smulRightL ℂ (ℂ × ℂ) (ℂ × ℂ)
      (ContinuousLinearMap.snd ℂ ℂ ℂ)).continuous.comp continuous_snd)

/-- The exact operator norm of an off-diagonal matrix in the Hermitian norm. -/
theorem norm_hermitianColumns_offDiagonal (a b : ℂ) :
    ‖hermitianColumns (0,b) (a,0)‖ = max ‖a‖ ‖b‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (le_max_of_le_left (norm_nonneg _))
    intro w
    obtain ⟨v,rfl⟩ := hermitianPairEquiv.symm.surjective w
    change ‖hermitianColumns (0,b) (a,0) (hermitianPair v)‖ ≤ max ‖a‖ ‖b‖*‖hermitianPair v‖
    rw [hermitianColumns_apply]
    have h := hermitianPair_norm_diagonal_le a b (v.2,v.1) (max ‖a‖ ‖b‖)
      (le_max_of_le_left (norm_nonneg _)) (le_max_left _ _) (le_max_right _ _)
    rw [hermitianPair_norm_swap] at h
    simpa [smul_eq_mul,mul_comm] using h
  · apply max_le
    · have h := (hermitianColumns (0,b) (a,0)).le_opNorm (hermitianPair (0,1))
      simpa [hermitianColumns_apply,hermitianPair_norm,smul_eq_mul] using h
    · have h := (hermitianColumns (0,b) (a,0)).le_opNorm (hermitianPair (1,0))
      simpa [hermitianColumns_apply,hermitianPair_norm,smul_eq_mul] using h

end NLS.ComplexAnalysis
