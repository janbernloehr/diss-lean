import NLS.ZakharovShabat.FloquetModeProjections
import Mathlib.Analysis.Matrix.Normed

/-! # Floquet mode projections without a choice of normalized eigenvectors -/
noncomputable section
set_option autoImplicit false
open Matrix Module
open scoped Matrix.Norms.Elementwise
namespace NLS.ZakharovShabat

/-- The algebraic projection for the root mu when the other root is nu. -/
def floquetRootProjection (M : Matrix (Fin 2) (Fin 2) ℂ) (μ ν : ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ := (μ-ν)⁻¹ • (M-ν • 1)

/-- The explicit root projection is the actual mode projection for an eigenbasis. -/
theorem floquetRootProjection_mulVecLin (M : Matrix (Fin 2) (Fin 2) ℂ)
    (μ ν : ℂ) (hne : μ ≠ ν) (b : Basis (Fin 2) ℂ (Fin 2 → ℂ))
    (hμ : M *ᵥ b 0 = μ • b 0) (hν : M *ᵥ b 1 = ν • b 1) :
    (floquetRootProjection M μ ν).mulVecLin = floquetModeProjection b 0 := by
  apply b.ext
  intro j
  fin_cases j
  · change (floquetRootProjection M μ ν) *ᵥ b 0 = _
    simp only [floquetRootProjection,Matrix.smul_mulVec,Matrix.sub_mulVec,
      Matrix.one_mulVec,hμ,← sub_smul,smul_smul,inv_mul_cancel₀ (sub_ne_zero.mpr hne),one_smul]
    simp [floquetModeProjection_apply]
  · change (floquetRootProjection M μ ν) *ᵥ b 1 = _
    simp [floquetRootProjection,Matrix.smul_mulVec,Matrix.sub_mulVec,Matrix.one_mulVec,
      hν,floquetModeProjection_apply]

/-- The separation of reciprocal roots is exactly controlled by the discriminant. -/
theorem floquet_root_separation_sq (d μ ν : ℂ) (hsum : d = μ+ν) (hprod : μ*ν = 1) :
    (μ-ν)^2 = d^2-4 := by
  rw [hsum]
  linear_combination -4*hprod

theorem norm_floquet_root_separation_sq (d μ ν : ℂ) (hsum : d = μ+ν) (hprod : μ*ν = 1) :
    ‖μ-ν‖^2 = ‖d^2-4‖ := by
  rw [← norm_pow,floquet_root_separation_sq d μ ν hsum hprod]

/-- Each root of the original unimodular quadratic is controlled by the trace. -/
theorem norm_floquet_root_le (d μ : ℂ) (h : μ^2-d*μ+1 = 0) : ‖μ‖ ≤ ‖d‖+1 := by
  have he : μ^2 = d*μ-1 := by linear_combination h
  have hb : ‖μ‖^2 ≤ ‖d‖*‖μ‖+1 := by
    calc
      ‖μ‖^2 = ‖μ^2‖ := (norm_pow _ _).symm
      _ = ‖d*μ-1‖ := by rw [he]
      _ ≤ ‖d*μ‖+‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = ‖d‖*‖μ‖+1 := by rw [norm_mul,norm_one]
  by_contra hn
  have hh : ‖d‖+1 < ‖μ‖ := lt_of_not_ge hn
  nlinarith [norm_nonneg d]

/-- A quantitative bound on the actual algebraic projection, independent of
normalization of eigenvectors. -/
theorem norm_floquetRootProjection_le (M : Matrix (Fin 2) (Fin 2) ℂ) (μ ν : ℂ) :
    ‖floquetRootProjection M μ ν‖ ≤ (‖M‖+‖ν‖*‖(1 : Matrix (Fin 2) (Fin 2) ℂ)‖)/‖μ-ν‖ := by
  rw [floquetRootProjection,norm_smul,norm_inv,div_eq_mul_inv,mul_comm]
  apply mul_le_mul_of_nonneg_right ?_ (inv_nonneg.mpr (norm_nonneg _))
  simpa only [norm_smul] using norm_sub_le M (ν • (1 : Matrix (Fin 2) (Fin 2) ℂ))

/-- Uniform coefficient and root-separation estimates give a uniform projection bound. -/
theorem norm_floquetRootProjection_le_of_bounds (M : Matrix (Fin 2) (Fin 2) ℂ)
    (μ ν : ℂ) (B K δ : ℝ) (hδ : 0 < δ) (hM : ‖M‖ ≤ B) (hν : ‖ν‖ ≤ K)
    (hsep : δ ≤ ‖μ-ν‖) : ‖floquetRootProjection M μ ν‖ ≤ (B+K)/δ := by
  calc
    ‖floquetRootProjection M μ ν‖ ≤ (‖M‖+‖ν‖)/‖μ-ν‖ := by
      simpa using norm_floquetRootProjection_le M μ ν
    _ ≤ (‖M‖+‖ν‖)/δ :=
      div_le_div_of_nonneg_left (add_nonneg (norm_nonneg _) (norm_nonneg _)) hδ hsep
    _ ≤ (B+K)/δ := div_le_div_of_nonneg_right (add_le_add hM hν) hδ.le

/-- A discriminant lower bound controls both actual mode projections without
choosing continuous roots or a normalized eigenbasis. -/
theorem norm_floquetRootProjection_le_of_discriminant_bound
    (M : Matrix (Fin 2) (Fin 2) ℂ) (d μ ν : ℂ) (B δ : ℝ) (hδ : 0 < δ)
    (hM : ‖M‖ ≤ B) (hsum : d = μ+ν) (hprod : μ*ν = 1)
    (hdisc : δ^2 ≤ ‖d^2-4‖) :
    ‖floquetRootProjection M μ ν‖ ≤ (B+‖d‖+1)/δ := by
  have hq : ν^2-d*ν+1 = 0 := by linear_combination -ν*hsum-hprod
  have hsep : δ ≤ ‖μ-ν‖ := by
    rw [← norm_floquet_root_separation_sq d μ ν hsum hprod] at hdisc
    nlinarith [norm_nonneg (μ-ν)]
  simpa only [add_assoc] using norm_floquetRootProjection_le_of_bounds
    M μ ν B (‖d‖+1) δ hδ hM (norm_floquet_root_le d ν hq) hsep

end NLS.ZakharovShabat
