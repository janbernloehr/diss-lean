import NLS.ZakharovShabat.FloquetModeProjections
import NLS.ZakharovShabat.L2WholeLineFloquetBound
import Mathlib.Analysis.SpecificLimits.Normed

/-! # Exact Floquet mode propagation and directional decay -/
noncomputable section
set_option autoImplicit false
open Set Filter Complex Matrix Module
open scoped Topology
namespace NLS.ZakharovShabat

/-- Every projected mode retains its exact multiplier at all signed
integer translations of the original real-time physical propagation. -/
theorem l2WholeLineFundamentalMatrix_mode_add_int
    (u : IntervalPairL2) (z : ℂ) (b : Basis (Fin 2) ℂ (Fin 2 → ℂ))
    (μ : Fin 2 → ℂ) (hM : ∀ i, l2Monodromy u z *ᵥ b i = μ i • b i)
    (i : Fin 2) (hμ : μ i ≠ 0) (v : Fin 2 → ℂ) (t : ℝ) (n : ℤ) :
    l2WholeLineFundamentalMatrix u z (t+n) *ᵥ floquetModeProjection b i v =
      μ i ^ n • (l2WholeLineFundamentalMatrix u z t *ᵥ floquetModeProjection b i v) := by
  rw [l2WholeLineFundamentalMatrix_add_int,← Matrix.mulVec_mulVec,
    unit_matrix_zpow_mulVec_of_eigenvector (l2MonodromyUnit u z) (μ i) hμ
      (floquetModeProjection b i v) (mulVec_floquetModeProjection _ b μ hM i v) n,
    Matrix.mulVec_smul]

/-- Stable physical modes decay along every forward period sequence. -/
theorem tendsto_l2WholeLine_stable_mode (u : IntervalPairL2) (z : ℂ)
    (b : Basis (Fin 2) ℂ (Fin 2 → ℂ)) (μ : Fin 2 → ℂ)
    (hM : ∀ i, l2Monodromy u z *ᵥ b i = μ i • b i)
    (i : Fin 2) (hμ0 : μ i ≠ 0) (hμ : ‖μ i‖ < 1) (v : Fin 2 → ℂ) (t : ℝ) :
    Tendsto (fun n : ℕ => l2WholeLineFundamentalMatrix u z (t+n) *ᵥ
      floquetModeProjection b i v) atTop (𝓝 0) := by
  have h := (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hμ).smul
    (tendsto_const_nhds (x := l2WholeLineFundamentalMatrix u z t *ᵥ floquetModeProjection b i v))
  simpa only [zero_smul] using! h.congr' (Filter.Eventually.of_forall (fun n => by
    simpa only [Int.cast_natCast,zpow_natCast] using
      (l2WholeLineFundamentalMatrix_mode_add_int u z b μ hM i hμ0 v t (n : ℤ)).symm))

/-- Unstable physical modes decay along every backward period sequence. -/
theorem tendsto_l2WholeLine_unstable_mode_backward (u : IntervalPairL2) (z : ℂ)
    (b : Basis (Fin 2) ℂ (Fin 2 → ℂ)) (μ : Fin 2 → ℂ)
    (hM : ∀ i, l2Monodromy u z *ᵥ b i = μ i • b i)
    (i : Fin 2) (hμ : 1 < ‖μ i‖) (v : Fin 2 → ℂ) (t : ℝ) :
    Tendsto (fun n : ℕ => l2WholeLineFundamentalMatrix u z (t-n) *ᵥ
      floquetModeProjection b i v) atTop (𝓝 0) := by
  have hμ0 : μ i ≠ 0 := norm_pos_iff.mp (zero_lt_one.trans hμ)
  have hi : ‖(μ i)⁻¹‖ < 1 := by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hμ
  have h := (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hi).smul
    (tendsto_const_nhds (x := l2WholeLineFundamentalMatrix u z t *ᵥ floquetModeProjection b i v))
  simpa only [zero_smul] using! h.congr' (Filter.Eventually.of_forall (fun n => by
    simpa only [Int.cast_neg,Int.cast_natCast,_root_.zpow_neg,zpow_natCast,inv_pow,sub_eq_add_neg] using
      (l2WholeLineFundamentalMatrix_mode_add_int u z b μ hM i hμ0 v t (-(n : ℤ))).symm))

end NLS.ZakharovShabat
