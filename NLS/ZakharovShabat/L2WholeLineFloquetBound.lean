import NLS.ZakharovShabat.L2WholeLineFundamental
import NLS.ZakharovShabat.L2FloquetBandCriterion

/-! # Bounded monodromy propagation on the full real line

A unit-modulus monodromy eigenvector gives a uniformly bounded nonzero
continuous propagated curve for the all-real-time fundamental matrix.
This is not yet the whole-line operator's spectral characterization.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Matrix
open scoped Matrix.Norms.Elementwise
namespace NLS.ZakharovShabat

/-- An invertible matrix propagates its eigenvector by the scalar
eigenvalue to every integer power, including negative powers. -/
theorem unit_matrix_zpow_mulVec_of_eigenvector
    (U : (Matrix (Fin 2) (Fin 2) ℂ)ˣ) (μ : ℂ) (hμ : μ ≠ 0)
    (v : Fin 2 → ℂ) (hv : (U : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v = μ • v) (n : ℤ) :
    (↑(U^n) : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v = μ^n • v := by
  have hi : (↑U⁻¹ : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v = μ⁻¹ • v := by
    have he := congrArg (fun w => (↑U⁻¹ : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ w) hv
    rw [Matrix.mulVec_mulVec,Units.inv_mul,Matrix.one_mulVec,Matrix.mulVec_smul] at he
    calc
      (↑U⁻¹ : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v = μ⁻¹ • (μ • ((↑U⁻¹ : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v)) := by
        rw [smul_smul,inv_mul_cancel₀ hμ,one_smul]
      _ = μ⁻¹ • v := by rw [← he]
  induction n using Int.induction_on with
  | zero => simp
  | succ n hn =>
    rw [_root_.zpow_add_one,Units.val_mul,← Matrix.mulVec_mulVec,hv,
      Matrix.mulVec_smul,hn,smul_smul,zpow_add₀ hμ,zpow_one]
    rw [mul_comm]
  | pred n hn =>
    rw [_root_.zpow_sub_one,Units.val_mul,← Matrix.mulVec_mulVec,hi,
      Matrix.mulVec_smul,hn,smul_smul,zpow_sub₀ hμ,zpow_one]
    rw [div_eq_mul_inv,mul_comm]

/-- The propagated vector has its exact scalar Floquet form in every period. -/
theorem l2WholeLineFundamentalMatrix_mulVec_of_eigenvector
    (u : IntervalPairL2) (z μ : ℂ) (hμ : μ ≠ 0) (v : Fin 2 → ℂ)
    (hv : l2Monodromy u z *ᵥ v = μ • v) (t : ℝ) :
    l2WholeLineFundamentalMatrix u z t *ᵥ v =
      μ^⌊t⌋ • (l2FundamentalMatrix u z (l2WholeLinePeriodTime t) *ᵥ v) := by
  rw [l2WholeLineFundamentalMatrix,← Matrix.mulVec_mulVec,
    unit_matrix_zpow_mulVec_of_eigenvector (l2MonodromyUnit u z) μ hμ v hv,
    Matrix.mulVec_smul]

/-- Evaluation of a continuous matrix curve on a fixed initial vector is continuous. -/
theorem continuous_matrixCurve_mulVec {X : Type*} [TopologicalSpace X]
    (M : X → Matrix (Fin 2) (Fin 2) ℂ) (hM : Continuous M) (v : Fin 2 → ℂ) :
    Continuous (fun x => M x *ᵥ v) := by
  apply continuous_pi
  intro i
  simp only [Matrix.mulVec,dotProduct]
  apply continuous_finsetSum
  intro j _
  exact ((continuous_apply j).comp ((continuous_apply i).comp hM)).mul continuous_const

/-- A unit multiplier keeps the actual all-real-time propagated vector
uniformly bounded, with no restriction to nonnegative time. -/
theorem bounded_l2WholeLineFundamentalMatrix_mulVec
    (u : IntervalPairL2) (z μ : ℂ) (hμ : ‖μ‖ = 1) (v : Fin 2 → ℂ)
    (hv : l2Monodromy u z *ᵥ v = μ • v) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, ‖l2WholeLineFundamentalMatrix u z t *ᵥ v‖ ≤ C := by
  have hμ0 : μ ≠ 0 := by intro he; simp [he] at hμ
  have hpair : Continuous (fun t : Icc (0 : ℝ) 1 => ((z,u),t)) :=
    continuous_const.prodMk continuous_id
  have hM := continuous_l2FundamentalMatrix_time_joint.comp hpair
  have hK : IsCompact (Set.univ : Set (Icc (0 : ℝ) 1)) := isCompact_univ
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn
    (continuous_matrixCurve_mulVec _ hM v).continuousOn
  refine ⟨max C 0,le_max_right _ _,fun t => ?_⟩
  rw [l2WholeLineFundamentalMatrix_mulVec_of_eigenvector u z μ hμ0 v hv t,
    norm_smul,norm_zpow,hμ,_root_.one_zpow,one_mul]
  exact (hC (l2WholeLinePeriodTime t) (mem_univ _)).trans (le_max_left _ _)

/-- At every point of the closed canonical band set, the actual physical
continuation carries a nonzero initial vector to a bounded continuous curve. -/
theorem source_band_exists_bounded_wholeLine_propagation
    (φ : CoeffPair 2) (hφ : IsRealType (CoeffPair.toMax 2 φ)) (x : ℝ)
    (hx : x ∈ sourceFloquetBandSet (by simp) (by norm_num) φ) :
    ∃ v : Fin 2 → ℂ, v ≠ 0 ∧
      Continuous (fun t => l2WholeLineFundamentalMatrix (sourcePhysicalL2 φ) x t *ᵥ v) ∧
      (l2WholeLineFundamentalMatrix (sourcePhysicalL2 φ) x 0 *ᵥ v = v) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
        ‖l2WholeLineFundamentalMatrix (sourcePhysicalL2 φ) x t *ᵥ v‖ ≤ C := by
  obtain ⟨μ,hμ,v,hv,hMv⟩ := (source_l2_unit_monodromy_eigenvector_iff_mem_band φ hφ x).mpr hx
  exact ⟨v,hv,continuous_matrixCurve_mulVec _ (continuous_l2WholeLineFundamentalMatrix _ _) v,
    by simp,bounded_l2WholeLineFundamentalMatrix_mulVec _ _ μ hμ v hMv⟩

end NLS.ZakharovShabat
