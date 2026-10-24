import NLS.ZakharovShabat.FloquetQuadratic
import NLS.ZakharovShabat.SourceFloquetBandSet
import NLS.ZakharovShabat.L2Discriminant

/-! # Physical L2 monodromy and the closed Floquet band criterion

The actual monodromy of each original real Hilbert source has a unit
multiplier with a nonzero eigenvector precisely outside its open gaps.
This supplies the finite-dimensional Floquet criterion, not yet a
whole-line spectral theorem.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Matrix
namespace NLS.ZakharovShabat

/-- The characteristic determinant criterion for the actual physical
monodromy, with all gap endpoints included. -/
theorem source_l2_unit_characteristic_root_iff_mem_band
    (φ : CoeffPair 2) (hφ : IsRealType (CoeffPair.toMax 2 φ)) (x : ℝ) :
    (∃ μ : ℂ, ‖μ‖ = 1 ∧ (l2Monodromy (sourcePhysicalL2 φ) x-μ • 1).det = 0) ↔
      x ∈ sourceFloquetBandSet (by simp) (by norm_num) φ := by
  have htrace : (l2Monodromy (sourcePhysicalL2 φ) x).trace =
      canonicalDiscriminant (by simp) (periodOnePotential φ) x :=
    (canonicalDiscriminant_eq_l2_source φ x).symm
  have hr : (l2Monodromy (sourcePhysicalL2 φ) x).trace.im = 0 := by
    rw [htrace]
    exact canonicalDiscriminant_im_eq_zero_of_realType (p := 2)
      (by simp) (by norm_num) (periodOnePotential φ) (periodOnePotential_mem φ)
      (isRealType_periodOnePotential φ hφ) x
  rw [exists_unit_characteristic_root_iff _ (det_l2Monodromy _ _) hr,htrace]
  exact (mem_sourceFloquetBandSet_iff_abs_discriminant_le_two
    (by simp) (by norm_num) φ hφ x).symm

/-- A nonzero physical monodromy eigenvector with unit multiplier exists
exactly on the full closed band set of the original source. -/
theorem source_l2_unit_monodromy_eigenvector_iff_mem_band
    (φ : CoeffPair 2) (hφ : IsRealType (CoeffPair.toMax 2 φ)) (x : ℝ) :
    (∃ μ : ℂ, ‖μ‖ = 1 ∧ ∃ v : Fin 2 → ℂ, v ≠ 0 ∧
      l2Monodromy (sourcePhysicalL2 φ) x *ᵥ v = μ • v) ↔
      x ∈ sourceFloquetBandSet (by simp) (by norm_num) φ := by
  rw [← source_l2_unit_characteristic_root_iff_mem_band φ hφ x]
  simp_rw [← Matrix.exists_mulVec_eq_zero_iff,Matrix.sub_mulVec,
    Matrix.smul_mulVec,Matrix.one_mulVec,sub_eq_zero]

/-- Floquet eigenvectors evolve by the exact powers of their multiplier
at every nonnegative integer time in the constructed physical solution. -/
theorem l2PeriodicFundamentalMatrix_nat_mulVec_of_eigenvector
    (u : IntervalPairL2) (z μ : ℂ) (v : Fin 2 → ℂ)
    (hv : l2Monodromy u z *ᵥ v = μ • v) (n : ℕ) :
    l2PeriodicFundamentalMatrix u z ⟨(n : ℝ),by change 0 ≤ (n : ℝ); positivity⟩ *ᵥ v = μ^n • v := by
  rw [l2PeriodicFundamentalMatrix_nat]
  induction n with
  | zero => simp
  | succ n hn =>
    rw [pow_succ',← Matrix.mulVec_mulVec,hn,Matrix.mulVec_smul,hv,smul_smul]
    rw [pow_succ]

end NLS.ZakharovShabat
