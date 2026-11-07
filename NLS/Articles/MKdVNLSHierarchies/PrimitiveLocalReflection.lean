import NLS.Articles.MKdVNLSHierarchies.PrimitiveNonlocalReflection
import NLS.Articles.MKdVNLSHierarchies.PointwiseSpectralSymmetries
import NLS.ZakharovShabat.SourceSwapScalingConstraint
import NLS.ZakharovShabat.L2NormalizedLocalResidual

/-! # Both corrected Corollary 9 clauses on one common primitive domain -/
noncomputable section
open Set Complex MeasureTheory NLS.ZakharovShabat
namespace NLS.Articles.MKdVNLSHierarchies

def primitiveLocalResidual (φ : CoeffPair 2) (z : ℂ) (x : ℝ) : ℂ × ℂ :=
  ((deriv (sourceFullAbelianPhysicalGradient φ z) x).1-2*I*z*(sourceFullAbelianPhysicalGradient φ z x).1,
   (deriv (sourceFullAbelianPhysicalGradient φ z) x).2+2*I*z*(sourceFullAbelianPhysicalGradient φ z x).2)

theorem primitiveLocalResidual_eq_normalized (φ : CoeffPair 2) (z : ℂ) (x : ℝ) :
    primitiveLocalResidual φ z x = l2NormalizedLocalResidual (sourcePhysicalL2 φ) z
      (sourceCanonicalRoot (by simp) (by norm_num) φ z) x := rfl

theorem corollary9_i_normalized_actual_gradients (φ : CoeffPair 2) (α : ℝ)
    (hP : sourceComponentSwap φ = sourcePhaseRotation α φ) (z : ℂ) :
    ∀ᵐ x : ℝ, primitiveLocalResidual φ z x = primitiveLocalResidual φ (-z) x := by
  simp_rw [primitiveLocalResidual_eq_normalized]
  filter_upwards [ae_l2NormalizedLocalResidual_eq_xi (sourcePhysicalL2 φ) z
      (sourceCanonicalRoot (by simp) (by norm_num) φ z),
    ae_l2NormalizedLocalResidual_eq_xi (sourcePhysicalL2 φ) (-z)
      (sourceCanonicalRoot (by simp) (by norm_num) φ (-z))] with x hp hm
  rw [hp,hm,source_swap_scaling_normalized_xi_even _ (exp_ne_zero _) φ hP z x]

/-- Both clauses use the same constructed full primitive and source neighborhood.
Its actual gradient is identified in every original Hilbert direction. The
spectral parameter lies in the full moving cut complement. -/
theorem exists_corollary9_complete_corrected :
    ∃ W U : Set (CoeffPair 2), IsOpen U ∧ realTypeSourceLocus 2 ⊆ U ∧
      (∀ φ ∈ U, ∀ z ∈ sourceCanonicalRootDomain (by simp) (by norm_num) φ,
        ∀ j : ℤ, ∀ h : CoeffPair 2,
          (fderiv ℂ (fun χ => sourceFullAbelianPrimitive (by simp) (by norm_num) W j (z,χ)) φ) h =
            ∫ x in (0:ℝ)..1,
              (sourceFullAbelianPhysicalGradient φ z x).1*(sourcePhysicalL2 h).ofLp.1 x+
              (sourceFullAbelianPhysicalGradient φ z x).2*(sourcePhysicalL2 h).ofLp.2 x) ∧
      (∀ φ ∈ U, ∀ α : ℝ, sourceComponentSwap φ = sourcePhaseRotation α φ →
        ∀ z ∈ sourceCanonicalRootDomain (by simp) (by norm_num) φ,
          -z ∈ sourceCanonicalRootDomain (by simp) (by norm_num) φ ∧
          ∀ᵐ x : ℝ, primitiveLocalResidual φ z x = primitiveLocalResidual φ (-z) x) ∧
      (∀ φ ∈ U, (sourceMidpointReflection φ = φ ∨ sourceMidpointReflection φ = -φ) →
        ∀ z ∈ sourceCanonicalRootDomain (by simp) (by norm_num) φ,
          -z ∈ sourceCanonicalRootDomain (by simp) (by norm_num) φ ∧
          ∀ᵐ x : ℝ, primitiveNonlocalResidual φ z x = primitiveNonlocalResidual φ (-z) x) := by
  obtain ⟨W,U,_,D⟩ := exists_sourceFullAbelianDifferentialData (p := 2) (by simp) (by norm_num)
  refine ⟨W,U,D.source_open,D.real_subset,?_,?_,?_⟩
  · intro φ hφ z hz j h
    exact sourceFullAbelianPrimitive_fderiv_eq_physical_integral D j φ h hφ z hz
  · intro φ _ α hP z hz
    exact ⟨(sourcePeriodicReflection_of_swap_scaling _ (exp_ne_zero _) φ hP).neg_mem_rootDomain_iff z |>.mpr hz,
      corollary9_i_normalized_actual_gradients φ α hP z⟩
  · intro φ _ hT z hz
    refine ⟨(source_midpoint_even_or_odd_neg_mem_rootDomain_iff φ hT z).mpr hz,?_⟩
    simp_rw [primitiveNonlocalResidual_eq_normalized]
    exact corollary9_ii_corrected_normalized_discriminant_gradients φ hT z

end NLS.Articles.MKdVNLSHierarchies
