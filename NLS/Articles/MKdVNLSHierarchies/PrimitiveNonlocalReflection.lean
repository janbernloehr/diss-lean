import NLS.ZakharovShabat.L2FullAbelianGradient
import NLS.ZakharovShabat.SourceReflectionCutDomain
import NLS.Articles.MKdVNLSHierarchies.NonlocalSign

/-! # Corrected Corollary 9(ii) for the actual full primitive

The primitive gradient is identified by all original Hilbert variations,
with a proved unique continuous periodic representative. One common open
complex neighborhood contains every real source. Both spectral parameters
lie off the actual moving cuts. The nonlocal integral multiplies J*phi,
and its sign on the residual's left side is positive.
-/
noncomputable section
open Set Complex MeasureTheory NLS.ZakharovShabat
namespace NLS.Articles.MKdVNLSHierarchies

/-- The corrected residual, written with the actual physical primitive gradient. -/
def primitiveNonlocalResidual (φ : CoeffPair 2) (z : ℂ) (x : ℝ) : ℂ × ℂ :=
  ((deriv (sourceFullAbelianPhysicalGradient φ z) x).1-
      2*I*z*(sourceFullAbelianPhysicalGradient φ z x).1+
      2*I*(∫ t in (0:ℝ)..x,
        (I*(l2WholeLinePotential (sourcePhysicalL2 φ) t).1)*(sourceFullAbelianPhysicalGradient φ z t).1+
        (-I*(l2WholeLinePotential (sourcePhysicalL2 φ) t).2)*(sourceFullAbelianPhysicalGradient φ z t).2)*
          (l2WholeLinePotential (sourcePhysicalL2 φ) x).2,
   (deriv (sourceFullAbelianPhysicalGradient φ z) x).2+
      2*I*z*(sourceFullAbelianPhysicalGradient φ z x).2-
      2*I*(∫ t in (0:ℝ)..x,
        (I*(l2WholeLinePotential (sourcePhysicalL2 φ) t).1)*(sourceFullAbelianPhysicalGradient φ z t).1+
        (-I*(l2WholeLinePotential (sourcePhysicalL2 φ) t).2)*(sourceFullAbelianPhysicalGradient φ z t).2)*
          (l2WholeLinePotential (sourcePhysicalL2 φ) x).1)

theorem primitiveNonlocalResidual_eq_normalized (φ : CoeffPair 2) (z : ℂ) (x : ℝ) :
    primitiveNonlocalResidual φ z x = l2NormalizedNonlocalResidual (sourcePhysicalL2 φ) z
      (sourceCanonicalRoot (by simp) (by norm_num) φ z) x := rfl

/-- The complete corrected part(ii), including the actual primitive-gradient
interface on one common source neighborhood and the entire cut complement. -/
theorem exists_corollary9_ii_corrected :
    ∃ W U : Set (CoeffPair 2), IsOpen U ∧ realTypeSourceLocus 2 ⊆ U ∧
      ∀ φ ∈ U, (sourceMidpointReflection φ = φ ∨ sourceMidpointReflection φ = -φ) →
      ∀ z ∈ sourceCanonicalRootDomain (by simp) (by norm_num) φ,
        -z ∈ sourceCanonicalRootDomain (by simp) (by norm_num) φ ∧
        (∀ j : ℤ, ∀ h : CoeffPair 2,
          (fderiv ℂ (fun χ => sourceFullAbelianPrimitive (by simp) (by norm_num) W j (z,χ)) φ) h =
            ∫ x in (0:ℝ)..1,
              (sourceFullAbelianPhysicalGradient φ z x).1*(sourcePhysicalL2 h).ofLp.1 x+
              (sourceFullAbelianPhysicalGradient φ z x).2*(sourcePhysicalL2 h).ofLp.2 x) ∧
        (∀ j : ℤ, ∀ h : CoeffPair 2,
          (fderiv ℂ (fun χ => sourceFullAbelianPrimitive (by simp) (by norm_num) W j (-z,χ)) φ) h =
            ∫ x in (0:ℝ)..1,
              (sourceFullAbelianPhysicalGradient φ (-z) x).1*(sourcePhysicalL2 h).ofLp.1 x+
              (sourceFullAbelianPhysicalGradient φ (-z) x).2*(sourcePhysicalL2 h).ofLp.2 x) ∧
        ∀ᵐ x : ℝ, primitiveNonlocalResidual φ z x = primitiveNonlocalResidual φ (-z) x := by
  obtain ⟨W,U,_,D⟩ := exists_sourceFullAbelianDifferentialData (p := 2) (by simp) (by norm_num)
  refine ⟨W,U,D.source_open,D.real_subset,?_⟩
  intro φ hφ hT z hz
  have hm := (source_midpoint_even_or_odd_neg_mem_rootDomain_iff φ hT z).mpr hz
  refine ⟨hm,fun j h => sourceFullAbelianPrimitive_fderiv_eq_physical_integral D j φ h hφ z hz,
    fun j h => sourceFullAbelianPrimitive_fderiv_eq_physical_integral D j φ h hφ (-z) hm,?_⟩
  simp_rw [primitiveNonlocalResidual_eq_normalized]
  exact corollary9_ii_corrected_normalized_discriminant_gradients φ hT z

end NLS.Articles.MKdVNLSHierarchies
