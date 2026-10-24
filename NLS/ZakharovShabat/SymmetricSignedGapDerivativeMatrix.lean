import NLS.ZakharovShabat.SymmetricDirichletDualDirections
import NLS.ZakharovShabat.SourceSymmetricSignedGaps

/-! # The actual signed-gap derivative in Dirichlet coordinates

The proved Dirichlet derivative inverse supplies a bounded change of
coordinates. Its columns are the actual dual directions, so the entries
of the signed-gap derivative have the cross-boundary characteristic
formula. At a collapsed gap the diagonal entry is exactly two.
-/
noncomputable section
open Set Complex
namespace NLS.ZakharovShabat

def symmetricDirichletDerivativeEquiv (φ : CoeffPair 2)
    (hφ : IsRealType (CoeffPair.toMax 2 φ)) (href : sourceSpatialReflection φ = φ) :
    Coeff 2 ≃L[ℂ] Coeff 2 :=
  ContinuousLinearEquiv.ofBijective (symmetricDirichletDerivative φ)
    (LinearMap.ker_eq_bot.mpr (bijective_symmetricDirichletDerivative φ hφ href).1)
    (LinearMap.range_eq_top.mpr (bijective_symmetricDirichletDerivative φ hφ href).2)

theorem symmetricDirichletDerivativeEquiv_symm_single (φ : CoeffPair 2)
    (hφ : IsRealType (CoeffPair.toMax 2 φ)) (href : sourceSpatialReflection φ = φ) (m : ℤ) :
    (symmetricDirichletDerivativeEquiv φ hφ href).symm (lp.single 2 m 1) =
      symmetricDirichletDualCoordinate φ m := by
  apply (symmetricDirichletDerivativeEquiv φ hφ href).injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact (symmetricDirichletDerivative_dualCoordinate φ hφ href m).symm

/-- The bounded signed-gap derivative after the invertible Dirichlet change of coordinates. -/
def symmetricSignedGapDerivativeMatrix (φ : CoeffPair 2)
    (hφ : IsRealType (CoeffPair.toMax 2 φ)) (href : sourceSpatialReflection φ = φ) :
    Coeff 2 →L[ℂ] Coeff 2 :=
  ((fderiv ℂ (sourceSignedGapSequence (p := 2) (by simp) (by norm_num)) φ).comp
    (complexSymmetricSourceCoefficients 2)).comp
      (symmetricDirichletDerivativeEquiv φ hφ href).symm.toContinuousLinearMap

theorem symmetricSignedGapDerivativeMatrix_single (φ : CoeffPair 2)
    (hφ : IsRealType (CoeffPair.toMax 2 φ)) (href : sourceSpatialReflection φ = φ) (n m : ℤ) :
    symmetricSignedGapDerivativeMatrix φ hφ href (lp.single 2 m 1) n =
      (if n = m then 1 else 0) -
        (fderiv ℂ (fun ψ : CoeffPair 2 => canonicalPeriodOneBoundaryRoots
          (by simp) (by norm_num) .neumann ψ n) φ)
          (complexSymmetricSourceCoefficients 2 (symmetricDirichletDualCoordinate φ m)) := by
  obtain ⟨_,_,hr,hD⟩ := exists_sourceBoundaryDisplacement_analytic_common_domain
    (p := 2) (by simp) (by norm_num)
  have hd := (hD .dirichlet φ (hr hφ)).differentiableAt
  have hn := (hD .neumann φ (hr hφ)).differentiableAt
  change (fderiv ℂ (sourceSignedGapSequence (p := 2) (by simp) (by norm_num)) φ)
    (complexSymmetricSourceCoefficients 2
      ((symmetricDirichletDerivativeEquiv φ hφ href).symm (lp.single 2 m 1))) n = _
  rw [symmetricDirichletDerivativeEquiv_symm_single]
  unfold sourceSignedGapSequence
  rw [fderiv_fun_sub hd hn]
  change (symmetricDirichletDerivative φ (symmetricDirichletDualCoordinate φ m)) n -
    (fderiv ℂ (sourceBoundaryDisplacement (p := 2) (by simp) (by norm_num) .neumann) φ)
      (complexSymmetricSourceCoefficients 2 (symmetricDirichletDualCoordinate φ m)) n = _
  rw [symmetricDirichletDerivative_dualCoordinate φ hφ href,
    fderiv_sourceBoundaryDisplacement_apply_of_differentiableAt
      (by simp) (by norm_num) .neumann φ _ n hn]
  by_cases he : n = m
  · subst n; simp
  · simp [he]

/-- Each noncoincident matrix entry is the actual characteristic quotient subtracted from identity. -/
theorem symmetricSignedGapDerivativeMatrix_single_of_ne (φ : CoeffPair 2)
    (hφ : IsRealType (CoeffPair.toMax 2 φ)) (href : sourceSpatialReflection φ = φ) (n m : ℤ)
    (hne : canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .neumann φ n ≠
      canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet φ m) :
    let ν := canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .neumann φ n
    let μ := canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet φ m
    symmetricSignedGapDerivativeMatrix φ hφ href (lp.single 2 m 1) n =
      (if n = m then 1 else 0) -
        canonicalDiscriminant (by simp) (periodOnePotential φ) ν *
          periodOneBoundaryCharacteristic (by simp) (by norm_num) .neumann φ μ /
          (canonicalDiscriminant (by simp) (periodOnePotential φ) μ * (ν-μ) *
            deriv (periodOneBoundaryCharacteristic (by simp) (by norm_num) .neumann φ) ν) := by
  dsimp only
  rw [symmetricSignedGapDerivativeMatrix_single φ hφ href,
    fderiv_neumannRoot_dualCoordinate_of_ne φ hφ href n m hne]

/-- The apparent singularity at a collapsed gap has diagonal value two. -/
theorem symmetricSignedGapDerivativeMatrix_collapsed_diagonal (φ : CoeffPair 2)
    (hφ : IsRealType (CoeffPair.toMax 2 φ)) (href : sourceSpatialReflection φ = φ) (n : ℤ)
    (he : canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .neumann φ n =
      canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet φ n) :
    symmetricSignedGapDerivativeMatrix φ hφ href (lp.single 2 n 1) n = 2 := by
  rw [symmetricSignedGapDerivativeMatrix_single φ hφ href,
    fderiv_neumannRoot_dualCoordinate_of_eq φ hφ href n n he, if_pos rfl]
  norm_num

end NLS.ZakharovShabat
