import NLS.ZakharovShabat.SymmetricDirichletDerivative

/-! # Actual Dirichlet dual directions and cross-boundary derivatives

Normalized anti-discriminant Hamiltonian directions, averaged under
reflection, are dual to the actual Dirichlet root cotangents. Their
Neumann root variations have the characteristic quotient of the global
signed-gap argument, with the coincident value equal to minus one.
-/
noncomputable section
open Set Complex NLS.Poisson
namespace NLS.ZakharovShabat

private theorem terminal_discriminant_ne_zero (φ : CoeffPair 2)
    (href : sourceSpatialReflection φ = φ) (m : ℤ) :
    canonicalDiscriminant (by simp) (periodOnePotential φ)
      (canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet φ m) ≠ 0 := by
  let μ := canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet φ m
  have hz : sourceAntiDiscriminantCandidate (by simp) (by norm_num) φ μ = 0 := by
    have h := sourceAntiDiscriminant_spatialReflection (by simp) (by norm_num) φ μ
    rw [href] at h
    linear_combination (1/2 : ℂ)*h
  have h := sourceDiscriminant_sq_sub_four (by simp) (by norm_num) φ μ
  rw [hz, periodOneBoundaryCharacteristic_at_canonicalRoot_eq_zero] at h
  intro he
  rw [he] at h
  norm_num at h

/-- A normalized actual Hamiltonian direction before reflection averaging. -/
def symmetricDirichletDualVector (φ : CoeffPair 2) (m : ℤ) : CoeffPair 2 :=
  let μ := canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet φ m
  (-2 / canonicalDiscriminant (by simp) (periodOnePotential φ) μ) •
    sourceHamiltonianVector (by norm_num)
      (fun ψ : CoeffPair 2 => sourceAntiDiscriminantCandidate (by simp) (by norm_num) ψ μ) φ

/-- Symmetric Fourier coordinates of the averaged Dirichlet dual direction. -/
def symmetricDirichletDualCoordinate (φ : CoeffPair 2) (m : ℤ) : Coeff 2 :=
  ((1/2 : ℂ) • (symmetricDirichletDualVector φ m +
    sourceSpatialReflection (symmetricDirichletDualVector φ m))).snd

theorem fderiv_boundaryRoot_symmetricDirichletDualCoordinate
    (φ : CoeffPair 2) (hφ : IsRealType (CoeffPair.toMax 2 φ))
    (href : sourceSpatialReflection φ = φ) (b : BoundaryCondition) (n m : ℤ) :
    (fderiv ℂ (fun ψ : CoeffPair 2 => canonicalPeriodOneBoundaryRoots
      (by simp) (by norm_num) b ψ n) φ)
      (complexSymmetricSourceCoefficients 2 (symmetricDirichletDualCoordinate φ m)) =
    (-2 / canonicalDiscriminant (by simp) (periodOnePotential φ)
      (canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet φ m)) *
      sourceBoundaryRootAntiDiscriminantBracket (by simp) (by norm_num) (by norm_num) b φ n
        (canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet φ m) := by
  unfold symmetricDirichletDualCoordinate
  rw [complexSymmetricSourceCoefficients_average]
  simp only [map_smul, map_add, smul_eq_mul]
  rw [fderiv_boundaryRoot_spatialReflection_of_fixed (by simp) (by norm_num) b φ hφ href]
  simp only [symmetricDirichletDualVector, map_smul, smul_eq_mul,
    fderiv_apply_sourceHamiltonianVector, sourceBoundaryRootAntiDiscriminantBracket]
  ring

/-- The full actual Dirichlet derivative takes each dual coordinate to its coordinate vector. -/
theorem symmetricDirichletDerivative_dualCoordinate (φ : CoeffPair 2)
    (hφ : IsRealType (CoeffPair.toMax 2 φ)) (href : sourceSpatialReflection φ = φ) (m : ℤ) :
    symmetricDirichletDerivative φ (symmetricDirichletDualCoordinate φ m) = lp.single 2 m 1 := by
  ext n
  rw [symmetricDirichletDerivative_apply φ hφ,
    fderiv_boundaryRoot_symmetricDirichletDualCoordinate φ hφ href]
  by_cases hn : n = m
  · subst n
    rw [sourceBoundaryRootAntiDiscriminantBracket_at_root (by simp) (by norm_num)
      (by norm_num) .dirichlet φ hφ]
    simp only [BoundaryCondition.extensionSign, lp.single_apply, Pi.single_eq_same]
    field_simp
    exact div_self (terminal_discriminant_ne_zero φ href m)
  · have hne := (injective_canonicalPeriodOneBoundaryRoots_of_realType
      (by simp) (by norm_num) .dirichlet φ hφ).ne hn
    rw [sourceBoundaryRootAntiDiscriminantBracket_eq (by simp) (by norm_num)
      (by norm_num) .dirichlet φ hφ n _ hne,
      periodOneBoundaryCharacteristic_at_canonicalRoot_eq_zero]
    simp [hn]

/-- Distinct cross-boundary parameters give the actual characteristic quotient. -/
theorem fderiv_neumannRoot_dualCoordinate_of_ne (φ : CoeffPair 2)
    (hφ : IsRealType (CoeffPair.toMax 2 φ)) (href : sourceSpatialReflection φ = φ) (n m : ℤ)
    (hne : canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .neumann φ n ≠
      canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet φ m) :
    let ν := canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .neumann φ n
    let μ := canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet φ m
    (fderiv ℂ (fun ψ : CoeffPair 2 => canonicalPeriodOneBoundaryRoots
      (by simp) (by norm_num) .neumann ψ n) φ)
      (complexSymmetricSourceCoefficients 2 (symmetricDirichletDualCoordinate φ m)) =
        canonicalDiscriminant (by simp) (periodOnePotential φ) ν *
          periodOneBoundaryCharacteristic (by simp) (by norm_num) .neumann φ μ /
          (canonicalDiscriminant (by simp) (periodOnePotential φ) μ * (ν-μ) *
            deriv (periodOneBoundaryCharacteristic (by simp) (by norm_num) .neumann φ) ν) := by
  dsimp only
  rw [fderiv_boundaryRoot_symmetricDirichletDualCoordinate φ hφ href,
    sourceBoundaryRootAntiDiscriminantBracket_eq (by simp) (by norm_num)
      (by norm_num) .neumann φ hφ n _ hne]
  simp only [BoundaryCondition.extensionSign, div_eq_mul_inv, mul_inv_rev]
  ring

/-- At coincident Dirichlet/Neumann roots the filled cross-boundary derivative is minus one. -/
theorem fderiv_neumannRoot_dualCoordinate_of_eq (φ : CoeffPair 2)
    (hφ : IsRealType (CoeffPair.toMax 2 φ)) (href : sourceSpatialReflection φ = φ) (n m : ℤ)
    (he : canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .neumann φ n =
      canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet φ m) :
    (fderiv ℂ (fun ψ : CoeffPair 2 => canonicalPeriodOneBoundaryRoots
      (by simp) (by norm_num) .neumann ψ n) φ)
      (complexSymmetricSourceCoefficients 2 (symmetricDirichletDualCoordinate φ m)) = -1 := by
  rw [fderiv_boundaryRoot_symmetricDirichletDualCoordinate φ hφ href, ← he,
    sourceBoundaryRootAntiDiscriminantBracket_at_root (by simp) (by norm_num)
      (by norm_num) .neumann φ hφ]
  simp only [BoundaryCondition.extensionSign]
  rw [he]
  field_simp
  rw [div_self (terminal_discriminant_ne_zero φ href m)]

end NLS.ZakharovShabat
