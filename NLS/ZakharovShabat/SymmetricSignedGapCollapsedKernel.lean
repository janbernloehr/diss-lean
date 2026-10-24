import NLS.ZakharovShabat.SymmetricSignedGapGradientMatrix

/-! # A gradient-matrix kernel vanishes at collapsed gaps

At a coincident indexed Dirichlet/Neumann pair, the corresponding column
of the actual signed-gap derivative matrix is exactly twice its coordinate
vector. The corresponding transpose equation therefore forces that
coordinate of every kernel sequence to vanish.
-/
noncomputable section
open Set Complex
namespace NLS.ZakharovShabat

/-- At a collapsed gap the full derivative-matrix column has only its diagonal entry. -/
theorem symmetricSignedGapDerivativeMatrix_single_of_coincident (φ : CoeffPair 2)
    (hφ : IsRealType (CoeffPair.toMax 2 φ)) (href : sourceSpatialReflection φ = φ)
    (m : ℤ)
    (he : canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .neumann φ m =
      canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet φ m) :
    symmetricSignedGapDerivativeMatrix φ hφ href (lp.single 2 m 1) =
      (2 : ℂ) • lp.single 2 m 1 := by
  ext n
  by_cases hn : n = m
  · subst n
    rw [symmetricSignedGapDerivativeMatrix_collapsed_diagonal φ hφ href m he]
    simp [lp.coeFn_smul]
  · have hne : canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .neumann φ n ≠
        canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet φ m := by
      rw [← he]
      exact (injective_canonicalPeriodOneBoundaryRoots_of_realType
        (by simp) (by norm_num) .neumann φ hφ).ne hn
    rw [symmetricSignedGapDerivativeMatrix_single_of_ne φ hφ href n m hne]
    rw [← he, periodOneBoundaryCharacteristic_at_canonicalRoot_eq_zero]
    simp [hn, lp.coeFn_smul]

/-- The transpose row for a coincident pair is exactly twice that input coordinate. -/
theorem symmetricSignedGapGradientMatrix_apply_of_coincident (φ : CoeffPair 2)
    (hφ : IsRealType (CoeffPair.toMax 2 φ)) (href : sourceSpatialReflection φ = φ)
    (τ : Coeff 2) (m : ℤ)
    (he : canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .neumann φ m =
      canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet φ m) :
    symmetricSignedGapGradientMatrix φ hφ href τ m = 2 * τ m := by
  change Coeff.hilbertCotangentCoefficients
    ((Coeff.dualPairing τ).comp (symmetricSignedGapDerivativeMatrix φ hφ href)) m = _
  rw [Coeff.hilbertCotangentCoefficients_apply]
  change Coeff.dualPairing τ
    (symmetricSignedGapDerivativeMatrix φ hφ href (lp.single 2 m 1)) = _
  rw [symmetricSignedGapDerivativeMatrix_single_of_coincident φ hφ href m he,
    map_smul, Coeff.dualPairing_hilbert_single_right]
  rfl

/-- Any actual transpose-kernel vector vanishes at every coincident indexed pair. -/
theorem eq_zero_at_coincident_of_mem_signedGapGradientMatrix_ker (φ : CoeffPair 2)
    (hφ : IsRealType (CoeffPair.toMax 2 φ)) (href : sourceSpatialReflection φ = φ)
    (τ : Coeff 2) (hτ : symmetricSignedGapGradientMatrix φ hφ href τ = 0) (m : ℤ)
    (he : canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .neumann φ m =
      canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet φ m) : τ m = 0 := by
  have h := symmetricSignedGapGradientMatrix_apply_of_coincident φ hφ href τ m he
  rw [hτ] at h
  have hz : (2 : ℂ) * τ m = 0 := h.symm
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

/-- A closed actual periodic gap forces the same zero coordinate. -/
theorem eq_zero_at_closed_gap_of_mem_signedGapGradientMatrix_ker (φ : CoeffPair 2)
    (hφ : IsRealType (CoeffPair.toMax 2 φ)) (href : sourceSpatialReflection φ = φ)
    (τ : Coeff 2) (hτ : symmetricSignedGapGradientMatrix φ hφ href τ = 0) (m : ℤ)
    (hg : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential φ) (periodOnePotential_mem φ) m = 0) : τ m = 0 := by
  have he := sub_eq_zero.mp hg
  have hn := canonicalPeriodOneBoundaryRoots_eq_of_collapsed_gap
    (by simp) (by norm_num) .neumann φ hφ m he.symm
  have hd := canonicalPeriodOneBoundaryRoots_eq_of_collapsed_gap
    (by simp) (by norm_num) .dirichlet φ hφ m he.symm
  exact eq_zero_at_coincident_of_mem_signedGapGradientMatrix_ker φ hφ href τ hτ m
    (hn.trans hd.symm)

/-- Kernel support lies in the actual open periodic gaps. -/
theorem support_subset_openGaps_of_mem_signedGapGradientMatrix_ker (φ : CoeffPair 2)
    (hφ : IsRealType (CoeffPair.toMax 2 φ)) (href : sourceSpatialReflection φ = φ)
    (τ : Coeff 2) (hτ : symmetricSignedGapGradientMatrix φ hφ href τ = 0) :
    Function.support τ ⊆ {m : ℤ | canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential φ) (periodOnePotential_mem φ) m ≠ 0} := by
  intro m hm hg
  exact hm (eq_zero_at_closed_gap_of_mem_signedGapGradientMatrix_ker φ hφ href τ hτ m hg)

/-- At a finite-gap source every gradient-matrix kernel vector has finite support. -/
theorem finite_support_of_mem_signedGapGradientMatrix_ker (φ : CoeffPair 2)
    (hφ : IsRealType (CoeffPair.toMax 2 φ)) (href : sourceSpatialReflection φ = φ)
    (hf : (⟨φ, hφ⟩ : realTypeSourceSubmodule 2) ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (τ : Coeff 2) (hτ : symmetricSignedGapGradientMatrix φ hφ href τ = 0) :
    (Function.support τ).Finite :=
  hf.subset (support_subset_openGaps_of_mem_signedGapGradientMatrix_ker φ hφ href τ hτ)

end NLS.ZakharovShabat
