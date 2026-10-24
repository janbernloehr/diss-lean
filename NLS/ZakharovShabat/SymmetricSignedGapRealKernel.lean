import NLS.ZakharovShabat.SymmetricSignedGapGradientMatrix
import NLS.SequenceSpaces.RealDerivativeEntries
import NLS.SequenceSpaces.RealOperatorInverse

/-! # Reality of the actual gradient matrix and its kernel

The actual Dirichlet derivative preserves the real coefficient form, and
so does its bounded inverse. The signed-gap matrix and its ordinary
transpose therefore have real entries. Every complex kernel splits into
real and imaginary kernels; it suffices to prove vanishing on real
coefficient sequences before using a real sign/interlacing argument.
-/
noncomputable section
open Set Complex Filter Topology
namespace NLS.ZakharovShabat

/-- The actual symmetric Dirichlet derivative has real matrix entries at real coordinates. -/
theorem symmetricDirichletDerivative_entries_real (a : RealCoeff 2) (n m : ℤ) :
    (symmetricDirichletDerivative (symmetricSourceCoefficients 2 a) (lp.single 2 m 1) n).im = 0 := by
  have ha : IsRealType (CoeffPair.toMax 2
      (complexSymmetricSourceCoefficients 2 (RealCoeff.complexCLM 2 a))) := by
    rw [complexSymmetricSourceCoefficients_realCoeff]
    exact symmetricSourceCoefficients_realType a
  have hr : ∀ y : Coeff 2, y ∈ Coeff.realLocus 2 →
      symmetricSourceDirichletMap y ∈ Coeff.realLocus 2 := by
    intro y hy n
    have he := RealCoeff.complexCLM_reCLM 2 y hy
    have hsource : IsRealType (CoeffPair.toMax 2 (complexSymmetricSourceCoefficients 2 y)) := by
      rw [← he, complexSymmetricSourceCoefficients_realCoeff]
      exact symmetricSourceCoefficients_realType _
    change (sourceBoundaryDisplacement (by simp) (by norm_num) .dirichlet
      (complexSymmetricSourceCoefficients 2 y) n).im = 0
    rw [sourceBoundaryDisplacement_apply]
    simp only [sub_im, canonicalPeriodOneBoundaryRoots_im_eq_zero
      (by simp) (by norm_num) .dirichlet _ hsource]
    simp
  have h := Coeff.fderiv_entries_real_of_eventually_real
    (show RealCoeff.complexCLM 2 a ∈ Coeff.realLocus 2 by intro k; simp)
    (analyticAt_symmetricSourceDirichletMap _ ha)
    (Filter.Eventually.of_forall hr) n m
  rw [fderiv_symmetricSourceDirichletMap _ ha,
    complexSymmetricSourceCoefficients_realCoeff] at h
  exact h

/-- The actual bounded inverse Dirichlet derivative preserves real coefficient sequences. -/
theorem symmetricDirichletDerivativeEquiv_symm_mapsTo_realLocus (a : RealCoeff 2) :
    let φ := symmetricSourceCoefficients 2 a
    let hφ := symmetricSourceCoefficients_realType a
    let href := congrArg Subtype.val (symmetricRealSourceCoefficients_reflection_fixed a)
    MapsTo (symmetricDirichletDerivativeEquiv φ hφ href).symm
      (Coeff.realLocus 2) (Coeff.realLocus 2) := by
  dsimp only
  let e := symmetricDirichletDerivativeEquiv (symmetricSourceCoefficients 2 a)
    (symmetricSourceCoefficients_realType a)
    (congrArg Subtype.val (symmetricRealSourceCoefficients_reflection_fixed a))
  intro z hz
  apply (Coeff.mem_realLocus_iff_star_eq _).mpr
  apply e.injective
  change symmetricDirichletDerivative (symmetricSourceCoefficients 2 a) (star (e.symm z)) =
    symmetricDirichletDerivative (symmetricSourceCoefficients 2 a) (e.symm z)
  rw [Coeff.operator_star_of_real_entries (by simp) _ (symmetricDirichletDerivative_entries_real a)]
  change star (e (e.symm z)) = e (e.symm z)
  rw [ContinuousLinearEquiv.apply_symm_apply, (Coeff.mem_realLocus_iff_star_eq z).mp hz]

/-- The actual complex signed-gap derivative preserves the real coefficient form. -/
theorem complexSymmetricSignedGapDerivative_mapsTo_realLocus (a : RealCoeff 2) :
    MapsTo (complexSymmetricSignedGapDerivative (symmetricSourceCoefficients 2 a))
      (Coeff.realLocus 2) (Coeff.realLocus 2) := by
  intro z hz n
  have he := RealCoeff.complexCLM_reCLM 2 z hz
  have h := congrArg (fun L : RealCoeff 2 →L[ℝ] Coeff 2 => L (Coeff.reCLM 2 z))
    (complexSymmetricSignedGapDerivative_real_restriction a)
  change complexSymmetricSignedGapDerivative (symmetricSourceCoefficients 2 a)
    (RealCoeff.complexCLM 2 (Coeff.reCLM 2 z)) = _ at h
  rw [he] at h
  rw [h]
  rfl

/-- Matrix columns remain real after the actual inverse Dirichlet coordinate change. -/
theorem symmetricSignedGapDerivativeMatrix_entries_real (a : RealCoeff 2) (n m : ℤ) :
    let φ := symmetricSourceCoefficients 2 a
    let hφ := symmetricSourceCoefficients_realType a
    let href := congrArg Subtype.val (symmetricRealSourceCoefficients_reflection_fixed a)
    (symmetricSignedGapDerivativeMatrix φ hφ href (lp.single 2 m 1) n).im = 0 := by
  apply complexSymmetricSignedGapDerivative_mapsTo_realLocus a
  apply symmetricDirichletDerivativeEquiv_symm_mapsTo_realLocus a
  intro k
  by_cases hk : k = m <;> simp [lp.single_apply, hk]

/-- The ordinary transpose has real entries with the source's gradient convention. -/
theorem symmetricSignedGapGradientMatrix_entries_real (a : RealCoeff 2) (n m : ℤ) :
    let φ := symmetricSourceCoefficients 2 a
    let hφ := symmetricSourceCoefficients_realType a
    let href := congrArg Subtype.val (symmetricRealSourceCoefficients_reflection_fixed a)
    (symmetricSignedGapGradientMatrix φ hφ href (lp.single 2 m 1) n).im = 0 := by
  exact (congrArg Complex.im (symmetricSignedGapGradientMatrix_single
    (symmetricSourceCoefficients 2 a) (symmetricSourceCoefficients_realType a)
    (congrArg Subtype.val (symmetricRealSourceCoefficients_reflection_fixed a)) m n)).trans
      (symmetricSignedGapDerivativeMatrix_entries_real a m n)

/-- Complex injectivity reduces exactly to the actual kernel on real sequences. -/
theorem symmetricSignedGapGradientMatrix_injective_iff_realKernelZero (a : RealCoeff 2) :
    let A := symmetricSignedGapGradientMatrix (symmetricSourceCoefficients 2 a)
      (symmetricSourceCoefficients_realType a)
      (congrArg Subtype.val (symmetricRealSourceCoefficients_reflection_fixed a))
    Function.Injective A ↔ ∀ τ : RealCoeff 2, A (RealCoeff.complexCLM 2 τ) = 0 → τ = 0 := by
  dsimp only
  constructor
  · intro hi τ hτ
    have h := hi (hτ.trans (map_zero _).symm)
    simpa only [map_zero, RealCoeff.reCLM_complexCLM] using congrArg (Coeff.reCLM 2) h
  · intro hk
    apply Coeff.operator_injective_of_realKernelZero (by simp) _
      (symmetricSignedGapGradientMatrix_entries_real a)
    intro τ hreal hτ
    have he := RealCoeff.complexCLM_reCLM 2 τ hreal
    have hz := hk (Coeff.reCLM 2 τ) (he.symm ▸ hτ)
    simpa only [he, map_zero] using congrArg (RealCoeff.complexCLM 2) hz

/-- Any failure of complex injectivity supplies a nonzero real kernel vector. -/
theorem exists_real_kernel_of_not_injective_signedGapGradientMatrix (a : RealCoeff 2) :
    let A := symmetricSignedGapGradientMatrix (symmetricSourceCoefficients 2 a)
      (symmetricSourceCoefficients_realType a)
      (congrArg Subtype.val (symmetricRealSourceCoefficients_reflection_fixed a))
    ¬ Function.Injective A → ∃ τ : RealCoeff 2, τ ≠ 0 ∧ A (RealCoeff.complexCLM 2 τ) = 0 := by
  dsimp only
  intro hn
  by_contra h
  apply hn
  apply (symmetricSignedGapGradientMatrix_injective_iff_realKernelZero a).mpr
  intro τ hτ
  by_contra hne
  exact h ⟨τ, hne, hτ⟩

end NLS.ZakharovShabat
