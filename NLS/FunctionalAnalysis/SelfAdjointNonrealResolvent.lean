import NLS.FunctionalAnalysis.SelfAdjointPencilRange

/-! # Bounded nonreal resolvents of actual self-adjoint partial operators -/
noncomputable section
set_option autoImplicit false
namespace NLS.FunctionalAnalysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {T : E →ₗ.[ℂ] E}

/-- The actual nonreal pencil is a linear equivalence from its operator domain. -/
def selfAdjointPencilEquiv (hT : IsSelfAdjoint T) (z : ℂ) (hz : z.im ≠ 0) :
    T.domain ≃ₗ[ℂ] E :=
  LinearEquiv.ofBijective (linearPMapPencil T z)
    (linearPMapPencil_bijective_of_isSelfAdjoint hT z hz)

/-- The bounded inverse with values in the actual domain, carrying its inherited norm. -/
def selfAdjointNonrealResolventToDomain (hT : IsSelfAdjoint T) (z : ℂ) (hz : z.im ≠ 0) :
    E →L[ℂ] T.domain :=
  (selfAdjointPencilEquiv hT z hz).symm.toLinearMap.mkContinuous (1 / |z.im|) (by
    intro y
    have hs : T.IsFormalAdjoint T := by
      simpa only [LinearPMap.isSelfAdjoint_def.mp hT] using
        LinearPMap.adjoint_isFormalAdjoint hT.dense_domain
    have he : linearPMapPencil T z ((selfAdjointPencilEquiv hT z hz).symm y) = y :=
      (selfAdjointPencilEquiv hT z hz).apply_symm_apply y
    have h := norm_le_linearPMapPencil_div_im hs z hz ((selfAdjointPencilEquiv hT z hz).symm y)
    rw [he] at h
    simpa only [div_eq_mul_inv,one_mul,mul_one,mul_comm] using! h)

/-- The bounded resolvent on the original Hilbert base space. -/
def selfAdjointNonrealResolvent (hT : IsSelfAdjoint T) (z : ℂ) (hz : z.im ≠ 0) : E →L[ℂ] E :=
  T.domain.subtypeL.comp (selfAdjointNonrealResolventToDomain hT z hz)

/-- The constructed inverse solves the original pencil for every base-space vector. -/
theorem linearPMapPencil_selfAdjointNonrealResolventToDomain
    (hT : IsSelfAdjoint T) (z : ℂ) (hz : z.im ≠ 0) (y : E) :
    linearPMapPencil T z (selfAdjointNonrealResolventToDomain hT z hz y) = y :=
  (selfAdjointPencilEquiv hT z hz).apply_symm_apply y

/-- It also recovers every element of the actual operator domain. -/
theorem selfAdjointNonrealResolventToDomain_linearPMapPencil
    (hT : IsSelfAdjoint T) (z : ℂ) (hz : z.im ≠ 0) (x : T.domain) :
    selfAdjointNonrealResolventToDomain hT z hz (linearPMapPencil T z x) = x :=
  (selfAdjointPencilEquiv hT z hz).symm_apply_apply x

/-- The base-space resolvent satisfies the standard nonreal operator-norm bound. -/
theorem norm_selfAdjointNonrealResolvent_le
    (hT : IsSelfAdjoint T) (z : ℂ) (hz : z.im ≠ 0) :
    ‖selfAdjointNonrealResolvent hT z hz‖ ≤ 1 / |z.im| := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro y
  have hs : T.IsFormalAdjoint T := by
    simpa only [LinearPMap.isSelfAdjoint_def.mp hT] using
      LinearPMap.adjoint_isFormalAdjoint hT.dense_domain
  have h := norm_le_linearPMapPencil_div_im hs z hz
    (selfAdjointNonrealResolventToDomain hT z hz y)
  rw [linearPMapPencil_selfAdjointNonrealResolventToDomain] at h
  simpa only [selfAdjointNonrealResolvent,ContinuousLinearMap.comp_apply,
    Submodule.subtypeL_apply,div_eq_mul_inv,one_mul,mul_one,mul_comm] using! h

end NLS.FunctionalAnalysis
