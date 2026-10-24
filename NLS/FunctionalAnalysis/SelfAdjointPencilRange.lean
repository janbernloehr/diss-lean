import NLS.FunctionalAnalysis.ClosedPencilRange

/-! # Nonreal pencils of self-adjoint partial operators

Orthogonal separation proves dense range. Together with the closed-range
estimate this gives actual bijectivity on the unbounded operator domain.
-/
noncomputable section
set_option autoImplicit false
open Set
namespace NLS.FunctionalAnalysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The nonreal spectral pencil of a self-adjoint partial operator has dense range. -/
theorem denseRange_linearPMapPencil_of_isSelfAdjoint {T : E →ₗ.[ℂ] E}
    (hT : IsSelfAdjoint T) (z : ℂ) (hz : z.im ≠ 0) :
    DenseRange (linearPMapPencil T z) := by
  have he : T.adjoint = T := LinearPMap.isSelfAdjoint_def.mp hT
  have hs : T.IsFormalAdjoint T := by
    simpa only [he] using LinearPMap.adjoint_isFormalAdjoint hT.dense_domain
  have horth : (LinearMap.range (linearPMapPencil T z)).orthogonal = ⊥ := by
    apply le_antisymm _ bot_le
    intro v hv
    have hp (x : T.domain) : inner ℂ v (T x) = z * inner ℂ v (x : E) := by
      have h := ((LinearMap.range (linearPMapPencil T z)).mem_orthogonal' v).mp hv
        (linearPMapPencil T z x) ⟨x,rfl⟩
      rw [linearPMapPencil_apply,inner_sub_right,inner_smul_right] at h
      exact (sub_eq_zero.mp h).symm
    have hd : v ∈ T.adjoint.domain := by
      apply LinearPMap.mem_adjoint_domain_of_exists
      refine ⟨star z • v,fun x => ?_⟩
      rw [inner_smul_left,hp]
      simp
    have ha : T.adjoint ⟨v,hd⟩ = star z • v := by
      apply LinearPMap.adjoint_apply_eq hT.dense_domain
      intro x
      rw [inner_smul_left,hp]
      simp
    have hvT : v ∈ T.domain := by rwa [he] at hd
    have hTv : T ⟨v,hvT⟩ = star z • v :=
      ((le_of_eq he).2 (show ((⟨v,hd⟩ : T.adjoint.domain) : E) =
        ((⟨v,hvT⟩ : T.domain) : E) from rfl)).symm.trans ha
    have hn : (star z).im ≠ 0 := by simpa using hz
    have hzero : linearPMapPencil T (star z) ⟨v,hvT⟩ = 0 := by
      rw [linearPMapPencil_apply,hTv,sub_self]
    have hvzero := (linearPMapPencil_injective_of_im_ne_zero hs (star z) hn)
      (show linearPMapPencil T (star z) ⟨v,hvT⟩ = linearPMapPencil T (star z) 0 by
        simpa only [map_zero] using hzero)
    simpa only [Submodule.mem_bot,ZeroMemClass.coe_zero] using congrArg Subtype.val hvzero
  have hd : Dense (↑(LinearMap.range (linearPMapPencil T z)) : Set E) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr
      ((LinearMap.range (linearPMapPencil T z)).topologicalClosure_eq_top_iff.mpr horth)
  exact hd

/-- At a nonreal parameter a self-adjoint partial operator has an actual
inverse on every base-space vector. Boundedness follows from the preceding estimate. -/
theorem linearPMapPencil_bijective_of_isSelfAdjoint {T : E →ₗ.[ℂ] E}
    (hT : IsSelfAdjoint T) (z : ℂ) (hz : z.im ≠ 0) :
    Function.Bijective (linearPMapPencil T z) := by
  have hs : T.IsFormalAdjoint T := by
    simpa only [LinearPMap.isSelfAdjoint_def.mp hT] using
      LinearPMap.adjoint_isFormalAdjoint hT.dense_domain
  refine ⟨linearPMapPencil_injective_of_im_ne_zero hs z hz,?_⟩
  have hd := denseRange_linearPMapPencil_of_isSelfAdjoint hT z hz
  have hc := isClosed_range_linearPMapPencil_of_im_ne_zero hT.isClosed hs z hz
  intro y
  have hy := hd y
  rw [hc.closure_eq] at hy
  exact hy

end NLS.FunctionalAnalysis
