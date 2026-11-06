import NLS.FunctionalAnalysis.CompactScalarPerturbation
import Mathlib.Analysis.InnerProductSpace.Adjoint

noncomputable section
set_option autoImplicit false
open Set
namespace NLS.FunctionalAnalysis

/-- A bounded Hilbert operator with compact normal defect has closed
range. Adding the finite-dimensional kernel projection makes its normal
operator invertible and constructs a projection onto its actual range. -/
theorem isClosed_range_of_compact_normal_defect
    {E Y : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (T : E →L[ℝ] Y)
    (hc : IsCompactOperator (ContinuousLinearMap.id ℝ E-T.adjoint.comp T)) :
    IsClosed (range T) := by
  let A := T.adjoint.comp T
  have hA : IsCompactOperator (A-(1 : E →L[ℝ] E)) := by
    have he : A-1 = -(ContinuousLinearMap.id ℝ E-A) := by change A-1 = -(1-A); abel
    rw [he]
    exact hc.neg
  let N := T.ker
  have hf : FiniteDimensional ℝ N := by
    have hh := NLS.CompactScalarPerturbation.finiteDimensional_ker A (c := (1 : ℝ)) one_ne_zero
      (by simpa only [one_smul] using hA)
    have he : A.ker = N := ContinuousLinearMap.ker_adjoint_comp_self T
    rw [he] at hh
    exact hh
  let _ := hf
  let _ : CompleteSpace N := T.isClosed_ker.completeSpace_coe
  let P := N.starProjection
  have hPc : IsCompactOperator P := by
    have hi : IsCompactOperator (id : N → N) := (isCompactOperator_id_iff_finiteDimensional (𝕜 := ℝ)).mpr inferInstance
    exact (hi.comp_clm N.orthogonalProjectionOnto).clm_comp N.subtypeL
  let U := A+P
  have hUc : IsCompactOperator (U-(1 : E →L[ℝ] E)) := by
    have he : U-1 = (A-1)+P := by dsimp only [U]; abel
    rw [he]
    exact hA.add hPc
  have hUi : Function.Injective U := by
    apply (injective_iff_map_eq_zero U).mpr
    intro x hx
    have hPx : P x ∈ N := N.starProjection_apply_mem x
    have ho := N.starProjection_inner_eq_zero x (P x) hPx
    rw [inner_sub_left] at ho
    have hpinner : inner ℝ (P x) x = ‖P x‖^2 := by
      rw [real_inner_comm x (P x)]
      rw [real_inner_self_eq_norm_sq] at ho
      linarith
    have hh := congrArg (fun y : E => inner ℝ y x) hx
    rw [inner_zero_left] at hh
    change inner ℝ (T.adjoint (T x)+P x) x = 0 at hh
    rw [inner_add_left,ContinuousLinearMap.adjoint_inner_left,real_inner_self_eq_norm_sq,hpinner] at hh
    have hTx : T x = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg (T x),sq_nonneg ‖P x‖])
    have hPzero : P x = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg (P x),sq_nonneg ‖T x‖])
    have hxN : x ∈ N := hTx
    have hPself : P x = x := N.starProjection_eq_self_iff.mpr hxN
    exact hPself.symm.trans hPzero
  have hUb := NLS.CompactScalarPerturbation.bijective_of_injective U (c := (1 : ℝ)) one_ne_zero
    (by simpa only [one_smul] using hUc) hUi
  let V := ContinuousLinearEquiv.ofBijective U (LinearMap.ker_eq_bot.mpr hUb.1) (LinearMap.range_eq_top.mpr hUb.2)
  let B := T.comp (V.symm.toContinuousLinearMap.comp T.adjoint)
  have hBT (x : E) : B (T x) = T x := by
    have hPx : P x ∈ N := N.starProjection_apply_mem x
    have hTP : T (P x) = 0 := hPx
    have hPP : P (P x) = P x := N.starProjection_eq_self_iff.mpr hPx
    have hAP : A (P x) = 0 := by change T.adjoint (T (P x)) = 0; rw [hTP,map_zero]
    have he : U (x-P x) = A x := by
      change A (x-P x)+P (x-P x) = A x
      rw [map_sub,map_sub,hAP,hPP,sub_self,sub_zero,add_zero]
    have hv : V.symm (A x) = x-P x := V.symm_apply_eq.mpr he.symm
    change T (V.symm (A x)) = T x
    rw [hv,map_sub,hTP,sub_zero]
  have hr : range T = {y | B y = y} := by
    ext y
    constructor
    · rintro ⟨x,rfl⟩
      exact hBT x
    · intro hy
      exact ⟨V.symm (T.adjoint y),hy⟩
  rw [hr]
  exact isClosed_eq B.continuous continuous_id

end NLS.FunctionalAnalysis
