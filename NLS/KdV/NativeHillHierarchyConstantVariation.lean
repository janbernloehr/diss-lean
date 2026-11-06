import NLS.KdV.NativeHillHierarchyHamiltonian
import NLS.KdV.HillHierarchyConstantVariation
import NLS.KdV.NativeHamiltonianShifts

/-! # Constant-shift derivatives on the full native hierarchy domains

The smooth physical derivative extends by native smooth density and
continuity of the actual Frechet differential. No smoothness premise is
retained in the resulting derivative identity.
-/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.Fourier NLS.ZakharovShabat
open scoped ContDiff
namespace NLS.KdV

theorem smul_nativeScalarConstant (s : ℕ) (a b : ℂ) :
    a • nativeScalarConstant s b = nativeScalarConstant s (a*b) := by
  apply Subtype.ext
  funext n
  by_cases hn : (0 : ℤ)=n <;>
    simp [nativeScalarConstant,WeightedCoeff.smul_val,WeightedCoeff.ofFinsupp_apply,hn]

theorem hierarchySobolevInclusion_nativeScalarConstant (s t : ℕ) (ht : t ≤ s) (c : ℂ) :
    hierarchySobolevInclusion s t ht (nativeScalarConstant s c) = nativeScalarConstant t c := by
  apply Subtype.ext
  funext n
  simp only [hierarchySobolevInclusion_apply,nativeScalarConstant,WeightedCoeff.ofFinsupp_apply]

private theorem hasDerivAt_analytic_affine
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (H : E → ℂ) (hH : ∀ q, AnalyticAt ℂ H q) (q C : E) (c : ℂ) :
    HasDerivAt (fun d : ℂ => H (q+d • C)) (fderiv ℂ H (q+c • C) C) c := by
  have hc : HasDerivAt (fun d : ℂ => q+d • C) C c := by
    simpa only [id_eq,one_smul] using! ((hasDerivAt_id c).smul_const C).const_add q
  simpa only [Function.comp_def] using!
    (hH (q+c • C)).differentiableAt.hasFDerivAt.comp_hasDerivAt c hc

/-- The actual full native differential in the constant direction is the
previous original hierarchy member, with coefficient 2*(2m+3). -/
theorem nativeHillHierarchyHamiltonian_constant_direction (m : ℕ) (q : ScalarSobolev (m+1)) :
    fderiv ℂ (nativeHillHierarchyHamiltonian (m+1)) q (nativeScalarConstant (m+1) 1) =
      2*((2*m+3 : ℕ) : ℂ)*nativeHillHierarchyHamiltonian m
        (hierarchySobolevInclusion (m+1) m (by omega) q) := by
  let C := nativeScalarConstant (m+1) 1
  have hD : Continuous (fun v : ScalarSobolev (m+1) => fderiv ℂ (nativeHillHierarchyHamiltonian (m+1)) v) :=
    continuous_iff_continuousAt.mpr fun v => (analyticAt_nativeHillHierarchyHamiltonian (m+1) v).fderiv.continuousAt
  have hF : Continuous (fun v : ScalarSobolev (m+1) =>
      fderiv ℂ (nativeHillHierarchyHamiltonian (m+1)) v C) := hD.clm_apply continuous_const
  have hG : Continuous (fun v : ScalarSobolev (m+1) =>
      2*((2*m+3 : ℕ) : ℂ)*nativeHillHierarchyHamiltonian m (hierarchySobolevInclusion (m+1) m (by omega) v)) :=
    continuous_const.mul ((continuous_iff_continuousAt.mpr fun v =>
      (analyticAt_nativeHillHierarchyHamiltonian m v).continuousAt).comp
        (hierarchySobolevInclusion (m+1) m (by omega)).continuous)
  have he := eq_of_continuous_of_smooth_scalarSobolev (m+1) _ _ hF hG (by
    intro v f hf hp hc
    have hper (c : ℂ) : Function.Periodic (fun x => f x+c) 1 := by
      intro x
      change f (x+1)+c=f x+c
      rw [hp x]
    have hcoef (c : ℂ) (n : ℤ) : (v+c • C).val n = periodOneCoefficient (fun x => f x+c) n := by
      change (v+c • nativeScalarConstant (m+1) 1).val n = _
      rw [smul_nativeScalarConstant,mul_one]
      exact native_add_constant_coefficients (m+1) v f hf.continuous c hc n
    have heq (c : ℂ) : nativeHillHierarchyHamiltonian (m+1) (v+c • C) =
        classicalHillHierarchyHamiltonian (fun x => f x+c) (m+1) :=
      nativeHillHierarchyHamiltonian_eq_classical (m+1) _ _ (hf.add contDiff_const) (hper c) (hcoef c)
    have hN : HasDerivAt (fun c : ℂ => nativeHillHierarchyHamiltonian (m+1) (v+c • C))
        (fderiv ℂ (nativeHillHierarchyHamiltonian (m+1)) v C) 0 := by
      simpa only [zero_smul,add_zero] using!
        hasDerivAt_analytic_affine (nativeHillHierarchyHamiltonian (m+1))
          (analyticAt_nativeHillHierarchyHamiltonian (m+1)) v C 0
    have hfun : (fun c : ℂ => nativeHillHierarchyHamiltonian (m+1) (v+c • C)) =
        (fun c => classicalHillHierarchyHamiltonian (fun x => f x+c) (m+1)) := funext heq
    rw [hfun] at hN
    have hd := hN.unique (hasDerivAt_classicalHillHierarchyHamiltonian_shift_zero m f hf)
    rw [hd,nativeHillHierarchyHamiltonian_eq_classical m _ f hf hp
      (fun n => by simpa only [hierarchySobolevInclusion_apply] using hc n)])
  exact congrFun he q

private theorem hasDerivAt_analytic_affine_of_direction
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (H : E → ℂ) (hH : ∀ q, AnalyticAt ℂ H q) (G : F → ℂ)
    (L : E →L[ℂ] F) (C : E) (C' : F) (b : ℂ) (hC : L C=C')
    (hd : ∀ q, fderiv ℂ H q C=b*G (L q)) (q : E) (c : ℂ) :
    HasDerivAt (fun d : ℂ => H (q+d • C)) (b*G (L q+c • C')) c := by
  have h := hasDerivAt_analytic_affine H hH q C c
  rw [hd,map_add,map_smul,hC] at h
  exact h

/-- The original hierarchy's constant-shift differential holds at EVERY
complex shift and EVERY native source, without a smoothness assumption. -/
theorem hasDerivAt_nativeHillHierarchyHamiltonian_shift (m : ℕ) (q : ScalarSobolev (m+1)) (c : ℂ) :
    HasDerivAt (fun d : ℂ => nativeHillHierarchyHamiltonian (m+1)
      (q+d • nativeScalarConstant (m+1) 1))
      (2*((2*m+3 : ℕ) : ℂ)*nativeHillHierarchyHamiltonian m
        (hierarchySobolevInclusion (m+1) m (by omega) q+c • nativeScalarConstant m 1)) c := by
  exact hasDerivAt_analytic_affine_of_direction
    (E := ScalarSobolev (m+1)) (F := ScalarSobolev m)
    (nativeHillHierarchyHamiltonian (m+1)) (analyticAt_nativeHillHierarchyHamiltonian (m+1))
    (nativeHillHierarchyHamiltonian m) (hierarchySobolevInclusion (m+1) m (by omega))
    (nativeScalarConstant (m+1) 1) (nativeScalarConstant m 1) (2*((2*m+3 : ℕ) : ℂ))
    (hierarchySobolevInclusion_nativeScalarConstant (m+1) m (by omega) 1)
    (nativeHillHierarchyHamiltonian_constant_direction m) q c

end NLS.KdV
