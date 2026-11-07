import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.LinearAlgebra.SesquilinearForm.Basic
import Mathlib.Topology.Connected.Clopen
import Mathlib.Analysis.Complex.Basic

/-!
# Positivity of invertible Hermitian duality maps

The full dual is represented isometrically. A nonnegative Hermitian form
whose operator is invertible is coercive, by Hahn-Banach and the algebraic
Cauchy-Schwarz inequality. No Hilbert-space identification is substituted.
-/
noncomputable section
open Set Complex Filter Topology
namespace NLS
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The real symmetric form underlying a conjugated full-duality pairing. -/
def realDualityForm (D : F ≃ₗᵢ[ℂ] (E →L[ℂ] ℂ)) (C : E ≃ₗᵢ⋆[ℂ] E)
    (P : E →L[ℂ] F) : LinearMap.BilinForm ℝ E :=
  LinearMap.mk₂ ℝ (fun x y => (D (P x) (C y)).re)
    (fun x y z => by simp only [map_add,add_apply,add_re])
    (fun r x y => by
      rw [← IsScalarTower.algebraMap_smul ℂ r x]
      rw [P.map_smul,D.map_smul]
      change (((algebraMap ℝ ℂ) r) * D (P x) (C y)).re = _
      simp only [RCLike.algebraMap_eq_ofReal,RCLike.ofReal_eq_complex_ofReal,
        Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,smul_eq_mul])
    (fun x y z => by simp only [map_add,add_re])
    (fun r x y => by
      have hC : C (r • y) = ((algebraMap ℝ ℂ) r) • C y := by
        rw [← IsScalarTower.algebraMap_smul ℂ r y,C.map_smulₛₗ]
        simp only [RCLike.algebraMap_eq_ofReal,RCLike.ofReal_eq_complex_ofReal]
        exact congrArg (fun c : ℂ => c • C y) (Complex.conj_ofReal r)
      rw [hC,(D (P x)).map_smul]
      change (((algebraMap ℝ ℂ) r) * D (P x) (C y)).re = _
      simp only [RCLike.algebraMap_eq_ofReal,RCLike.ofReal_eq_complex_ofReal,
        Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,smul_eq_mul])

@[simp] theorem realDualityForm_apply (D : F ≃ₗᵢ[ℂ] (E →L[ℂ] ℂ))
    (C : E ≃ₗᵢ⋆[ℂ] E) (P : E →L[ℂ] F) (x y : E) :
    realDualityForm D C P x y = (D (P x) (C y)).re := rfl

/-- An operator-norm bound for the actual real quadratic form. -/
theorem abs_realDualityForm_le (D : F ≃ₗᵢ[ℂ] (E →L[ℂ] ℂ))
    (C : E ≃ₗᵢ⋆[ℂ] E) (P : E →L[ℂ] F) (x : E) :
    |realDualityForm D C P x x| ≤ ‖P‖*‖x‖^2 := by
  calc
    _ ≤ ‖D (P x) (C x)‖ := Complex.abs_re_le_norm _
    _ ≤ ‖D (P x)‖*‖C x‖ := ContinuousLinearMap.le_opNorm _ _
    _ = ‖P x‖*‖x‖ := by rw [D.norm_map,C.norm_map]
    _ ≤ (‖P‖*‖x‖)*‖x‖ :=
      mul_le_mul_of_nonneg_right (P.le_opNorm x) (norm_nonneg x)
    _ = _ := by ring

/-- A positive Hermitian full-duality isomorphism is coercive on its
unchanged Banach domain. The explicit coefficient uses only its inverse norm. -/
theorem realDualityForm_coercive_of_nonneg (D : F ≃ₗᵢ[ℂ] (E →L[ℂ] ℂ))
    (C : E ≃ₗᵢ⋆[ℂ] E) (P : E ≃L[ℂ] F)
    (hs : (realDualityForm D C P.toContinuousLinearMap).IsSymm)
    (hn : ∀ x, 0 ≤ realDualityForm D C P.toContinuousLinearMap x x) :
    ∀ x, (1/(‖P.symm.toContinuousLinearMap‖+1))*‖x‖^2 ≤
      realDualityForm D C P.toContinuousLinearMap x x := by
  intro x
  obtain ⟨phi,hphi,hvalue⟩ := exists_dual_vector'' ℂ (C x)
  let v := P.symm (D.symm phi)
  have hPv : D (P.toContinuousLinearMap v) = phi := by
    change D (P v) = phi
    simp only [v,P.apply_symm_apply,D.apply_symm_apply]
  have hv : ‖v‖ ≤ ‖P.symm.toContinuousLinearMap‖ := by
    calc
      _ ≤ ‖P.symm.toContinuousLinearMap‖*‖D.symm phi‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖P.symm.toContinuousLinearMap‖*‖phi‖ := by rw [D.symm.norm_map]
      _ ≤ _ := mul_le_of_le_one_right (norm_nonneg _) hphi
  have hpair : realDualityForm D C P.toContinuousLinearMap v x = ‖x‖ := by
    rw [realDualityForm_apply,hPv,hvalue,C.norm_map]
    rw [RCLike.ofReal_eq_complex_ofReal,Complex.ofReal_re]
  have hvv : realDualityForm D C P.toContinuousLinearMap v v ≤ ‖P.symm.toContinuousLinearMap‖ := by
    calc
      _ = (phi (C v)).re := by rw [realDualityForm_apply,hPv]
      _ ≤ ‖phi (C v)‖ := Complex.re_le_norm _
      _ ≤ ‖phi‖*‖C v‖ := phi.le_opNorm _
      _ ≤ ‖v‖ := by rw [C.norm_map]; exact mul_le_of_le_one_left (norm_nonneg _) hphi
      _ ≤ _ := hv
  have hc := (realDualityForm D C P.toContinuousLinearMap).apply_sq_le_of_symm hn hs v x
  rw [hpair] at hc
  have hb := mul_le_mul_of_nonneg_right hvv (hn x)
  rw [one_div,mul_comm,← div_eq_mul_inv]
  apply (div_le_iff₀ (by positivity : 0 < ‖P.symm.toContinuousLinearMap‖+1)).mpr
  nlinarith [hn x]

/-- The full-duality real form is linear in the operator. -/
theorem realDualityForm_sub (D : F ≃ₗᵢ[ℂ] (E →L[ℂ] ℂ))
    (C : E ≃ₗᵢ⋆[ℂ] E) (P Q : E →L[ℂ] F) (x y : E) :
    realDualityForm D C (P-Q) x y =
      realDualityForm D C P x y-realDualityForm D C Q x y := by
  simp only [realDualityForm_apply,sub_apply,map_sub,Complex.sub_re]

/-- Positivity controls the entire dual norm of an operator value by its
quadratic energy and operator norm. Complex phases recover the full dual
norm from the real form, so no norm-attainment assumption is needed. -/
theorem norm_apply_sq_le_realDualityForm_mul_norm
    (D : F ≃ₗᵢ[ℂ] (E →L[ℂ] ℂ)) (C : E ≃ₗᵢ⋆[ℂ] E)
    (P : E →L[ℂ] F) (hs : LinearMap.IsSymm (realDualityForm D C P))
    (hn : ∀ x, 0 ≤ realDualityForm D C P x x) (v : E) :
    ‖P v‖^2 ≤ realDualityForm D C P v v*‖P‖ := by
  let phi := D (P v)
  have hprod : 0 ≤ realDualityForm D C P v v*‖P‖ := mul_nonneg (hn v) (norm_nonneg P)
  have hbound : ‖phi‖ ≤ Real.sqrt (realDualityForm D C P v v*‖P‖) := by
    apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
    intro w
    obtain ⟨c,hc,hvalue⟩ := Complex.exists_norm_eq_mul_self (phi w)
    let y := C.symm (c • w)
    have hy : ‖y‖ = ‖w‖ := by rw [C.symm.norm_map,norm_smul,hc,one_mul]
    have hpair : realDualityForm D C P v y = ‖phi w‖ := by
      change (phi (C (C.symm (c • w)))).re = _
      rw [C.apply_symm_apply,phi.map_smul]
      change (c*phi w).re = _
      rw [← hvalue,Complex.ofReal_re]
    have hcs := (realDualityForm D C P).apply_sq_le_of_symm hn hs v y
    rw [hpair] at hcs
    have hyy := (le_abs_self (realDualityForm D C P y y)).trans
      (abs_realDualityForm_le D C P y)
    rw [hy] at hyy
    have hsq : ‖phi w‖^2 ≤ (realDualityForm D C P v v*‖P‖)*‖w‖^2 :=
      hcs.trans (by nlinarith [mul_le_mul_of_nonneg_left hyy (hn v)])
    apply (sq_le_sq₀ (norm_nonneg (phi w))
      (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg w))).mp
    rw [mul_pow,Real.sq_sqrt hprod]
    exact hsq
  calc
    ‖P v‖^2 = ‖phi‖^2 := by rw [D.norm_map]
    _ ≤ (Real.sqrt (realDualityForm D C P v v*‖P‖))^2 :=
      (sq_le_sq₀ (norm_nonneg phi) (Real.sqrt_nonneg _)).mpr hbound
    _ = _ := Real.sq_sqrt hprod

/-- Positivity cannot change in a continuous connected family of invertible
Hermitian full-duality operators. No spectral theorem or Hilbert norm is used. -/
theorem nonneg_realDualityForm_of_preconnected
    [CompleteSpace E] [CompleteSpace F]
    {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    (D : F ≃ₗᵢ[ℂ] (E →L[ℂ] ℂ)) (C : E ≃ₗᵢ⋆[ℂ] E)
    (P : X → E →L[ℂ] F) (hP : Continuous P)
    (hb : ∀ x, Function.Bijective (P x))
    (hs : ∀ x, (realDualityForm D C (P x)).IsSymm)
    (hstart : ∃ x, ∀ v, 0 ≤ realDualityForm D C (P x) v v) :
    ∀ x v, 0 ≤ realDualityForm D C (P x) v v := by
  let S : Set X := {x | ∀ v, 0 ≤ realDualityForm D C (P x) v v}
  have hclosed : IsClosed S := by
    have he : S = ⋂ v : E, {x | 0 ≤ realDualityForm D C (P x) v v} := by
      ext x
      simp only [S,mem_ofPred_eq,mem_iInter]
    rw [he]
    apply isClosed_iInter
    intro v
    exact isClosed_le continuous_const (Complex.continuous_re.comp
      ((D.continuous.comp (hP.clm_apply continuous_const)).clm_apply continuous_const))
  have hopen : IsOpen S := by
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    let e := ContinuousLinearEquiv.ofBijective (P x)
      (LinearMap.ker_eq_bot.mpr (hb x).1) (LinearMap.range_eq_top.mpr (hb x).2)
    let ε := 1/(‖e.symm.toContinuousLinearMap‖+1)
    have hε : 0 < ε := by dsimp [ε]; positivity
    have hc : ∀ v, ε*‖v‖^2 ≤ realDualityForm D C (P x) v v :=
      realDualityForm_coercive_of_nonneg D C e (hs x) hx
    have hnear : ∀ᶠ y in 𝓝 x, ‖P y-P x‖ < ε := by
      have ht := hP.continuousAt.eventually (Metric.ball_mem_nhds (P x) hε)
      simpa only [Metric.mem_ball,dist_eq_norm] using ht
    apply Filter.mem_of_superset hnear
    intro y hy v
    have hd := abs_realDualityForm_le D C (P y-P x) v
    rw [realDualityForm_sub] at hd
    have hneg := (neg_le_abs (realDualityForm D C (P y) v v-
      realDualityForm D C (P x) v v)).trans hd
    have hsmall := mul_le_mul_of_nonneg_right hy.le (sq_nonneg ‖v‖)
    linarith [hc v]
  have he : S = univ := (show IsClopen S from ⟨hclosed,hopen⟩).eq_univ hstart
  intro x v
  have hx : x ∈ S := he ▸ mem_univ x
  exact hx v

end NLS
