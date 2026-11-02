import NLS.ComplexAnalysis.AnalyticOpenInverse
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.SpecificLimits.Normed

/-! # Inverting a small quadratic perturbation on a Banach ball

A bilinear estimate on the ball gives both a contraction and an
invertible derivative at the resulting solution. No compactness or
finite-dimensional hypothesis is used.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Filter Topology
open scoped NNReal
namespace NLS.ComplexAnalysis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem quadratic_difference_bound (B : E →L[ℂ] E →L[ℂ] E)
    {C R : ℝ} (hC : 0 ≤ C)
    (hB : ∀ u v, ‖B u v‖ ≤ C*‖u‖*‖v‖)
    {u v : E} (hu : ‖u‖ ≤ R) (hv : ‖v‖ ≤ R) :
    ‖B u u-B v v‖ ≤ 2*C*R*‖u-v‖ := by
  have he : B u u-B v v = B (u-v) u+B v (u-v) := by
    simp only [map_sub,_root_.sub_apply]
    abel
  rw [he]
  calc
    _ ≤ ‖B (u-v) u‖+‖B v (u-v)‖ := norm_add_le _ _
    _ ≤ C*‖u-v‖*‖u‖+C*‖v‖*‖u-v‖ := add_le_add (hB _ _) (hB _ _)
    _ ≤ 2*C*R*‖u-v‖ := by
      have h₁ := mul_le_mul_of_nonneg_left hu (mul_nonneg hC (norm_nonneg (u-v)))
      have h₂ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hv hC) (norm_nonneg (u-v))
      nlinarith

/-- A solution in the complete closed ball, for a quadratic term with C R ≤ 1/4. -/
theorem exists_small_quadratic_solution (B : E →L[ℂ] E →L[ℂ] E)
    {C R : ℝ} (hC : 0 ≤ C) (hR : 0 < R)
    (hB : ∀ u v, ‖B u v‖ ≤ C*‖u‖*‖v‖) (hsmall : C*R ≤ 1/4)
    (y : E) (hy : ‖y‖ ≤ R/2) :
    ∃ x : E, ‖x‖ ≤ R ∧ x+B x x = y := by
  let Φ : E → E := fun x => y-B x x
  have hmap : MapsTo Φ (closedBall 0 R) (closedBall 0 R) := by
    intro x hx
    have hxR : ‖x‖ ≤ R := by simpa only [mem_closedBall,dist_zero_right] using hx
    have hxx : ‖B x x‖ ≤ C*R*R := (hB x x).trans
      (mul_le_mul (mul_le_mul_of_nonneg_left hxR hC) hxR (norm_nonneg x) (mul_nonneg hC hR.le))
    rw [mem_closedBall,dist_zero_right]
    exact (norm_sub_le _ _).trans (by
      have hprod := mul_le_mul_of_nonneg_right hsmall hR.le
      linarith)
  let F : closedBall (0 : E) R → closedBall (0 : E) R := fun x => ⟨Φ x,hmap x.property⟩
  have hc : ContractingWith (1/2 : ℝ≥0) F := by
    refine ⟨by norm_num,LipschitzWith.of_dist_le_mul ?_⟩
    intro u v
    simp only [Subtype.dist_eq,dist_eq_norm,NNReal.coe_div,NNReal.coe_one,NNReal.coe_ofNat]
    change ‖Φ u-Φ v‖ ≤ (1/2 : ℝ)*‖(u : E)-v‖
    have hu : ‖(u : E)‖ ≤ R := by simpa only [mem_closedBall,dist_zero_right] using u.property
    have hv : ‖(v : E)‖ ≤ R := by simpa only [mem_closedBall,dist_zero_right] using v.property
    rw [show Φ u-Φ v = -(B u u-B v v) by dsimp [Φ]; abel,norm_neg]
    exact (quadratic_difference_bound B hC hB hu hv).trans (by
      have hn := norm_nonneg ((u : E)-v)
      nlinarith [mul_le_mul_of_nonneg_right hsmall hn])
  let : CompleteSpace (closedBall (0 : E) R) := isClosed_closedBall.completeSpace_coe
  let : Nonempty (closedBall (0 : E) R) := ⟨⟨0,mem_closedBall_self hR.le⟩⟩
  let x := hc.fixedPoint F
  have hfix : Φ x = (x : E) := congrArg Subtype.val hc.fixedPoint_isFixedPt
  refine ⟨x,by simpa only [mem_closedBall,dist_zero_right] using x.property,?_⟩
  dsimp [Φ] at hfix
  exact (eq_sub_iff_add_eq).mp hfix.symm

/-- The derivative of x ↦ x+B(x,x) is a unit under the same smallness condition. -/
theorem isUnit_fderiv_small_quadratic (B : E →L[ℂ] E →L[ℂ] E)
    {C : ℝ} (hC : 0 ≤ C) (hB : ∀ u v, ‖B u v‖ ≤ C*‖u‖*‖v‖)
    (x : E) (hsmall : 2*C*‖x‖ < 1) :
    IsUnit (fderiv ℂ (fun z => z+B z z) x) := by
  let D : E →L[ℂ] E := B x+B.flip x
  have hnorm : ‖D‖ ≤ 2*C*‖x‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro z
    change ‖B x z+B z x‖ ≤ 2*C*‖x‖*‖z‖
    exact (norm_add_le _ _).trans ((add_le_add (hB x z) (hB z x)).trans (by ring_nf; rfl))
  have hquad : HasFDerivAt (fun z => B z z) D x := by
    have h := B.hasFDerivAt_of_bilinear (hasFDerivAt_id x) (hasFDerivAt_id x)
    have he : B.precompR E x (ContinuousLinearMap.id ℂ E) +
        B.precompL E (ContinuousLinearMap.id ℂ E) x = D := by
      ext z
      rfl
    rw [show id x = x from rfl,he] at h
    exact h
  have hder : HasFDerivAt (fun z => z+B z z) (1+D) x :=
    (hasFDerivAt_id x).add hquad
  rw [hder.fderiv]
  have hu := isUnit_one_sub_of_norm_lt_one (x := -D) (by simpa only [norm_neg] using hnorm.trans_lt hsmall)
  simpa only [sub_neg_eq_add] using hu

/-- Analytic inverse charts around a solution of the small quadratic equation. -/
theorem exists_small_quadratic_analytic_inverse (B : E →L[ℂ] E →L[ℂ] E)
    {C R : ℝ} (hC : 0 ≤ C) (hR : 0 < R)
    (hB : ∀ u v, ‖B u v‖ ≤ C*‖u‖*‖v‖) (hsmall : C*R ≤ 1/4)
    (y : E) (hy : ‖y‖ ≤ R/2) :
    ∃ x : E, ‖x‖ ≤ R ∧ x+B x x = y ∧
      ∃ W : Set E, IsOpen W ∧ y ∈ W ∧
        ∃ G : E → E, AnalyticOnNhd ℂ G W ∧ G y = x ∧
          ∀ z ∈ W, G z+B (G z) (G z) = z := by
  obtain ⟨x,hx,hxy⟩ := exists_small_quadratic_solution B hC hR hB hsmall y hy
  have hf : AnalyticOnNhd ℂ (fun z => z+B z z) univ := fun z _ =>
    analyticAt_id.add ((B.analyticAt_bilinear _).comp₂ analyticAt_id analyticAt_id)
  have hu := isUnit_fderiv_small_quadratic B hC hB x (by
    have h := mul_le_mul_of_nonneg_left hx (show 0 ≤ 2*C by positivity)
    nlinarith)
  obtain ⟨V,W,_,hW,hxV,hyW,_,_,_,G,_,hG,hleft,hright⟩ :=
    exists_analytic_inverse_open_sets isOpen_univ hf (mem_univ x) hu
  refine ⟨x,hx,hxy,W,hW,by simpa only [hxy] using hyW,G,hG,?_,?_⟩
  · simpa only [hxy] using hleft x hxV
  · intro z hz
    exact (hright z hz).2

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Transfer the chart through an injective linear normalization of its target. -/
theorem exists_analytic_right_inverse_of_small_quadratic
    (L : F →L[ℂ] E) (hL : Function.Injective L) (f : E → F)
    (B : E →L[ℂ] E →L[ℂ] E) (hf : ∀ x, L (f x) = x+B x x)
    {C R : ℝ} (hC : 0 ≤ C) (hR : 0 < R)
    (hB : ∀ u v, ‖B u v‖ ≤ C*‖u‖*‖v‖) (hsmall : C*R ≤ 1/4)
    (q : F) (hq : ‖L q‖ ≤ R/2) :
    ∃ x : E, ‖x‖ ≤ R ∧ f x = q ∧
      ∃ U : Set F, IsOpen U ∧ q ∈ U ∧ ∃ s : F → E,
        AnalyticOnNhd ℂ s U ∧ s q = x ∧ ∀ r ∈ U, f (s r) = r := by
  obtain ⟨x,hx,hxy,W,hW,hyW,G,hG,hGy,hright⟩ :=
    exists_small_quadratic_analytic_inverse B hC hR hB hsmall (L q) hq
  have hsolve : f x = q := hL (by rw [hf]; exact hxy)
  let U : Set F := L ⁻¹' W
  let s : F → E := fun r => G (L r)
  refine ⟨x,hx,hsolve,U,hW.preimage L.continuous,hyW,s,?_,hGy,?_⟩
  · intro r hr
    exact (hG _ hr).comp (L.analyticAt r)
  · intro r hr
    apply hL
    rw [hf]
    exact hright _ hr

end NLS.ComplexAnalysis
