import NLS.ComplexAnalysis.SmallQuadraticInverse

/-! # Real-preserving inverse charts for small quadratic maps

Uniqueness in the actual contraction ball forces equivariance. The
solution lies strictly inside the ball, so the analytic inverse can be
restricted to one open neighborhood preserving the fixed-point loci.
-/
noncomputable section
open Set Metric Filter Topology
namespace NLS.ComplexAnalysis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem small_quadratic_solution_unique (B : E →L[ℂ] E →L[ℂ] E)
    {C R : ℝ} (hC : 0 ≤ C)
    (hB : ∀ u v, ‖B u v‖ ≤ C*‖u‖*‖v‖) (hsmall : C*R ≤ 1/4)
    {x z y : E} (hx : ‖x‖ ≤ R) (hz : ‖z‖ ≤ R)
    (hxy : x+B x x = y) (hzy : z+B z z = y) : x = z := by
  have he : B x x-B z z = -(x-z) := by
    rw [show B x x = y-x by rw [← hxy];abel,
      show B z z = y-z by rw [← hzy];abel]
    abel
  have hb := quadratic_difference_bound B hC hB hx hz
  rw [he,norm_neg] at hb
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  have hd := norm_nonneg (x-z)
  have hs := mul_le_mul_of_nonneg_right hsmall hd
  linarith

theorem norm_small_quadratic_solution_le_three_quarters
    (B : E →L[ℂ] E →L[ℂ] E) {C R : ℝ} (hC : 0 ≤ C) (hR : 0 < R)
    (hB : ∀ u v, ‖B u v‖ ≤ C*‖u‖*‖v‖) (hsmall : C*R ≤ 1/4)
    {x y : E} (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R/2) (hxy : x+B x x = y) :
    ‖x‖ ≤ 3*R/4 := by
  have hquad : ‖B x x‖ ≤ C*R*R := (hB x x).trans (by gcongr)
  have ht := norm_sub_le y (B x x)
  rw [show y-B x x = x by rw [← hxy];abel] at ht
  have hs := mul_le_mul_of_nonneg_right hsmall hR.le
  linarith

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace E]

/-- The target normalization and the quadratic map commute with the
given norm-preserving symmetry. The constructed inverse preserves its
fixed points on a genuine common open source neighborhood. -/
theorem exists_equivariant_analytic_right_inverse_of_small_quadratic
    (L : F →L[ℂ] E) (hL : Function.Injective L) (f : E → F)
    (B : E →L[ℂ] E →L[ℂ] E) (hf : ∀ x, L (f x) = x+B x x)
    {C R : ℝ} (hC : 0 ≤ C) (hR : 0 < R)
    (hB : ∀ u v, ‖B u v‖ ≤ C*‖u‖*‖v‖) (hsmall : C*R ≤ 1/4)
    (sigma : E → E) (tau : F → F)
    (hnorm : ∀ x, ‖sigma x‖ = ‖x‖)
    (hquad : ∀ x, sigma (x+B x x) = sigma x+B (sigma x) (sigma x))
    (hlinear : ∀ r, sigma (L r) = L (tau r))
    (q : F) (hq : ‖L q‖ ≤ R/2) (hqreal : tau q = q) :
    ∃ x : E, ‖x‖ ≤ 3*R/4 ∧ f x = q ∧ sigma x = x ∧
      ∃ U : Set F, IsOpen U ∧ q ∈ U ∧ ∃ s : F → E,
        AnalyticOnNhd ℂ s U ∧ s q = x ∧
        (∀ r ∈ U, f (s r) = r) ∧
        ∀ r ∈ U, tau r = r → sigma (s r) = s r := by
  obtain ⟨x,hx,hfx,U0,hU0,hqU0,s,hs,hsq,hsolve⟩ :=
    exists_analytic_right_inverse_of_small_quadratic L hL f B hf hC hR hB hsmall q hq
  have hxy : x+B x x = L q := by rw [← hf,hfx]
  have hxstrict := norm_small_quadratic_solution_le_three_quarters B hC hR hB hsmall hx hq hxy
  have hxreal : sigma x = x := small_quadratic_solution_unique B hC hB hsmall
    (by rw [hnorm];exact hx) hx (by rw [← hquad,hxy,hlinear,hqreal]) hxy
  have hn : ‖s q‖ < R := by rw [hsq];linarith
  obtain ⟨W,hWsub,hW,hqW⟩ := _root_.mem_nhds_iff.mp ((hs q hqU0).continuousAt.norm.eventually (gt_mem_nhds hn))
  refine ⟨x,hxstrict,hfx,hxreal,U0 ∩ W,hU0.inter hW,⟨hqU0,hqW⟩,s,hs.mono inter_subset_left,hsq,
    fun r hr => hsolve r hr.1,?_⟩
  intro r hr hrreal
  have hsr : ‖s r‖ ≤ R := (hWsub hr.2).le
  have he : s r+B (s r) (s r) = L r := by rw [← hf,hsolve r hr.1]
  exact small_quadratic_solution_unique B hC hB hsmall (by rw [hnorm];exact hsr) hsr
    (by rw [← hquad,he,hlinear,hrreal]) he

end NLS.ComplexAnalysis
