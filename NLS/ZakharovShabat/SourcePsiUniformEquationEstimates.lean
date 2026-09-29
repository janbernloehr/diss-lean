import NLS.ZakharovShabat.SourcePsiUniformEquationTube

/-!
# Uniform estimates for the glued psi equations

The common bounded analytic tube controls the joint derivative, its
root restriction, and the equation residual under source perturbation.
All constants depend only on the tube radius and its equation norm
bound, so they are independent of the deleted index.
-/

noncomputable section
open Set Filter Topology Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat.SourcePsiUniformEquationTube
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
  {φ : realTypeSourceLocus p}

theorem differentiableAt (D : SourcePsiUniformEquationTube hp hp1 φ) (n : ℤ)
    (q : DeletedCoeff p n × CoeffPair p)
    (hq : q ∈ ball (sourcePsiGapRoot hp hp1 n φ,φ.val) (4*D.radius)) :
    DifferentiableAt ℂ (D.equation n) q := (D.analytic n q hq).differentiableAt

theorem root_fderiv_eq (D : SourcePsiUniformEquationTube hp hp1 φ) (n : ℤ)
    (q : DeletedCoeff p n × CoeffPair p)
    (hq : q ∈ ball (sourcePsiGapRoot hp hp1 n φ,φ.val) (4*D.radius)) :
    fderiv ℂ (fun b => D.equation n (b,q.2)) q.1 =
      (fderiv ℂ (D.equation n) q).comp
        (ContinuousLinearMap.inl ℂ (DeletedCoeff p n) (CoeffPair p)) :=
  ((D.differentiableAt n q hq).hasFDerivAt.comp q.1
    (hasFDerivAt_prodMk_left q.1 q.2)).fderiv

theorem norm_fderiv_le (D : SourcePsiUniformEquationTube hp hp1 φ) (n : ℤ)
    (q : DeletedCoeff p n × CoeffPair p)
    (hq : q ∈ ball (sourcePsiGapRoot hp hp1 n φ,φ.val) D.radius) :
    ‖fderiv ℂ (D.equation n) q‖ ≤ 2*D.normBound/D.radius := by
  have houter : 3*D.radius+D.radius = 4*D.radius := by ring
  apply NLS.ComplexAnalysis.norm_fderiv_le_of_ball_bound (D.equation n)
    (sourcePsiGapRoot hp hp1 n φ,φ.val) q (3*D.radius) D.radius D.normBound D.radius_pos
  · simpa only [houter] using (D.analytic n).differentiableOn
  · simpa only [houter] using D.norm_le n
  · exact (ball_subset_ball (by linarith [D.radius_pos] : D.radius ≤ 3*D.radius)) hq

theorem norm_fderiv_sub_le (D : SourcePsiUniformEquationTube hp hp1 φ) (n : ℤ)
    (q u : DeletedCoeff p n × CoeffPair p)
    (hq : q ∈ ball (sourcePsiGapRoot hp hp1 n φ,φ.val) D.radius)
    (hu : u ∈ ball (sourcePsiGapRoot hp hp1 n φ,φ.val) D.radius) :
    ‖fderiv ℂ (D.equation n) q-fderiv ℂ (D.equation n) u‖ ≤
      (4*D.normBound/D.radius^2)*‖q-u‖ :=
  NLS.ComplexAnalysis.norm_fderiv_sub_le_of_holomorphic_ball_bound (D.equation n)
    (sourcePsiGapRoot hp hp1 n φ,φ.val) D.radius D.normBound D.radius_pos
    (D.analytic n).differentiableOn (D.norm_le n) hu hq

theorem norm_root_fderiv_sub_le (D : SourcePsiUniformEquationTube hp hp1 φ) (n : ℤ)
    (q u : DeletedCoeff p n × CoeffPair p)
    (hq : q ∈ ball (sourcePsiGapRoot hp hp1 n φ,φ.val) D.radius)
    (hu : u ∈ ball (sourcePsiGapRoot hp hp1 n φ,φ.val) D.radius) :
    ‖fderiv ℂ (fun b => D.equation n (b,q.2)) q.1-
        fderiv ℂ (fun b => D.equation n (b,u.2)) u.1‖ ≤
      (4*D.normBound/D.radius^2)*‖q-u‖ := by
  have hball : ball (sourcePsiGapRoot hp hp1 n φ,φ.val) D.radius ⊆
      ball (sourcePsiGapRoot hp hp1 n φ,φ.val) (4*D.radius) :=
    ball_subset_ball (by linarith [D.radius_pos])
  rw [D.root_fderiv_eq n q (hball hq),D.root_fderiv_eq n u (hball hu),
    ← ContinuousLinearMap.sub_comp]
  calc
    _ ≤ ‖fderiv ℂ (D.equation n) q-fderiv ℂ (D.equation n) u‖ *
        ‖ContinuousLinearMap.inl ℂ (DeletedCoeff p n) (CoeffPair p)‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖fderiv ℂ (D.equation n) q-fderiv ℂ (D.equation n) u‖ := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left
        (ContinuousLinearMap.norm_inl_le_one ℂ (DeletedCoeff p n) (CoeffPair p))
        (norm_nonneg (fderiv ℂ (D.equation n) q-fderiv ℂ (D.equation n) u))
    _ ≤ (4*D.normBound/D.radius^2)*‖q-u‖ := D.norm_fderiv_sub_le n q u hq hu

/-- Source perturbations have an actual equation residual bounded
linearly in the source distance, with one constant for every index. -/
theorem norm_equation_at_source_le (D : SourcePsiUniformEquationTube hp hp1 φ) (n : ℤ)
    (ψ : CoeffPair p) (hψ : ψ ∈ ball φ.val D.radius) :
    ‖D.equation n (sourcePsiGapRoot hp hp1 n φ,ψ)‖ ≤
      (2*D.normBound/D.radius)*‖ψ-φ.val‖ := by
  let a := sourcePsiGapRoot hp hp1 n φ
  have hball : ball (a,φ.val) D.radius ⊆ ball (a,φ.val) (4*D.radius) :=
    ball_subset_ball (by linarith [D.radius_pos])
  have hq : (a,ψ) ∈ ball (a,φ.val) D.radius := by
    simpa only [mem_ball,dist_prod_same_left] using hψ
  have h := (convex_ball (a,φ.val) D.radius).norm_image_sub_le_of_norm_fderiv_le
    (fun q hq => D.differentiableAt n q (hball hq))
    (fun q hq => D.norm_fderiv_le n q hq) (mem_ball_self D.radius_pos) hq
  have hd : ‖(a,ψ)-(a,φ.val)‖ = ‖ψ-φ.val‖ := by
    change max ‖a-a‖ ‖ψ-φ.val‖ = ‖ψ-φ.val‖
    rw [sub_self,norm_zero,max_eq_right (norm_nonneg _)]
  rw [D.zero n,sub_zero,hd] at h
  exact h

theorem bijective_root_fderiv (D : SourcePsiUniformEquationTube hp hp1 φ) (n : ℤ)
    (q : DeletedCoeff p n × CoeffPair p)
    (hq : q ∈ ball (sourcePsiGapRoot hp hp1 n φ,φ.val) (4*D.radius)) :
    Function.Bijective (fderiv ℂ (fun b => D.equation n (b,q.2)) q.1) := by
  obtain ⟨S,hQS,hSQ,hS⟩ := D.inverse n q hq
  let Q := fderiv ℂ (fun b => D.equation n (b,q.2)) q.1
  have hleft : Function.LeftInverse S Q := by
    intro x
    have h := congrArg (fun T : DeletedCoeff p n →L[ℂ] DeletedCoeff p n => T x) hSQ
    simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply] using h
  have hright : Function.RightInverse S Q := by
    intro x
    have h := congrArg (fun T : DeletedCoeff p n →L[ℂ] DeletedCoeff p n => T x) hQS
    simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply] using h
  exact ⟨hleft.injective,hright.surjective⟩

end NLS.ZakharovShabat.SourcePsiUniformEquationTube
