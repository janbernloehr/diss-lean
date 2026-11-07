import NLS.KdV.HillProductDataVariation
import NLS.KdV.HillProductFixedPeriods

/-! Differentiation of actual fixed-circle Hill product periods in an
arbitrary full l2 direction. The contour and physical normalization are
literal; no coordinate-series interchange is assumed. -/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.KdV

theorem fderiv_hillEnergyProductPeriodIntegrand_data (n : ℕ+) (c : ℂ) (ψ : CoeffPair 2)
    (z : ℂ) (d h : lp (fun _ : ℕ+ => ℂ) 2) :
    fderiv ℂ (fun b => hillEnergyProductPeriodIntegrand n c ψ (z,b)) d h =
      (2*z*hillEnergyProductDataVariation n d h (z^2-c))/sourceCanonicalRoot (by norm_num) (by norm_num) ψ z := by
  have hp : HasFDerivAt (fun b : lp (fun _ : ℕ+ => ℂ) 2 => hillEnergySequenceProduct n (z^2-c,b))
      (fderiv ℂ (fun b => hillEnergySequenceProduct n (z^2-c,b)) d) d :=
    ((analyticAt_hillEnergySequenceProduct n (z^2-c,d)).comp
      (f := fun b : lp (fun _ : ℕ+ => ℂ) 2 => (z^2-c,b)) (analyticAt_const.prod analyticAt_id)).differentiableAt.hasFDerivAt
  have hd := hp.const_mul ((2*z)/sourceCanonicalRoot (by norm_num) (by norm_num) ψ z)
  have he : (fun b => hillEnergyProductPeriodIntegrand n c ψ (z,b)) =
      (fun b => ((2*z)/sourceCanonicalRoot (by norm_num) (by norm_num) ψ z)*hillEnergySequenceProduct n (z^2-c,b)) := by
    funext b
    unfold hillEnergyProductPeriodIntegrand
    ring
  rw [he,hd.fderiv]
  change ((2*z)/sourceCanonicalRoot (by norm_num) (by norm_num) ψ z)*
    (fderiv ℂ (fun b => hillEnergySequenceProduct n (z^2-c,b)) d h) = _
  rw [← hillEnergyProductDataVariation_eq_section]
  ring

theorem fderiv_hillEnergyProductFixedPeriod_data (n : ℕ+) (c : ℂ) (ψ : CoeffPair 2)
    (hreal : IsRealType (CoeffPair.toMax 2 ψ)) {k : ℤ}
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num) ψ k)
    (d h : lp (fun _ : ℕ+ => ℂ) 2) :
    fderiv ℂ (hillEnergyProductFixedPeriod n c ψ D) d h =
      (2*Real.pi:ℂ)⁻¹*(∮ z in C((D.center:ℂ),D.radius),
        (2*z*hillEnergyProductDataVariation n d h (z^2-c))/sourceCanonicalRoot (by norm_num) (by norm_num) ψ z) := by
  let F := hillEnergyProductPeriodIntegrand n c ψ
  let U := sourceCanonicalRootDomain (by norm_num) (by norm_num) ψ ×ˢ (univ : Set (lp (fun _ : ℕ+ => ℂ) 2))
  have hU : IsOpen U := (isOpen_sourceCanonicalRootDomain_of_realType (by norm_num) (by norm_num) ψ hreal).prod isOpen_univ
  have hF : AnalyticOnNhd ℂ F U := analyticOnNhd_hillEnergyProductPeriodIntegrand n c ψ
  obtain ⟨V,hV,hdV,M,_,hb⟩ := exists_uniform_joint_fderiv_bound_on_circle F U hU hF (D.center:ℂ) D.radius d
    (fun z hz => ⟨D.sphere_subset_rootDomain hz,mem_univ d⟩)
  have hdom (b : lp (fun _ : ℕ+ => ℂ) 2) (hbV : b ∈ V) (θ : ℝ) :
      (circleMap (D.center:ℂ) D.radius θ,b) ∈ U :=
    (hb _ (circleMap_mem_sphere _ D.radius_pos.le θ) b hbV).1
  have hbound (b : lp (fun _ : ℕ+ => ℂ) 2) (hbV : b ∈ V) (θ : ℝ) :
      ‖fderiv ℂ F (circleMap (D.center:ℂ) D.radius θ,b)‖ ≤ M :=
    (hb _ (circleMap_mem_sphere _ D.radius_pos.le θ) b hbV).2
  have he := fderiv_circleIntegral_apply_of_jointAnalytic F U hU hF (D.center:ℂ) D.radius D.radius_pos.le
    V hV d hdV M hdom hbound h
  have hI := analyticOnNhd_circleIntegral_of_jointAnalytic F hU hF (D.center:ℂ) D.radius D.radius_pos.le
    isOpen_univ (fun b _ z hz => ⟨D.sphere_subset_rootDomain hz,mem_univ b⟩)
  have hd := (hI d (mem_univ _)).differentiableAt.hasFDerivAt.const_mul (2*Real.pi:ℂ)⁻¹
  change (fderiv ℂ (fun b : lp (fun _ : ℕ+ => ℂ) 2 => (2*Real.pi:ℂ)⁻¹*
    (∮ z in C((D.center:ℂ),D.radius), F (z,b))) d) h = _
  rw [hd.fderiv]
  change (2*Real.pi:ℂ)⁻¹*(fderiv ℂ (fun b => ∮ z in C((D.center:ℂ),D.radius), F (z,b)) d h) = _
  rw [he]
  congr 1
  apply circleIntegral.integral_congr D.radius_pos.le
  intro z _
  exact fderiv_hillEnergyProductPeriodIntegrand_data n c ψ z d h

end NLS.KdV
