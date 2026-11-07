import NLS.KdV.HillFullProductDataVariation
import NLS.KdV.HillAffineEnergyPeriods

/-! The arbitrary full-data derivative of the full literal physical
Hill period is the actual normalized contour integral of its entire
energy numerator variation. -/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.KdV

def hillEnergyFullPeriodIntegrand (c : ℂ) (ψ : CoeffPair 2)
    (t : ℂ × lp (fun _ : ℕ+ => ℂ) 2) : ℂ :=
  (2*t.1*hillEnergySequenceFullProduct (t.1^2-c,t.2))/sourceCanonicalRoot (by norm_num) (by norm_num) ψ t.1

theorem analyticOnNhd_hillEnergyFullPeriodIntegrand (c : ℂ) (ψ : CoeffPair 2) :
    AnalyticOnNhd ℂ (hillEnergyFullPeriodIntegrand c ψ)
      (sourceCanonicalRootDomain (by norm_num) (by norm_num) ψ ×ˢ univ) := by
  intro t ht
  have hp := (analyticAt_hillEnergySequenceFullProduct (t.1^2-c,t.2)).comp
    (f := fun s : ℂ × lp (fun _ : ℕ+ => ℂ) 2 => (s.1^2-c,s.2))
    (((analyticAt_fst.pow 2).sub analyticAt_const).prod analyticAt_snd)
  exact ((analyticAt_const.mul analyticAt_fst).mul hp).div
    ((sourceCanonicalRoot_analyticOnNhd (by norm_num) (by norm_num) ψ t.1 ht.1).comp
      (f := Prod.fst) analyticAt_fst)
    (sourceCanonicalRoot_ne_zero_off_gaps (by norm_num) (by norm_num) ψ t.1 ht.1)

theorem fderiv_hillEnergyFullPeriodIntegrand_data (c : ℂ) (ψ : CoeffPair 2)
    (z : ℂ) (d h : lp (fun _ : ℕ+ => ℂ) 2) :
    fderiv ℂ (fun b => hillEnergyFullPeriodIntegrand c ψ (z,b)) d h =
      (2*z*hillEnergyFullProductDataVariation d h (z^2-c))/sourceCanonicalRoot (by norm_num) (by norm_num) ψ z := by
  have hp : HasFDerivAt (fun b : lp (fun _ : ℕ+ => ℂ) 2 => hillEnergySequenceFullProduct (z^2-c,b))
      (fderiv ℂ (fun b => hillEnergySequenceFullProduct (z^2-c,b)) d) d :=
    ((analyticAt_hillEnergySequenceFullProduct (z^2-c,d)).comp
    (f := fun b : lp (fun _ : ℕ+ => ℂ) 2 => (z^2-c,b)) (analyticAt_const.prod analyticAt_id)).differentiableAt.hasFDerivAt
  have hd := hp.const_mul ((2*z)/sourceCanonicalRoot (by norm_num) (by norm_num) ψ z)
  have he : (fun b => hillEnergyFullPeriodIntegrand c ψ (z,b)) =
      (fun b => ((2*z)/sourceCanonicalRoot (by norm_num) (by norm_num) ψ z)*hillEnergySequenceFullProduct (z^2-c,b)) := by
    funext b
    unfold hillEnergyFullPeriodIntegrand
    ring
  rw [he,hd.fderiv]
  change ((2*z)/sourceCanonicalRoot (by norm_num) (by norm_num) ψ z)*
    (fderiv ℂ (fun b => hillEnergySequenceFullProduct (z^2-c,b)) d h) = _
  rw [← hillEnergyFullProductDataVariation_eq_section]
  ring

theorem fderiv_hillEnergyFullProductFixedPeriod_data (c : ℂ) (ψ : CoeffPair 2)
    (hreal : IsRealType (CoeffPair.toMax 2 ψ)) {k : ℤ}
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num) ψ k)
    (d h : lp (fun _ : ℕ+ => ℂ) 2) :
    fderiv ℂ (hillEnergyFullProductFixedPeriod c ψ D) d h =
      hillEnergyNumeratorPeriod c ψ D (hillEnergyFullProductDataVariation d h) := by
  let F := hillEnergyFullPeriodIntegrand c ψ
  let U := sourceCanonicalRootDomain (by norm_num) (by norm_num) ψ ×ˢ (univ : Set (lp (fun _ : ℕ+ => ℂ) 2))
  have hU : IsOpen U := (isOpen_sourceCanonicalRootDomain_of_realType (by norm_num) (by norm_num) ψ hreal).prod isOpen_univ
  have hF : AnalyticOnNhd ℂ F U := analyticOnNhd_hillEnergyFullPeriodIntegrand c ψ
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
  have hp : hillEnergyFullProductFixedPeriod c ψ D =
      fun b : lp (fun _ : ℕ+ => ℂ) 2 => (2*Real.pi:ℂ)⁻¹*(∮ z in C((D.center:ℂ),D.radius), F (z,b)) := by
    funext b
    exact hillEnergyFullProductFixedPeriod_eq_numeratorPeriod c ψ D b
  rw [hp,hd.fderiv]
  change (2*Real.pi:ℂ)⁻¹*(fderiv ℂ (fun b => ∮ z in C((D.center:ℂ),D.radius), F (z,b)) d h) = _
  rw [he]
  apply congrArg (fun w : ℂ => (2*Real.pi:ℂ)⁻¹*w)
  apply circleIntegral.integral_congr D.radius_pos.le
  intro z _
  exact fderiv_hillEnergyFullPeriodIntegrand_data c ψ z d h

end NLS.KdV
