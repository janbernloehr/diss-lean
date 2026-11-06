import NLS.ComplexAnalysis.JointCircleCauchyTransform
import NLS.ComplexAnalysis.CauchyFiniteHoles

/-! Joint analyticity of a removable divided difference in a scalar
variable and arbitrary Banach parameters, reconstructed on a fixed circle. -/
noncomputable section
open Set Metric Complex Filter Topology
namespace NLS.ComplexAnalysis
variable {A : Type} [NormedAddCommGroup A] [NormedSpace ℂ A]

def jointDSlopeZero (F : ℂ × A → ℂ) (p : ℂ × A) : ℂ :=
  dslope (fun w => F (w,p.2)) 0 p.1

theorem analyticOnNhd_jointDSlopeZero (F : ℂ × A → ℂ) (V : Set A) (hV : IsOpen V)
    (hF : AnalyticOnNhd ℂ F (univ ×ˢ V)) :
    AnalyticOnNhd ℂ (jointDSlopeZero F) (univ ×ˢ V) := by
  intro p hp
  let R : ℝ := ‖p.1‖+1
  have hR : 0 < R := by dsimp [R]; positivity
  let G : ℂ × A → ℂ := fun t => (F t-F (0,t.2))/t.1
  have hG : AnalyticOnNhd ℂ G (sphere 0 R ×ˢ V) := by
    intro t ht
    have hzero : AnalyticAt ℂ (fun x : ℂ × A => F (0,x.2)) t :=
      (hF (0,t.2) ⟨mem_univ _,ht.2⟩).comp
        (f := fun x : ℂ × A => (0,x.2)) (analyticAt_const.prod analyticAt_snd)
    have hn : t.1 ≠ 0 := by
      have he : ‖t.1‖ = R := by simpa only [mem_sphere,dist_zero_right] using ht.1
      exact norm_pos_iff.mp (he.symm ▸ hR)
    exact ((hF t ⟨mem_univ _,ht.2⟩).sub hzero).div analyticAt_fst hn
  have ha := analyticOnNhd_jointCircleCauchyTransform G 0 R hR.le V hV hG
  have hpeq : ∀ t ∈ ball (0:ℂ) R ×ˢ V,
      jointCircleCauchyTransform G 0 R t = jointDSlopeZero F t := by
    intro t ht
    have hf : AnalyticOnNhd ℂ (fun w => F (w,t.2)) univ := by
      intro w _
      exact (hF (w,t.2) ⟨mem_univ _,ht.2⟩).comp
        (f := fun z : ℂ => (z,t.2)) (analyticAt_id.prod analyticAt_const)
    have hd := analyticOnNhd_dslope_of_analytic _ univ 0 hf (mem_univ _)
    apply jointCircleCauchyTransform_eq_filling G 0 R hR t.2
      (dslope (fun w => F (w,t.2)) 0) (hd.mono (subset_univ _)) _ t.1 ht.1
    intro w hw
    have hn : w ≠ 0 := by
      have he : ‖w‖ = R := by simpa only [mem_sphere,dist_zero_right] using hw
      exact norm_pos_iff.mp (he.symm ▸ hR)
    simp only [G,dslope_of_ne _ hn,slope_def_field,sub_zero]
  have hpball : p ∈ ball (0:ℂ) R ×ˢ V := by
    refine ⟨?_,hp.2⟩
    simp only [mem_ball,dist_zero_right]
    dsimp [R]
    linarith
  have hpc : p ∈ (sphere (0:ℂ) R)ᶜ ×ˢ V :=
    ⟨fun h => sphere_disjoint_ball.le_bot ⟨h,hpball.1⟩,hp.2⟩
  apply (ha p hpc).congr
  filter_upwards [(isOpen_ball.prod hV).mem_nhds hpball] with t ht
  exact hpeq t ht

end NLS.ComplexAnalysis
