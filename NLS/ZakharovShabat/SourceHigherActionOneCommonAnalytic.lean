import NLS.ZakharovShabat.SourceHigherActionOneUniformCircle
import NLS.ZakharovShabat.SourceDistantNormalizedActionCircleIntegrandAnalytic

/-! The actual filled first higher-action quotient is analytic on
ONE complex source neighborhood BEFORE ALL sufficiently high signed
indices. Its common-circle realization includes complex closed gaps. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

private theorem differentiable_circle_quotient
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (c : ℂ) (R : ℝ) (hR : 0 < R)
    (ψ : CoeffPair p)
    (hcircle : ∀ z ∈ sphere c R, AnalyticAt ℂ (sourceHigherActionOneKernelJoint hp hp1 n) (z,ψ)) :
    DifferentiableAt ℂ (sourceHigherActionOneCircleQuotient hp hp1 n c R) ψ := by
  let F := sourceHigherActionOneKernelJoint hp hp1 n
  let D : Set (ℂ × CoeffPair p) := {t | AnalyticAt ℂ F t}
  have hD : IsOpen D := isOpen_analyticAt ℂ F
  have hF : AnalyticOnNhd ℂ F D := fun _ ht => ht
  obtain ⟨V,hV,hψV,M,_,hbound⟩ :=
    exists_uniform_joint_fderiv_bound_on_circle F D hD hF c R ψ hcircle
  have hd := differentiableAt_circleIntegral_of_jointAnalytic F D hD hF c R hR.le V hV ψ hψV M
    (fun b hb θ => (hbound (circleMap c R θ) (circleMap_mem_sphere c hR.le θ) b hb).1)
    (fun b hb θ => (hbound (circleMap c R θ) (circleMap_mem_sphere c hR.le θ) b hb).2)
  exact hd.const_mul (-(2*(Real.pi:ℂ))⁻¹)

theorem exists_local_sourceHigherActionOneNormalized_common_analytic
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hr : IsRealType (CoeffPair.toMax p φ)) :
    ∃ N : ℕ, ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧
      ∀ n : ℤ, N ≤ n.natAbs → AnalyticOnNhd ℂ (sourceHigherActionOneNormalized hp hp1 n) U := by
  obtain ⟨Kj,Vj,hVj,hφVj,hjoint⟩ :=
    exists_local_source_distantNormalizedActionCircleIntegrand_jointAnalytic hp hp1 φ hr
  obtain ⟨Kb,Vb,hVb,hφVb,hcrit⟩ :=
    exists_local_source_distantCanonicalCriticalPoints_analytic hp hp1 φ hr
  obtain ⟨Ke,Ve,hVe,hφVe,hagree⟩ :=
    exists_local_sourceHigherActionOneNormalized_uniform_circle hp hp1 φ hr
  let U := (Vj ∩ Vb) ∩ Ve
  have hU : IsOpen U := (hVj.inter hVb).inter hVe
  refine ⟨max (Kj+1) (max (Kb+1) Ke),U,hU,⟨⟨hφVj,hφVb⟩,hφVe⟩,?_⟩
  intro n hn
  have hj : Kj < n.natAbs := by omega
  have hb : Kb < n.natAbs := by omega
  have he : Ke ≤ n.natAbs := (le_trans (le_max_right _ _) (le_max_right _ _)).trans hn
  have hd : DifferentiableOn ℂ
      (sourceHigherActionOneCircleQuotient hp hp1 n ((Real.pi:ℂ)*n) (Real.pi/8)) U := by
    intro ψ hψ
    apply (differentiable_circle_quotient hp hp1 n _ _ (by positivity) ψ ?_).differentiableWithinAt
    intro z hz
    have hc := (hcrit ψ hψ.1.2 n hb).comp (analyticAt_snd (p := (z,ψ)))
    exact (analyticAt_fst.add hc).mul (hjoint ψ hψ.1.1 n hj z hz)
  intro ψ hψ
  have hlocal : sourceHigherActionOneCircleQuotient hp hp1 n ((Real.pi:ℂ)*n) (Real.pi/8)
      =ᶠ[𝓝 ψ] sourceHigherActionOneNormalized hp hp1 n := by
    filter_upwards [hU.mem_nhds hψ] with χ hχ
    exact (hagree χ hχ.2 n he).1.symm
  exact (analyticOnNhd_of_complexDifferentiableOn _ U hU hd ψ hψ).congr hlocal

end NLS.ZakharovShabat
