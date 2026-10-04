import NLS.ComplexAnalysis.ParametricConvexPrimitive

/-! # Propagation of parameter regularity along connected spectral slices

A family of spectral primitives of a jointly analytic function is jointly
analytic near an entire connected slice once it is jointly analytic at
one point of that slice. No initial parameter continuity is assumed:
local integration transfers the analytic anchor value across each disc.
-/
noncomputable section
open Set Metric Filter Topology Complex
namespace NLS.ComplexAnalysis
variable {A : Type} [NormedAddCommGroup A] [NormedSpace ℂ A]

/-- An analytic source-dependent anchor value determines joint
regularity of any spectral primitive on a convex product chart. -/
theorem analyticAt_primitive_of_analytic_anchor
    (F P : ℂ × A → ℂ) (Ω : Set ℂ) (V : Set A) (c z : ℂ) (a : A)
    (hΩ : IsOpen Ω) (hconv : Convex ℝ Ω) (hV : IsOpen V)
    (hc : c ∈ Ω) (hz : z ∈ Ω) (ha : a ∈ V)
    (hF : AnalyticOnNhd ℂ F (Ω ×ˢ V))
    (hP : ∀ b ∈ V, ∀ w ∈ Ω, HasDerivAt (fun u => P (u,b)) (F (w,b)) w)
    (hanchor : AnalyticAt ℂ (fun b => P (c,b)) a) : AnalyticAt ℂ P (z,a) := by
  have hR := analyticOnNhd_parametricConvexPrimitive F Ω V c hΩ hconv hV hc hF (z,a) ⟨hz,ha⟩
  have hC : AnalyticAt ℂ (fun t : ℂ × A => P (c,t.2)) (z,a) := by
    simpa only using! hanchor.comp (x := (z,a)) (f := fun t : ℂ × A => t.2) analyticAt_snd
  apply (hC.add hR).congr
  filter_upwards [(hΩ.prod hV).mem_nhds ⟨hz,ha⟩] with t ht
  have hFt : AnalyticOnNhd ℂ (fun w => F (w,t.2)) Ω := by
    intro w hw
    exact (hF (w,t.2) ⟨hw,ht.2⟩).comp (f := fun w : ℂ => (w,t.2))
      (analyticAt_id.prod analyticAt_const)
  have he := parametricConvexPrimitive_eq_sub_of_primitive F Ω c t.2 hconv hc hFt.continuousOn
    (fun w => P (w,t.2)) (hP t.2 ht.2) t.1 ht.1
  change P (c,t.2)+parametricConvexPrimitive F c (t.1,t.2) = P (t.1,t.2)
  rw [he]
  ring

/-- Joint analyticity propagates from one point through a connected
spectral slice of an open joint domain. -/
theorem analyticAt_primitive_on_connected_slice
    (F P : ℂ × A → ℂ) (D : Set (ℂ × A)) (hD : IsOpen D)
    (hF : AnalyticOnNhd ℂ F D)
    (hP : ∀ t ∈ D, HasDerivAt (fun w => P (w,t.2)) (F t) t.1)
    (a : A) (hconn : IsPreconnected {z : ℂ | (z,a) ∈ D})
    (c : ℂ) (hc : (c,a) ∈ D) (hPc : AnalyticAt ℂ P (c,a))
    (z : ℂ) (hz : (z,a) ∈ D) : AnalyticAt ℂ P (z,a) := by
  let S : Set ℂ := {w | AnalyticAt ℂ P (w,a)}
  have hS : IsOpen S := (isOpen_analyticAt ℂ P).preimage (continuous_id.prodMk continuous_const)
  apply hconn.subset_of_closure_inter_subset hS ⟨c,hc,hPc⟩ ?_ hz
  rintro w ⟨hwS,hwD⟩
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (hD.mem_nhds hwD)
  have hprod : ball w r ×ˢ ball a r ⊆ D := by
    rw [ball_prod_same]
    exact hball
  obtain ⟨v,hvS,hvw⟩ := Metric.mem_closure_iff.mp hwS r hr
  have hv : v ∈ ball w r := by simpa only [mem_ball,dist_comm] using hvw
  have hanchor : AnalyticAt ℂ (fun b : A => P (v,b)) a := hvS.comp (f := fun b : A => (v,b)) (analyticAt_const.prod analyticAt_id)
  exact analyticAt_primitive_of_analytic_anchor F P (ball w r) (ball a r) v w a
    isOpen_ball (convex_ball _ _) isOpen_ball hv (mem_ball_self hr) (mem_ball_self hr)
    (hF.mono hprod) (fun b hb u hu => hP (u,b) (hprod ⟨hu,hb⟩)) hanchor

end NLS.ComplexAnalysis
