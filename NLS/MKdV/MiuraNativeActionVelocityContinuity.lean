import NLS.MKdV.MiuraNativeActionFlowAllTimes
import NLS.ComplexAnalysis.InverseCoordinateStationarity

/-! # The actual native physical action vector has local holomorphic extensions

The analytic Cartesian inverse differentiates the actual complete action
flow, so the resulting chart vector represents the original velocity.
In particular the physical action vector is continuous in each native
Sobolev norm, including at closed actions.
-/
noncomputable section
open Set Metric Complex Filter Topology NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV
namespace MiuraNativeCartesianChart
variable {s : ℕ} {a : MiuraRealSobolevSource s}

def actionVelocity (C : MiuraNativeCartesianChart s a) (j : ℕ) (b : ScalarSobolev s) : ScalarSobolev s :=
  fderiv ℂ C.inverse (miuraSobolevNormalizedCartesianMap s b)
    (miuraCartesianActionVector j (miuraSobolevNormalizedCartesianMap s b))

theorem actionVelocity_analyticAt (C : MiuraNativeCartesianChart s a) (j : ℕ) :
    AnalyticAt ℂ (C.actionVelocity j) a.val :=
  (analyticAt_fderiv_apply_clm (C.inverse_analytic _ (mem_ball_self C.radius_pos))
    (miuraCartesianActionVector j)).comp (analyticAt_miuraSobolevNormalizedCartesianMap s a.val a.property)

theorem actionVelocity_eq_native (C : MiuraNativeCartesianChart s a) (hs : 1 ≤ s)
    (j : ℕ) (hj : 1 ≤ j) (b : MiuraRealSobolevSource s) (hb : b.val ∈ C.source)
    (hz : miuraSobolevNormalizedCartesianMap s b.val ∈ ball (miuraSobolevNormalizedCartesianMap s a.val) C.radius) :
    C.actionVelocity j b.val = miuraNativeActionVelocity s b j := by
  let z := miuraSobolevNormalizedCartesianMap s b.val
  have hc : HasFDerivAt C.inverse ((fderiv ℂ C.inverse z).restrictScalars ℝ)
      (miuraCartesianRotation j 0 z) := by
    rw [miuraCartesianRotation_zero]
    exact (C.inverse_analytic z hz).differentiableAt.hasFDerivAt.restrictScalars ℝ
  have hd := hc.comp_hasDerivAt 0 (hasDerivAt_miuraCartesianRotation_zero j z)
  have he : (fun t => C.inverse (miuraCartesianRotation j t z)) =ᶠ[𝓝 (0:ℝ)]
      miuraActionFlow s b.val (fun k => b.property k) j := by
    have hnear : ∀ᶠ t in 𝓝 (0:ℝ),miuraActionFlow s b.val (fun k => b.property k) j t ∈ C.source := by
      have h0 := miuraActionFlow_zero s b.val (fun k => b.property k) j
      apply (continuous_miuraActionFlow s b.val (fun k => b.property k) j).continuousAt.tendsto.eventually
      rw [h0]
      exact C.source_open.mem_nhds hb
    filter_upwards [hnear] with t ht
    rw [← miuraSobolevNormalizedCartesianMap_actionFlow s b.val (fun k => b.property k) j hj t]
    exact C.left_inverse _ ht
  exact (hd.congr_of_eventuallyEq (Filter.EventuallyEq.symm he)).unique (hasDerivAt_miuraActionFlow_native_zero s hs b j hj)

end MiuraNativeCartesianChart

theorem exists_miuraNativeActionVelocity_analytic_extension (s : ℕ) (hs : 1 ≤ s)
    (j : ℕ) (hj : 1 ≤ j) (a : MiuraRealSobolevSource s) :
    ∃ V : ScalarSobolev s → ScalarSobolev s,AnalyticAt ℂ V a.val ∧
      ∀ᶠ b : MiuraRealSobolevSource s in 𝓝 a,V b.val = miuraNativeActionVelocity s b j := by
  obtain ⟨C⟩ := nonempty_miuraNativeCartesianChart s hs a
  have hM : ContinuousAt (fun b : MiuraRealSobolevSource s => miuraSobolevNormalizedCartesianMap s b.val) a :=
    (analyticAt_miuraSobolevNormalizedCartesianMap s a.val a.property).continuousAt.comp continuous_subtype_val.continuousAt
  have hsource : ∀ᶠ b : MiuraRealSobolevSource s in 𝓝 a,b.val ∈ C.source :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds (C.source_open.mem_nhds C.source_base)
  have hball : ∀ᶠ b : MiuraRealSobolevSource s in 𝓝 a,
      miuraSobolevNormalizedCartesianMap s b.val ∈ ball (miuraSobolevNormalizedCartesianMap s a.val) C.radius :=
    hM.preimage_mem_nhds (isOpen_ball.mem_nhds (mem_ball_self C.radius_pos))
  refine ⟨C.actionVelocity j,C.actionVelocity_analyticAt j,?_⟩
  filter_upwards [hsource,hball] with b hb hz
  exact C.actionVelocity_eq_native hs j hj b hb hz

theorem continuous_miuraNativeActionVelocity (s : ℕ) (hs : 1 ≤ s) (j : ℕ) (hj : 1 ≤ j) :
    Continuous (fun a : MiuraRealSobolevSource s => miuraNativeActionVelocity s a j) := by
  apply continuous_iff_continuousAt.mpr
  intro a
  obtain ⟨V,hV,he⟩ := exists_miuraNativeActionVelocity_analytic_extension s hs j hj a
  exact (hV.continuousAt.comp continuous_subtype_val.continuousAt).congr_of_eventuallyEq (Filter.EventuallyEq.symm he)

end NLS.MKdV
