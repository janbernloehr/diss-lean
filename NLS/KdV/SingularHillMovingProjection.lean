import NLS.KdV.SingularHillSpectralProjection

/-! # Norm-continuous spectral projections on moving physical circles

Potential, center and radius all vary continuously. The angular integral
is taken in the actual bounded-operator norm on the original H^-1 base.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

theorem continuousOn_singularHillBaseResolvent_joint :
    ContinuousOn (fun p : FourierLebesgueSpace (2 : ℝ) (-1) 2 × ℂ => singularHillBaseResolvent p.1 p.2)
      {p | p.2 ∈ singularHillResolventSet p.1} := by
  intro p hp
  exact (analyticAt_singularHillBaseResolvent_joint p hp).continuousAt.continuousWithinAt

theorem continuous_moving_circleMap
    {T : Type*} [TopologicalSpace T] (c : T → ℂ) (hc : Continuous c)
    (r : T → ℝ) (hr : Continuous r) :
    Continuous (fun p : T × ℝ => circleMap (c p.1) (r p.1) p.2) := by
  simp only [circleMap]
  fun_prop

theorem continuous_moving_circleMap_derivative
    {T : Type*} [TopologicalSpace T] (c : T → ℂ) (r : T → ℝ) (hr : Continuous r) :
    Continuous (fun p : T × ℝ => deriv (circleMap (c p.1) (r p.1)) p.2) := by
  simp only [deriv_circleMap,circleMap]
  fun_prop

theorem continuous_singularHillBaseResolvent_moving_circle
    {T : Type*} [TopologicalSpace T]
    (Q : T → FourierLebesgueSpace (2 : ℝ) (-1) 2) (hQ : Continuous Q)
    (c : T → ℂ) (hc : Continuous c) (r : T → ℝ) (hr : Continuous r)
    (hr0 : ∀ t, 0 ≤ r t)
    (hcircle : ∀ t, sphere (c t) (r t) ⊆ singularHillResolventSet (Q t)) :
    Continuous (fun p : T × ℝ => -singularHillBaseResolvent (Q p.1)
      (circleMap (c p.1) (r p.1) p.2)) := by
  have hmap := (hQ.comp continuous_fst).prodMk (continuous_moving_circleMap c hc r hr)
  have hcont := continuousOn_singularHillBaseResolvent_joint.comp_continuous hmap
    (fun p => hcircle p.1 (circleMap_mem_sphere (c p.1) (hr0 p.1) p.2))
  simpa only [] using! hcont.neg

theorem continuous_singularHillRieszProjection_moving
    {T : Type*} [TopologicalSpace T]
    (Q : T → FourierLebesgueSpace (2 : ℝ) (-1) 2) (hQ : Continuous Q)
    (c : T → ℂ) (hc : Continuous c) (r : T → ℝ) (hr : Continuous r)
    (hr0 : ∀ t, 0 ≤ r t)
    (hcircle : ∀ t, sphere (c t) (r t) ⊆ singularHillResolventSet (Q t)) :
    Continuous (fun t => singularHillRieszProjection (Q t) (c t) (r t)) := by
  have hB := continuous_singularHillBaseResolvent_moving_circle Q hQ c hc r hr hr0 hcircle
  have hd := continuous_moving_circleMap_derivative c r hr
  have hI := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ := MeasureTheory.volume)
    (f := fun (t : T) (θ : ℝ) => deriv (circleMap (c t) (r t)) θ •
      -singularHillBaseResolvent (Q t) (circleMap (c t) (r t) θ))
    (hd.smul hB) 0 (2*Real.pi)
  have hfinal := hI.const_smul ((2*Real.pi*I : ℂ)⁻¹)
  simpa only [singularHillRieszProjection,NLS.CircleIntegral.normalized,circleIntegral] using! hfinal

end NLS.KdV
