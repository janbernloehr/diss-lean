import NLS.MKdV.L2QuasiHillSolution

/-! # Uniqueness of the actual rough quasi-Hill integral problem

The reverse fixed state map takes any continuous integral solution to
the existing physical AKNS Volterra problem. Uniqueness therefore needs
no smoothness of the scalar L2 profile and includes every energy.
-/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory Filter Topology
open NLS.LinearVolterra NLS.ZakharovShabat
namespace NLS.MKdV

theorem quasiHillCoefficient_affine_inverse_intertwine (u μ : ℂ) (v : ℂ × ℂ) :
    quasiHillFixedStateInv (quasiHillCoefficient u μ v) =
      classicalODECoefficient (quasiHillAffinePotential u μ) (quasiHillAffineFrequency μ)
        (quasiHillFixedStateInv v) := by
  have hinj : Function.Injective quasiHillFixedState := miuraStateMap_injective 0 1 one_ne_zero
  apply hinj
  rw [quasiHillFixedState_right_inv,← quasiHillCoefficient_affine_intertwine,
    quasiHillFixedState_right_inv]

theorem intervalIntegrable_quasiHillCoefficient (u : IntervalL2) (μ : ℂ)
    (w : Curve (ℂ × ℂ)) (t : Icc (0 : ℝ) 1) :
    IntervalIntegrable (fun s => quasiHillCoefficient (u s) μ (extend w s)) volume 0 t.val := by
  have hu₁ := intervalIntegrable_intervalL2_mul u (l2BoundedFirst w) t
  have hu₂ := intervalIntegrable_intervalL2_mul u (l2BoundedSecond w) t
  have hv₁ := ((continuous_extend w).fst.intervalIntegrable (μ := volume) 0 t.val).const_mul (-μ)
  have hv₂ := (continuous_extend w).snd.intervalIntegrable (μ := volume) 0 t.val
  exact ⟨(hu₁.add hv₂).1.prodMk (hv₁.sub hu₂).1,(hu₁.add hv₂).2.prodMk (hv₁.sub hu₂).2⟩

def quasiHillFixedInvCurve : Curve (ℂ × ℂ) →L[ℂ] Curve (ℂ × ℂ) :=
  ContinuousLinearMap.compLeftContinuous ℂ (Icc (0 : ℝ) 1) quasiHillFixedStateInv

/-- Every continuous representative-based integral solution is the
constructed solution; the initial data are position and quasi-derivative. -/
theorem l2QuasiHillSolution_unique_integral (u : IntervalL2) (μ : ℂ) (v : ℂ × ℂ)
    (w : Curve (ℂ × ℂ))
    (hw : ∀ t : Icc (0 : ℝ) 1, w t = v+∫ s in (0 : ℝ)..t.val,
      quasiHillCoefficient (u s) μ (extend w s)) : w = l2QuasiHillSolution u μ v := by
  let G := quasiHillFixedInvCurve w
  have hg : G = l2SolutionCurve (l2QuasiHillPotential u μ) (quasiHillAffineFrequency μ)
      (quasiHillFixedStateInv v) := by
    apply l2SolutionCurve_unique_integral
    intro t
    have he := congrArg quasiHillFixedStateInv (hw t)
    rw [map_add,← quasiHillFixedStateInv.intervalIntegral_comp_comm
      (intervalIntegrable_quasiHillCoefficient u μ w t)] at he
    change G t = quasiHillFixedStateInv v+_ at he
    rw [he]
    congr 1
    apply intervalIntegral.integral_congr_ae_restrict
    rw [uIoc_of_le t.property.1]
    filter_upwards [ae_mono (Measure.restrict_mono (Ioc_subset_Ioc_right t.property.2) (le_refl volume))
      (l2QuasiHillPotential_representative u μ)] with s hs
    rw [hs,quasiHillCoefficient_affine_inverse_intertwine]
    rfl
  apply ContinuousMap.ext
  intro t
  calc
    w t = quasiHillFixedState (G t) := (quasiHillFixedState_right_inv (w t)).symm
    _ = quasiHillFixedState (l2SolutionCurve (l2QuasiHillPotential u μ) (quasiHillAffineFrequency μ)
        (quasiHillFixedStateInv v) t) := congrArg (fun h : Curve (ℂ × ℂ) => quasiHillFixedState (h t)) hg
    _ = l2QuasiHillSolution u μ v t := rfl

end NLS.MKdV
