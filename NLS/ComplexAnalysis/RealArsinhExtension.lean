import NLS.ComplexAnalysis.AnalyticLocalLipschitz
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Complex.SqrtDeriv
import Mathlib.Analysis.SpecialFunctions.Arsinh

/-! # A complex analytic extension of real inverse hyperbolic sine

The principal formula is analytic at every real point. Near zero it
vanishes linearly, giving the scalar estimate needed for ell2 norming
superposition. No single branch across the whole complex plane is asserted.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
namespace NLS.ComplexAnalysis

def realArsinhExtension (z : ℂ) : ℂ := Complex.log (z+Complex.sqrt (1+z^2))

theorem realArsinhExtension_ofReal (x : ℝ) : realArsinhExtension (x : ℂ) = (Real.arsinh x : ℂ) := by
  have hp : 0 < 1+x^2 := by positivity
  have hs : Complex.sqrt (1+(x : ℂ)^2) = (Real.sqrt (1+x^2) : ℂ) := by
    have hcast : (1+(x : ℂ)^2) = ((1+x^2 : ℝ) : ℂ) := by push_cast; rfl
    rw [hcast,Complex.sqrt_of_nonneg (by exact_mod_cast hp.le),ofReal_re]
  have harg : 0 < x+Real.sqrt (1+x^2) := by
    have hh : Real.sqrt (1+x^2) = Real.exp (Real.arsinh x)-x := by rw [Real.exp_arsinh]; ring
    rw [hh]
    linarith [Real.exp_pos (Real.arsinh x)]
  rw [realArsinhExtension,hs,← ofReal_add]
  exact (Complex.ofReal_log harg.le).symm

theorem analyticAt_realArsinhExtension_ofReal (x : ℝ) : AnalyticAt ℂ realArsinhExtension (x : ℂ) := by
  have hp : 0 < 1+x^2 := by positivity
  have hslit : 1+(x : ℂ)^2 ∈ Complex.slitPlane := by
    have hc : 1+(x : ℂ)^2 = ((1+x^2 : ℝ) : ℂ) := by push_cast; rfl
    rw [hc]
    exact Complex.ofReal_mem_slitPlane.mpr hp
  have hs : AnalyticAt ℂ (fun z : ℂ => Complex.sqrt (1+z^2)) (x : ℂ) :=
    (Complex.differentiableOn_sqrt.analyticAt (Complex.isOpen_slitPlane.mem_nhds hslit)).comp
      (f := fun z : ℂ => 1+z^2) (analyticAt_const.add (analyticAt_id.pow 2))
  have hsval : Complex.sqrt (1+(x : ℂ)^2) = (Real.sqrt (1+x^2) : ℂ) := by
    rw [show 1+(x : ℂ)^2 = ((1+x^2 : ℝ) : ℂ) by push_cast; rfl,
      Complex.sqrt_of_nonneg (by exact_mod_cast hp.le),ofReal_re]
  have hpos : 0 < x+Real.sqrt (1+x^2) := by
    rw [← Real.exp_arsinh]
    exact Real.exp_pos _
  have harg : (x : ℂ)+Complex.sqrt (1+(x : ℂ)^2) ∈ Complex.slitPlane := by
    rw [hsval,← ofReal_add]
    exact Complex.ofReal_mem_slitPlane.mpr hpos
  exact (analyticAt_clog harg).comp (f := fun z : ℂ => z+Complex.sqrt (1+z^2)) (analyticAt_id.add hs)

@[simp] theorem realArsinhExtension_zero : realArsinhExtension 0 = 0 := by
  simpa only [ofReal_zero,Real.arsinh_zero] using realArsinhExtension_ofReal 0

theorem exists_realArsinhExtension_linear_bound :
    ∃ L r : ℝ, 0 < L ∧ 0 < r ∧ AnalyticOnNhd ℂ realArsinhExtension (ball 0 r) ∧
      ∀ z ∈ ball 0 r, ‖realArsinhExtension z‖ ≤ L*‖z‖ := by
  have h0 : AnalyticAt ℂ realArsinhExtension 0 := by simpa only [ofReal_zero] using analyticAt_realArsinhExtension_ofReal 0
  obtain ⟨L,d,hL,hd,hLip⟩ := exists_local_lipschitz_bound_of_analyticAt realArsinhExtension 0 h0
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp h0.eventually_analyticAt
  refine ⟨L,min d r,hL,lt_min hd hr,fun z hz => hball (ball_subset_ball (min_le_right _ _) hz),?_⟩
  intro z hz
  have hh := hLip z (ball_subset_ball (min_le_left _ _) hz) 0 (mem_ball_self hd)
  simpa only [realArsinhExtension_zero,sub_zero] using hh

end NLS.ComplexAnalysis
