import NLS.KdV.HillIndexedFlowExtension
import NLS.FunctionalAnalysis.AutonomousGlobalContinuation

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.LinearVolterra NLS.FunctionalAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



/-- An actual global indexed mean-zero Hill trajectory conserves its original
mean and rough norm and every energy discriminant at every real time. -/
theorem hillIndexedIntegralCurve_global_conserved
    (k : ℕ) (hk : 1≤k) (γ : ℝ → hillRealSourceSubmodule)
    (hγ : ∀ t : ℝ, HasDerivAt γ (hillRealIndexedDiscriminantField k hk (γ t)) t)
    (hmean : (γ 0).val.val 0=0) (t : ℝ) :
    (γ t).val.val 0=0 ∧ ‖(γ t).val‖=‖(γ 0).val‖ ∧ ∀ E : ℂ,
      hillL2Discriminant (SpectralWeight.one.toCoeff (γ t).val) E=
        hillL2Discriminant (SpectralWeight.one.toCoeff (γ 0).val) E := by
  let a : ℝ := min t 0-1
  let b : ℝ := max t 0+1
  have ht : t∈Ioo a b := ⟨by dsimp only [a];linarith [min_le_left t 0],
    by dsimp only [b];linarith [le_max_left t 0]⟩
  have h0 : (0 : ℝ)∈Ioo a b := ⟨by dsimp only [a];linarith [min_le_right t 0],
    by dsimp only [b];linarith [le_max_right t 0]⟩
  refine ⟨(hillMean_eq_on_indexed_integralCurve k hk γ a b (fun s _ => hγ s) t 0 ht h0).trans hmean,
    (hillSource_norm_eq_on_indexed_integralCurve k hk γ a b (fun s _ => hγ s) 0 t h0 ht hmean).symm,?_⟩
  intro E
  exact hillL2Discriminant_eq_on_indexed_integralCurve k hk γ a b (fun s _ => hγ s) t 0 ht h0 E

/-- Every original real mean-zero rough Hill source has an actual indexed
spectral trajectory for all real times. It conserves the original source
norm, mean and every discriminant; no global-flow or continuation hypothesis
is supplied. Endpoints, collapsed gaps and zero sources are included. -/
theorem exists_hillIndexedDiscriminant_global_integralCurve
    (k : ℕ) (hk : 1≤k) (q : RealPeriodOneHillPotential) (hmean : q.val.val 0=0) :
    ∃ γ : ℝ → hillRealSourceSubmodule, (γ 0).val=q.val ∧
      (∀ t : ℝ, HasDerivAt γ (hillRealIndexedDiscriminantField k hk (γ t)) t) ∧
      ∀ t : ℝ, (γ t).val.val 0=0 ∧ ‖(γ t).val‖=‖q.val‖ ∧ ∀ E : ℂ,
        hillL2Discriminant (SpectralWeight.one.toCoeff (γ t).val) E=
          hillL2Discriminant (SpectralWeight.one.toCoeff q.val) E := by
  let q0 : hillRealSourceSubmodule := ⟨q.val,q.property⟩
  let V := hillRealIndexedDiscriminantField k hk
  have hV : ContDiff ℝ 1 V := contDiff_hillRealIndexedDiscriminantField k hk
  have hlocal : Nonempty (AutonomousTrajectory V q0) := by
    obtain ⟨γ,hγ0,ε,hε,hD⟩ := hV.contDiffAt (x := q0) |>.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ 0
    exact ⟨⟨γ,-ε,ε,⟨by linarith,hε⟩,hγ0,
      fun t ht => hD t (by simpa only [zero_sub,zero_add] using ht)⟩⟩
  have hExt : AutonomousEndpointExtensions V q0 := by
    constructor
    · intro T
      have hm : (T.curve 0).val.val 0=0 := by rw [T.initialSource];exact hmean
      exact exists_hillIndexedIntegralCurve_extend_right k hk T.curve T.lower T.upper T.hasDerivAt
        0 T.initialTime_mem hm
    · intro T
      have hm : (T.curve 0).val.val 0=0 := by rw [T.initialSource];exact hmean
      exact exists_hillIndexedIntegralCurve_extend_left k hk T.curve T.lower T.upper T.hasDerivAt
        0 T.initialTime_mem hm
  obtain ⟨γ,hγ0,hD⟩ := exists_global_autonomousTrajectory_of_endpointExtensions V q0 hV hlocal hExt
  have h0 : (γ 0).val=q.val := congrArg Subtype.val hγ0
  have hm0 : (γ 0).val.val 0=0 := by rw [h0];exact hmean
  refine ⟨γ,h0,hD,?_⟩
  intro t
  have hh := hillIndexedIntegralCurve_global_conserved k hk γ hD hm0 t
  simpa only [h0] using hh

end NLS.KdV
