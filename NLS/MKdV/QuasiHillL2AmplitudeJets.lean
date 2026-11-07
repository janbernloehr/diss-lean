import NLS.MKdV.QuasiHillL2ForcedCurve
import NLS.ComplexAnalysis.AffineVolterraJets

/-! # Actual energy Taylor states for polynomial Dirichlet amplitudes

The normalized rough IVP is multiplied by an arbitrary finite scalar
amplitude polynomial. Its Taylor coefficients satisfy the actual forced
Volterra recurrence. Each coefficient is therefore an AC physical H1
state, without assuming an analytic H1-valued reconstruction.
-/
noncomputable section
open Set Complex NLS.LinearVolterra NLS.FunctionalAnalysis NLS.ComplexAnalysis
namespace NLS.MKdV
open NLS.Fourier

/-- The full uniform-curve initial datum with zero scalar position. -/
def quasiHillAmplitudeInitial : ℂ →L[ℂ] Curve (ℂ × ℂ) :=
  (ContinuousLinearMap.const ℂ (Icc (0:ℝ) 1)).comp
    ((0 : ℂ →L[ℂ] ℂ).prod (ContinuousLinearMap.id ℂ ℂ))

theorem quasiHillAmplitudeInitial_apply (a : ℂ) (x : Icc (0:ℝ) 1) :
    quasiHillAmplitudeInitial a x = (0,a) := rfl

/-- The actual normalized rough Dirichlet IVP with a polynomial amplitude. -/
def quasiHillDirichletAmplitudeCurve (u : Coeff 2) (lambda : ℂ)
    (N : ℕ) (a : Fin N → ℂ) (t : ℂ) : Curve (ℂ × ℂ) :=
  pencilChainPolynomial N a t • quasiHillL2SolutionCurve u (lambda+t) (0,1)

/-- Analyticity holds in the FULL uniform state-curve norm. -/
theorem analyticAt_quasiHillDirichletAmplitudeCurve (u : Coeff 2) (lambda : ℂ)
    (N : ℕ) (a : Fin N → ℂ) : AnalyticAt ℂ (quasiHillDirichletAmplitudeCurve u lambda N a) 0 := by
  have hS : AnalyticAt ℂ (fun t : ℂ => quasiHillL2SolutionCurve u (lambda+t) (0,1)) 0 := by
    have h := (analyticOnNhd_quasiHillL2SolutionCurve_joint (0,1)
      (lambda+(0:ℂ),u) (mem_univ _)).comp
        (f := fun t : ℂ => (lambda+t,u)) ((analyticAt_const.add analyticAt_id).prod analyticAt_const)
    exact h
  exact (analyticAt_chainPolynomial N a 0).smul hS

/-- Every polynomial amplitude solves the actual full scalar Volterra equation. -/
theorem quasiHillDirichletAmplitudeCurve_eq_volterra (u : Coeff 2) (lambda : ℂ)
    (N : ℕ) (a : Fin N → ℂ) (t : ℂ) :
    quasiHillDirichletAmplitudeCurve u lambda N a t =
      quasiHillAmplitudeInitial (pencilChainPolynomial N a t)+
        quasiHillL2Volterra u (lambda+t) (quasiHillDirichletAmplitudeCurve u lambda N a t) := by
  have h := congrArg (fun w : Curve (ℂ × ℂ) => pencilChainPolynomial N a t • w)
    (quasiHillL2SolutionCurve_eq_volterra u (lambda+t) (0,1))
  have hi : pencilChainPolynomial N a t • (ContinuousMap.const _ (0,1) : Curve (ℂ × ℂ)) =
      quasiHillAmplitudeInitial (pencilChainPolynomial N a t) := by
    apply ContinuousMap.ext
    intro x
    change (pencilChainPolynomial N a t*(0:ℂ),pencilChainPolynomial N a t*1) = _
    simp only [mul_zero, mul_one, quasiHillAmplitudeInitial_apply]
  have hs : pencilChainPolynomial N a t •
      (ContinuousMap.const _ (0,1)+quasiHillL2Volterra u (lambda+t)
        (quasiHillL2SolutionCurve u (lambda+t) (0,1))) =
      pencilChainPolynomial N a t • ContinuousMap.const _ (0,1)+
        pencilChainPolynomial N a t • quasiHillL2Volterra u (lambda+t)
          (quasiHillL2SolutionCurve u (lambda+t) (0,1)) := by module
  have he := h.trans hs
  rw [hi] at he
  exact he.trans (congrArg (fun r : Curve (ℂ × ℂ) =>
    quasiHillAmplitudeInitial (pencilChainPolynomial N a t)+r)
      ((quasiHillL2Volterra u (lambda+t)).map_smul (pencilChainPolynomial N a t)
        (quasiHillL2SolutionCurve u (lambda+t) (0,1))).symm)

/-- Exact initial-data coefficient, with the prescribed finite amplitude retained. -/
theorem quasiHillAmplitudeInitial_coefficient (N : ℕ) (a : Fin N → ℂ) (k : Fin N) :
    analyticTaylorCoefficient (fun t : ℂ => quasiHillAmplitudeInitial (pencilChainPolynomial N a t)) k.val =
      quasiHillAmplitudeInitial (a k) := by
  rw [analyticTaylorCoefficient_compCLM quasiHillAmplitudeInitial (analyticAt_chainPolynomial N a 0),
    analyticTaylorCoefficient_chainPolynomial]

/-- The first actual state coefficient solves the homogeneous integral equation. -/
theorem quasiHillDirichletAmplitudeCoefficient_zero (u : Coeff 2) (lambda : ℂ)
    (N : ℕ) (a : Fin N → ℂ) (hN : 0 < N) :
    analyticTaylorCoefficient (quasiHillDirichletAmplitudeCurve u lambda N a) 0 =
      quasiHillAmplitudeInitial (a ⟨0,hN⟩)+quasiHillL2Volterra u lambda
        (analyticTaylorCoefficient (quasiHillDirichletAmplitudeCurve u lambda N a) 0) := by
  have he := affineVolterra_coefficient_zero (quasiHillL2Volterra u lambda) quasiHillL2EnergyVolterra
    (quasiHillDirichletAmplitudeCurve u lambda N a)
    (fun t => quasiHillAmplitudeInitial (pencilChainPolynomial N a t)) (fun t => by
      rw [← quasiHillL2Volterra_add_energy]
      exact quasiHillDirichletAmplitudeCurve_eq_volterra u lambda N a t)
  rw [quasiHillAmplitudeInitial_coefficient N a ⟨0,hN⟩] at he
  exact he

/-- Every subsequent state coefficient is forced by EXACTLY its preceding position. -/
theorem quasiHillDirichletAmplitudeCoefficient_succ (u : Coeff 2) (lambda : ℂ)
    (N : ℕ) (a : Fin N → ℂ) (k : ℕ) (hk : k+1 < N) :
    analyticTaylorCoefficient (quasiHillDirichletAmplitudeCurve u lambda N a) (k+1) =
      quasiHillAmplitudeInitial (a ⟨k+1,hk⟩)+quasiHillL2Volterra u lambda
        (analyticTaylorCoefficient (quasiHillDirichletAmplitudeCurve u lambda N a) (k+1))+
      quasiHillL2EnergyVolterra (analyticTaylorCoefficient (quasiHillDirichletAmplitudeCurve u lambda N a) k) := by
  have hf := analyticAt_quasiHillDirichletAmplitudeCurve u lambda N a
  have hc : AnalyticAt ℂ (fun t => quasiHillAmplitudeInitial (pencilChainPolynomial N a t)) 0 :=
    (quasiHillAmplitudeInitial.analyticAt _).comp (analyticAt_chainPolynomial N a 0)
  have he := affineVolterra_coefficient_succ (quasiHillL2Volterra u lambda) quasiHillL2EnergyVolterra
    hf hc (fun t => by
      rw [← quasiHillL2Volterra_add_energy]
      exact quasiHillDirichletAmplitudeCurve_eq_volterra u lambda N a t) k
  rw [quasiHillAmplitudeInitial_coefficient N a ⟨k+1,hk⟩] at he
  exact he

/-- The first extracted coefficient is a genuine AC physical state, with zero forcing. -/
theorem isQuasiHillL2ForcedSolution_amplitudeCoefficient_zero (u : Coeff 2) (lambda : ℂ)
    (N : ℕ) (a : Fin N → ℂ) (hN : 0 < N) :
    IsQuasiHillL2ForcedSolution u lambda 0
      (analyticTaylorCoefficient (quasiHillDirichletAmplitudeCurve u lambda N a) 0) := by
  apply isQuasiHillL2ForcedSolution_of_volterra u lambda _ _ (0,a ⟨0,hN⟩)
  rw [map_zero, add_zero]
  exact quasiHillDirichletAmplitudeCoefficient_zero u lambda N a hN

/-- Later extracted coefficients are genuine AC physical forced states. -/
theorem isQuasiHillL2ForcedSolution_amplitudeCoefficient_succ (u : Coeff 2) (lambda : ℂ)
    (N : ℕ) (a : Fin N → ℂ) (k : ℕ) (hk : k+1 < N) :
    IsQuasiHillL2ForcedSolution u lambda
      (analyticTaylorCoefficient (quasiHillDirichletAmplitudeCurve u lambda N a) k)
      (analyticTaylorCoefficient (quasiHillDirichletAmplitudeCurve u lambda N a) (k+1)) := by
  apply isQuasiHillL2ForcedSolution_of_volterra u lambda _ _ (0,a ⟨k+1,hk⟩)
  exact quasiHillDirichletAmplitudeCoefficient_succ u lambda N a k hk

/-- EVERY extracted physical Taylor coefficient has both components in full interval H1. -/
theorem quasiHillDirichletAmplitudeJet_intervalH1 (u : Coeff 2) (lambda : ℂ)
    (N : ℕ) (a : Fin N → ℂ) (k : Fin N) :
    HasIntervalH1Regularity (fun x => (extend (analyticFiniteJet N
      (quasiHillDirichletAmplitudeCurve u lambda N a) k) x).1) ∧
    HasIntervalH1Regularity (fun x => (extend (analyticFiniteJet N
      (quasiHillDirichletAmplitudeCurve u lambda N a) k) x).2) := by
  rw [analyticFiniteJet_eq_coefficient]
  obtain ⟨n,hn⟩ := k
  cases n with
  | zero =>
    exact (isQuasiHillL2ForcedSolution_amplitudeCoefficient_zero u lambda N a hn).intervalH1 u lambda _ _
  | succ n =>
    exact (isQuasiHillL2ForcedSolution_amplitudeCoefficient_succ u lambda N a n hn).intervalH1 u lambda _ _

end NLS.MKdV
