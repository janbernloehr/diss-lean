import NLS.MKdV.QuasiHillL2AmplitudeJets

/-! # Exact scalar characteristic boundary jets of actual rough states

Polynomial amplitudes map linearly and injectively to their actual state
jets. Their initial quasi-derivatives retain the amplitudes exactly. Their
terminal scalar positions are the formal Taylor multiplication map of the
independently normalized Dirichlet characteristic.
-/
noncomputable section
open Set Complex NLS.LinearVolterra NLS.FunctionalAnalysis NLS.ComplexAnalysis
namespace NLS.MKdV
open NLS.Fourier

/-- The actual normalized IVP with polynomial amplitudes, as a linear map
into full uniform-curve Taylor coefficients. -/
def quasiHillDirichletAmplitudeJet (u : Coeff 2) (lambda : ℂ) (N : ℕ) :
    (Fin N → ℂ) →ₗ[ℂ] (Fin N → Curve (ℂ × ℂ)) where
  toFun a := analyticFiniteJet N (quasiHillDirichletAmplitudeCurve u lambda N a)
  map_add' a b := by
    have he : quasiHillDirichletAmplitudeCurve u lambda N (a+b) =
        fun t => quasiHillDirichletAmplitudeCurve u lambda N a t+
          quasiHillDirichletAmplitudeCurve u lambda N b t := by
      funext t
      unfold quasiHillDirichletAmplitudeCurve
      have hp : pencilChainPolynomial N (a+b) t =
          pencilChainPolynomial N a t+pencilChainPolynomial N b t := by
        simp only [pencilChainPolynomial, Pi.add_apply, smul_add, Finset.sum_add_distrib]
      rw [hp]
      module
    rw [he]
    exact analyticFiniteJet_add (analyticAt_quasiHillDirichletAmplitudeCurve u lambda N a)
      (analyticAt_quasiHillDirichletAmplitudeCurve u lambda N b) N
  map_smul' c a := by
    have he : quasiHillDirichletAmplitudeCurve u lambda N (c • a) =
        fun t => c • quasiHillDirichletAmplitudeCurve u lambda N a t := by
      funext t
      unfold quasiHillDirichletAmplitudeCurve
      have hp : pencilChainPolynomial N (c • a) t = c • pencilChainPolynomial N a t :=
        (chainPolynomial_compCLM (c • ContinuousLinearMap.id ℂ ℂ) N a t).symm
      rw [hp]
      module
    funext k
    change analyticTaylorCoefficient (quasiHillDirichletAmplitudeCurve u lambda N (c • a)) k.val =
      c • analyticTaylorCoefficient (quasiHillDirichletAmplitudeCurve u lambda N a) k.val
    rw [he]
    exact analyticTaylorCoefficient_const_smul (analyticAt_quasiHillDirichletAmplitudeCurve u lambda N a) c k.val

/-- The actual initial state is exactly the prescribed polynomial amplitude. -/
theorem quasiHillDirichletAmplitudeCurve_initial (u : Coeff 2) (lambda : ℂ)
    (N : ℕ) (a : Fin N → ℂ) (t : ℂ) :
    quasiHillDirichletAmplitudeCurve u lambda N a t ⟨0,by constructor <;> norm_num⟩ =
      (0,pencilChainPolynomial N a t) := by
  change pencilChainPolynomial N a t •
    (quasiHillL2SolutionCurve u (lambda+t) (0,1) ⟨0,by constructor <;> norm_num⟩) = _
  rw [quasiHillL2SolutionCurve_zero]
  simp only [Prod.smul_mk, smul_eq_mul, mul_zero, mul_one]

/-- Terminal position is the actual characteristic times the amplitude. -/
theorem quasiHillDirichletAmplitudeCurve_terminal (u : Coeff 2) (lambda : ℂ)
    (N : ℕ) (a : Fin N → ℂ) (t : ℂ) :
    (quasiHillDirichletAmplitudeCurve u lambda N a t ⟨1,by constructor <;> norm_num⟩).1 =
      quasiHillL2Dirichlet u (lambda+t)*pencilChainPolynomial N a t := by
  change pencilChainPolynomial N a t*quasiHillL2Dirichlet u (lambda+t) = _
  exact mul_comm _ _

/-- The initial quasi-derivative coefficient is the SAME raw scalar amplitude. -/
theorem quasiHillDirichletAmplitudeJet_initial (u : Coeff 2) (lambda : ℂ)
    (N : ℕ) (a : Fin N → ℂ) (k : Fin N) :
    quasiHillDirichletAmplitudeJet u lambda N a k ⟨0,by constructor <;> norm_num⟩ = (0,a k) := by
  let T : Curve (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) :=
    ContinuousMap.evalCLM ℂ ⟨0,by constructor <;> norm_num⟩
  let R : ℂ →L[ℂ] (ℂ × ℂ) := (0 : ℂ →L[ℂ] ℂ).prod (ContinuousLinearMap.id ℂ ℂ)
  have he : (fun t : ℂ => T (quasiHillDirichletAmplitudeCurve u lambda N a t)) =
      fun t => R (pencilChainPolynomial N a t) :=
    funext fun t => quasiHillDirichletAmplitudeCurve_initial u lambda N a t
  have h := analyticFiniteJet_compCLM T (analyticAt_quasiHillDirichletAmplitudeCurve u lambda N a) N
  rw [he, analyticFiniteJet_compCLM R (analyticAt_chainPolynomial N a 0),
    analyticFiniteJet_chainPolynomial] at h
  exact (congrFun h k).symm

/-- No amplitude vector is lost by the actual physical state-jet map. -/
theorem quasiHillDirichletAmplitudeJet_injective (u : Coeff 2) (lambda : ℂ) (N : ℕ) :
    Function.Injective (quasiHillDirichletAmplitudeJet u lambda N) := by
  intro a b hab
  funext k
  have h := congrArg (fun v : Fin N → Curve (ℂ × ℂ) =>
    (v k ⟨0,by constructor <;> norm_num⟩).2) hab
  rw [quasiHillDirichletAmplitudeJet_initial, quasiHillDirichletAmplitudeJet_initial] at h
  exact h

/-- The complete terminal position jet is EXACTLY the existing scalar
formal Taylor multiplication map of the normalized characteristic. -/
theorem quasiHillDirichletAmplitudeJet_terminal (u : Coeff 2) (lambda : ℂ)
    (p : FormalMultilinearSeries ℂ ℂ ℂ)
    (hp : HasFPowerSeriesAt (fun t : ℂ => quasiHillL2Dirichlet u (lambda+t)) p 0)
    (N : ℕ) (a : Fin N → ℂ) :
    (fun k : Fin N => (quasiHillDirichletAmplitudeJet u lambda N a k
      ⟨1,by constructor <;> norm_num⟩).1) = scalarTaylorJetMap (scalarFormalTaylor p) N a := by
  let T : Curve (ℂ × ℂ) →L[ℂ] ℂ := (ContinuousLinearMap.fst ℂ ℂ ℂ).comp
    (ContinuousMap.evalCLM ℂ ⟨1,by constructor <;> norm_num⟩)
  have he : (fun t : ℂ => T (quasiHillDirichletAmplitudeCurve u lambda N a t)) =
      fun t => quasiHillL2Dirichlet u (lambda+t)*pencilChainPolynomial N a t :=
    funext fun t => quasiHillDirichletAmplitudeCurve_terminal u lambda N a t
  have h := analyticFiniteJet_compCLM T (analyticAt_quasiHillDirichletAmplitudeCurve u lambda N a) N
  rw [he, analyticFiniteJet_scalarProduct hp] at h
  exact h.symm

/-- The scalar characteristic Taylor kernel is exactly the zero-terminal-
position constraint on the actual physical state jets, at EVERY length. -/
theorem mem_scalarTaylorKernel_iff_quasiHillAmplitudeJet_terminal_zero (u : Coeff 2) (lambda : ℂ)
    (p : FormalMultilinearSeries ℂ ℂ ℂ)
    (hp : HasFPowerSeriesAt (fun t : ℂ => quasiHillL2Dirichlet u (lambda+t)) p 0)
    (N : ℕ) (a : Fin N → ℂ) :
    a ∈ LinearMap.ker (scalarTaylorJetMap (scalarFormalTaylor p) N) ↔
      ∀ k : Fin N, (quasiHillDirichletAmplitudeJet u lambda N a k
        ⟨1,by constructor <;> norm_num⟩).1 = 0 := by
  rw [LinearMap.mem_ker, ← quasiHillDirichletAmplitudeJet_terminal u lambda p hp N a]
  exact funext_iff

end NLS.MKdV
