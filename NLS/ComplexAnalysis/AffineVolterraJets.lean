import NLS.ComplexAnalysis.AffinePencilJets

/-! # Taylor recurrences for actual affine Volterra equations

The coefficient is the existing factorial-normalized Banach finite jet.
Bounded operators commute with it; an affine parameter dependence shifts
the preceding coefficient exactly once. No parameter/time derivative
interchange is assumed.
-/
noncomputable section
namespace NLS.ComplexAnalysis
open NLS.FunctionalAnalysis
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- A single normalized coefficient of the actual analytic germ at zero. -/
def analyticTaylorCoefficient (f : ℂ → E) (n : ℕ) : E :=
  analyticFiniteJet (n+1) f (Fin.last n)

omit [CompleteSpace E] in
theorem analyticTaylorCoefficient_zero (f : ℂ → E) : analyticTaylorCoefficient f 0 = f 0 := by
  simp [analyticTaylorCoefficient, analyticFiniteJet, iteratedDeriv_zero]

omit [CompleteSpace E] in
/-- A finite jet retains exactly the corresponding natural-index coefficient. -/
theorem analyticFiniteJet_eq_coefficient (N : ℕ) (f : ℂ → E) (k : Fin N) :
    analyticFiniteJet N f k = analyticTaylorCoefficient f k.val := rfl

/-- The actual normalized coefficient commutes with every bounded linear map. -/
theorem analyticTaylorCoefficient_compCLM (T : E →L[ℂ] F) {f : ℂ → E}
    (hf : AnalyticAt ℂ f 0) (n : ℕ) :
    analyticTaylorCoefficient (fun t => T (f t)) n = T (analyticTaylorCoefficient f n) :=
  congrFun (analyticFiniteJet_compCLM T hf (n+1)) (Fin.last n)

theorem analyticTaylorCoefficient_add {f g : ℂ → E}
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) (n : ℕ) :
    analyticTaylorCoefficient (fun t => f t+g t) n =
      analyticTaylorCoefficient f n+analyticTaylorCoefficient g n :=
  congrFun (analyticFiniteJet_add hf hg (n+1)) (Fin.last n)

theorem analyticTaylorCoefficient_const_smul {f : ℂ → E}
    (hf : AnalyticAt ℂ f 0) (c : ℂ) (n : ℕ) :
    analyticTaylorCoefficient (fun t => c • f t) n = c • analyticTaylorCoefficient f n :=
  analyticTaylorCoefficient_compCLM (c • ContinuousLinearMap.id ℂ E) hf n

/-- Multiplication by the spectral increment is a pure shift after factorial normalization. -/
theorem analyticTaylorCoefficient_t_smul_succ {f : ℂ → E}
    (hf : AnalyticAt ℂ f 0) (k : ℕ) :
    analyticTaylorCoefficient (fun t : ℂ => t • f t) (k+1) = analyticTaylorCoefficient f k :=
  normalized_iteratedDeriv_t_smul_succ hf k

/-- Finite input polynomials retain their prescribed coefficients exactly. -/
theorem analyticTaylorCoefficient_chainPolynomial (N : ℕ) (v : Fin N → E) (k : Fin N) :
    analyticTaylorCoefficient (pencilChainPolynomial N v) k.val = v k :=
  congrFun (analyticFiniteJet_chainPolynomial N v) k

omit [CompleteSpace E] in
/-- The initial coefficient satisfies the actual fixed-parameter integral equation. -/
theorem affineVolterra_coefficient_zero (V B : E →L[ℂ] E) (f c : ℂ → E)
    (he : ∀ t : ℂ, f t = c t+(V+t • B) (f t)) :
    analyticTaylorCoefficient f 0 = analyticTaylorCoefficient c 0+
      V (analyticTaylorCoefficient f 0) := by
  simpa only [analyticTaylorCoefficient_zero, zero_smul, add_zero] using he 0

/-- Every later coefficient is forced by exactly its preceding coefficient,
with the complete bounded operator and initial-data coefficient retained. -/
theorem affineVolterra_coefficient_succ (V B : E →L[ℂ] E) {f c : ℂ → E}
    (hf : AnalyticAt ℂ f 0) (hc : AnalyticAt ℂ c 0)
    (he : ∀ t : ℂ, f t = c t+(V+t • B) (f t)) (k : ℕ) :
    analyticTaylorCoefficient f (k+1) = analyticTaylorCoefficient c (k+1)+
      V (analyticTaylorCoefficient f (k+1))+B (analyticTaylorCoefficient f k) := by
  have hV : AnalyticAt ℂ (fun t => V (f t)) 0 := (V.analyticAt _).comp hf
  have hB : AnalyticAt ℂ (fun t => B (f t)) 0 := (B.analyticAt _).comp hf
  have ht : AnalyticAt ℂ (fun t : ℂ => t • B (f t)) 0 := analyticAt_id.smul hB
  have hfun : f = fun t : ℂ => (c t+V (f t))+t • B (f t) := by
    funext t
    simpa only [add_apply, smul_apply, add_assoc] using he t
  have hsum : AnalyticAt ℂ (fun t => c t+V (f t)) 0 := hc.add hV
  have h := congrArg (fun g : ℂ → E => analyticTaylorCoefficient g (k+1)) hfun
  rw [analyticTaylorCoefficient_add hsum ht,
    analyticTaylorCoefficient_add hc hV,
    analyticTaylorCoefficient_compCLM V hf,
    analyticTaylorCoefficient_t_smul_succ hB,
    analyticTaylorCoefficient_compCLM B hf] at h
  exact h

end NLS.ComplexAnalysis
