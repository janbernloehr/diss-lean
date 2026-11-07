import NLS.KdV.PseudomeasureWideWeightedErrors

/-! The same literal physical scalar entries are jointly complex analytic
on the full printed strip at every strictly controlled tail. -/
noncomputable section
open scoped ENNReal
namespace NLS.KdV

/-- Every actual effective coefficient is jointly analytic in the full endpoint norm and lambda. -/
theorem analyticAt_endpointEffective_coefficient_wide (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (n : ℕ) (hn : 2 ≤ n)
    (p : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ × ℂ)
    (hz : p.2 ∈ wideHillStrip n)
    (hs : 13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖p.1‖ ≤ 1/2)
    (u : ℂ × ℂ) (k : ℤ) :
    AnalyticAt ℂ (fun x => (endpointEffectiveFamily r hr hr1 n x u).val k) p := by
  have hE := SchurComplement.analyticAt_compCLM
    (analyticAt_endpointInverseFamily_wide r hr hr1 n hn p hz hs)
    (analyticAt_endpointModePotentialFamily r hr hr1 n p)
  let e := (WeightedCoeff.evalCLM (SpectralWeight.one.negativeSobolev r) ⊤ k).comp
    (ContinuousLinearMap.apply ℂ (WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) u)
  exact (e.analyticAt _).comp (f := endpointEffectiveFamily r hr hr1 n) hE

/-- Analyticity of the three literal scalar entries used in the source determinant. -/
theorem analyticAt_endpointCoefficients_wide (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (n : ℕ) (hn : 2 ≤ n)
    (p : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ × ℂ)
    (hz : p.2 ∈ wideHillStrip n)
    (hs : 13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖p.1‖ ≤ 1/2) :
    AnalyticAt ℂ (endpointDiagonal r hr hr1 n) p ∧
      AnalyticAt ℂ (endpointUpperCoupling r hr hr1 n) p ∧
      AnalyticAt ℂ (endpointLowerCoupling r hr hr1 n) p :=
  ⟨analyticAt_endpointEffective_coefficient_wide r hr hr1 n hn p hz hs (1,0) n,
    analyticAt_endpointEffective_coefficient_wide r hr hr1 n hn p hz hs (0,1) n,
    analyticAt_endpointEffective_coefficient_wide r hr hr1 n hn p hz hs (1,0) (-(n:ℤ))⟩

end NLS.KdV
