import NLS.ZakharovShabat.SourcePsiGapRootDerivative
import NLS.ZakharovShabat.SourceRealTypeBanachSpace

/-!
# Reduction of real analyticity of the canonical gap roots

At every real-type source, an anchored selected contour chart already
has a bijective root Jacobian and a complex `C¹` zero branch agreeing
with the canonical roots on nearby real sources. If the selected
equation in this chart has a joint Banach power series, the analytic
implicit theorem makes that branch analytic. Restriction to the real
source Banach space then gives real analyticity of the canonical map.
-/

noncomputable section
open Set Filter Topology
open scoped ENNReal ContDiff
namespace NLS.ZakharovShabat

/-- At each real-type source there is a concrete selected contour
chart for which joint analyticity of its equation implies real
analyticity of the canonical gap-root map at that source. -/
theorem exists_chart_analyticAt_sourcePsiGapRoot_real
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (φ : realTypeSourceSubmodule p) :
    ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ,
      AnalyticAt ℂ
        (fun t : DeletedCoeff p n × CoeffPair p =>
          sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2)
        (sourcePsiGapRoot hp hp1 n φ,(φ : CoeffPair p)) →
      AnalyticAt ℝ
        (fun ψ : realTypeSourceSubmodule p =>
          sourcePsiGapRoot hp hp1 n ψ) φ := by
  obtain ⟨c,R,s,hs,hsφ,hreal,hbij,hzero,_⟩ :=
    exists_sourcePsiGapRoot_derivative_equation hp hp1 n φ
  refine ⟨c,R,?_⟩
  intro hF
  have hsAnalytic : AnalyticAt ℂ s (φ : CoeffPair p) :=
    analyticAt_sourcePsi_implicit_solution_of_analytic
      hp hp1 n c R s (φ : CoeffPair p)
      (by simpa only [hsφ] using hF) hs.continuousAt hzero
      (by simpa only [hsφ] using hbij)
  have hsub : AnalyticAt ℝ
      (fun ψ : realTypeSourceSubmodule p => (ψ : CoeffPair p)) φ :=
    (realTypeSourceSubmodule p).subtypeL.analyticAt φ
  have hcomp : AnalyticAt ℝ
      (fun ψ : realTypeSourceSubmodule p => s (ψ : CoeffPair p)) φ :=
    (hsAnalytic.restrictScalars (𝕜 := ℝ)).comp hsub
  have hval : Tendsto
      (fun ψ : realTypeSourceSubmodule p => (ψ : CoeffPair p))
      (𝓝 φ) (𝓝 (φ : CoeffPair p)) :=
    continuous_subtype_val.continuousAt
  have hEq : (fun ψ : realTypeSourceSubmodule p => s (ψ : CoeffPair p)) =ᶠ[𝓝 φ]
      (fun ψ => sourcePsiGapRoot hp hp1 n ψ) := by
    filter_upwards [hval.eventually hreal] with ψ hψ
    exact hψ ψ.property
  exact hcomp.congr hEq

/-- A joint Banach power series for every selected psi chart at its
canonical real root gives real analyticity of the entire canonical
root map. The chart-specific implication above is the pointwise
version used in this reduction. -/
theorem analyticOnNhd_sourcePsiGapRoot_real_of_selectedEquation_analytic
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (hF : ∀ φ : realTypeSourceSubmodule p,
      ∀ c : ℤ → ℂ, ∀ R : ℤ → ℝ,
        AnalyticAt ℂ
          (fun t : DeletedCoeff p n × CoeffPair p =>
            sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2)
          (sourcePsiGapRoot hp hp1 n φ,(φ : CoeffPair p))) :
    AnalyticOnNhd ℝ
      (fun φ : realTypeSourceSubmodule p =>
        sourcePsiGapRoot hp hp1 n φ) Set.univ := by
  intro φ _
  obtain ⟨c,R,hchart⟩ :=
    exists_chart_analyticAt_sourcePsiGapRoot_real hp hp1 n φ
  exact hchart (hF φ c R)

end NLS.ZakharovShabat
