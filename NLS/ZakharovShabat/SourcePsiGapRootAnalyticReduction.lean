import NLS.ZakharovShabat.SourcePsiGapRootDerivative
import NLS.ZakharovShabat.SourceRealTypeBanachSpace

/-!
# Reduction of real analyticity of the canonical gap roots

At every real-type source, an anchored selected contour chart has a
bijective root Jacobian, a jointly analytic equation, and a complex
`C¹` zero branch agreeing with the canonical roots on nearby real
sources. The analytic implicit theorem makes that branch analytic.
Restriction to the real source Banach space gives real analyticity
of the canonical root map.
-/

noncomputable section
open Set Filter Topology
open scoped ENNReal ContDiff
namespace NLS.ZakharovShabat

/-- The anchored analytic selected contour equation and its
invertible root Jacobian give real analyticity of the canonical
gap-root map at each real-type source. -/
theorem analyticAt_sourcePsiGapRoot_real
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (φ : realTypeSourceSubmodule p) :
    AnalyticAt ℝ
      (fun ψ : realTypeSourceSubmodule p =>
        sourcePsiGapRoot hp hp1 n ψ) φ := by
  obtain ⟨c,R,s,hs,hsφ,hreal,hbij,hzero,hF,_⟩ :=
    exists_sourcePsiGapRoot_derivative_equation hp hp1 n φ
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

/-- The canonical selected psi roots depend real analytically on
every real-type source in the real Banach source space. -/
theorem analyticOnNhd_sourcePsiGapRoot_real
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) :
    AnalyticOnNhd ℝ
      (fun φ : realTypeSourceSubmodule p =>
        sourcePsiGapRoot hp hp1 n φ) Set.univ := by
  intro φ _
  exact analyticAt_sourcePsiGapRoot_real hp hp1 n φ

end NLS.ZakharovShabat
