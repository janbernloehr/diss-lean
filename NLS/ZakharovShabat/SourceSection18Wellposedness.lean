import NLS.ZakharovShabat.HigherExponentAnalyticNLSSolutions
import NLS.ZakharovShabat.SmoothClassicalNLSNonextension

/-!
# Theorem 18.5 in the original solution sense

Solutions are limits for every sequence of smooth initial data. Analytic
dependence is in the uniform norm on compact time intervals. Illposedness
refers to extensions of the actual ordinary classical solution map.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- All four parts of Theorem 18.5 and uniqueness in its solution definition. -/
structure SourceSection18WellposednessData (hp : p ≠ ⊤) (hp1 : 1 < p) : Prop where
  global : p ≤ 2 →
    IsGloballyAnalyticallyWellposedOn (fun f : SmoothNLSData => f.renormalizedSource p) univ
  local_wellposed : IsLocallyAnalyticallyWellposed (fun f : SmoothNLSData => f.renormalizedSource p)
  small_global : 2 < p → ∃ U : Set (realTypeSourceSubmodule p),
    (0 : realTypeSourceSubmodule p) ∈ U ∧ (∃ r > 0, Metric.ball 0 r ⊆ U) ∧
    IsGloballyAnalyticallyWellposedOn (fun f : SmoothNLSData => f.renormalizedSource p) U
  ordinary_nonextension : ∀ (q : ℝ≥0∞) [Fact (1 ≤ q)], q ≠ ⊤ →
    ∀ h2p : 2 < p, p ≤ q → ∀ T : ℝ, 0 < T → ∀ φ : realTypeSourceSubmodule p,
      φ ∉ sourceHilbertLocus h2p.le →
      ∀ F : realTypeSourceSubmodule p → C(Icc (-T) T,realTypeSourceSubmodule q),
        AgreesWithSmoothClassicalNLS (Icc (-T) T) F → ¬ ContinuousAt F φ
  unique : ∀ (J K : Set ℝ) (φ : realTypeSourceSubmodule p)
    (γ η : ℝ → realTypeSourceSubmodule p),
    IsRenormalizedNLSSolutionOn J φ γ → IsRenormalizedNLSSolutionOn K φ η → EqOn γ η (J ∩ K)

/-- Unconditional wellposedness and nonextension for every finite source exponent above one. -/
theorem source_theorem18_5 (hp : p ≠ ⊤) (hp1 : 1 < p) : SourceSection18WellposednessData hp hp1 := by
  refine ⟨renormalizedNLS_globallyAnalyticallyWellposed hp hp1,
    renormalizedNLS_locallyAnalyticallyWellposed hp hp1,?_,?_,?_⟩
  · intro hp2
    exact exists_small_global_analytic_renormalizedNLSSolutions hp hp1 hp2.le
  · intro q inst hq h2p hpq T hT φ hφ F hF
    exact smoothClassicalNLS_theorem18_5_iv hp hq h2p hpq T hT φ hφ F hF
  · intro J K φ γ η hγ hη
    exact hγ.eqOn_inter hη hp hp1

end NLS.ZakharovShabat
