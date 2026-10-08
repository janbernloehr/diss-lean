import NLS.ZakharovShabat.SmoothApproximationSolution
import Mathlib.Analysis.Analytic.Basic

/-! # Analytic wellposedness in the dissertation's solution sense

The trajectory norm is the uniform norm on a compact time interval. Local
wellposedness requires a common positive time and an open neighborhood of
every datum. Global wellposedness uses one solution for all real times and
analytic restriction maps for every positive compact time horizon.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Local real analytic wellposedness, with solutions defined by all smooth approximations. -/
def IsLocallyAnalyticallyWellposed
    (S : SmoothNLSData → ℝ → realTypeSourceSubmodule p) : Prop :=
  ∀ φ : realTypeSourceSubmodule p, ∃ T > 0, ∃ U : Set (realTypeSourceSubmodule p),
    IsOpen U ∧ φ ∈ U ∧
    ∃ F : realTypeSourceSubmodule p → ℝ → realTypeSourceSubmodule p,
      (∀ ψ ∈ U, IsSmoothApproximationSolutionOn S (Icc (-T) T) ψ (F ψ)) ∧
      ∃ G : realTypeSourceSubmodule p → C(Icc (-T) T,realTypeSourceSubmodule p),
        AnalyticOnNhd ℝ G U ∧ ∀ ψ ∈ U, ∀ time : Icc (-T) T, G ψ time = F ψ time.val

/-- Global real analytic wellposedness on an open initial-data set. -/
def IsGloballyAnalyticallyWellposedOn
    (S : SmoothNLSData → ℝ → realTypeSourceSubmodule p)
    (U : Set (realTypeSourceSubmodule p)) : Prop :=
  IsOpen U ∧ ∃ F : realTypeSourceSubmodule p → ℝ → realTypeSourceSubmodule p,
    (∀ φ ∈ U, IsSmoothApproximationSolutionOn S univ φ (F φ)) ∧
    ∀ T > 0, ∃ G : realTypeSourceSubmodule p → C(Icc (-T) T,realTypeSourceSubmodule p),
      AnalyticOnNhd ℝ G U ∧ ∀ φ ∈ U, ∀ time : Icc (-T) T, G φ time = F φ time.val

/-- Global wellposedness on the whole source space implies local wellposedness. -/
theorem IsGloballyAnalyticallyWellposedOn.local
    {S : SmoothNLSData → ℝ → realTypeSourceSubmodule p}
    (h : IsGloballyAnalyticallyWellposedOn S univ) : IsLocallyAnalyticallyWellposed S := by
  obtain ⟨hU,F,hF,hG⟩ := h
  intro φ
  obtain ⟨G,hGa,hGe⟩ := hG 1 (by norm_num)
  refine ⟨1,by norm_num,univ,hU,mem_univ _,F,?_,G,hGa,hGe⟩
  intro ψ hψ
  exact (hF ψ hψ).restrict (subset_univ _) (by constructor <;> norm_num)

end NLS.ZakharovShabat
