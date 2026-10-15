import NLS.ZakharovShabat.SourceAngularOriginalBetaBound
import NLS.ZakharovShabat.SourceAngularOriginalEtaAnalytic
import NLS.ZakharovShabat.SourceAngularBetaTheorem13_1Series
import NLS.ZakharovShabat.SourceAngularThetaAnalytic

/-!
# The actual beta correction on the retained Section 12 domain

The original beta bound supplies absolute and locally uniform convergence,
complex analyticity, and decay in both index directions. Reality of the
individual beta values makes their actual correction real at real sources.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceLemma12_12Data
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

theorem beta_original_series (H : SourceLemma12_12Data hp hp1 W₀ W s) :
    SourceAngularBetaSeriesData hp hp1 W s := by
  have hW : IsOpen W := by
    obtain ⟨A,hW,_⟩ := H.previous.previous.atlas
    exact hW ▸ A.toSourcePsiComplexRootAtlas.isOpen_domain
  exact (sourceAngularBetaSeriesAnalyticData_of_uniform_bound hp hp1 s W hW
    (H.boundary_original_displacement_analytic .dirichlet) H.beta_original_analytic
    H.beta_original_uniform_bound).with_decay_of_uniform_bound H.beta_original_uniform_bound

theorem beta_original_correction_im_eq_zero (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (hreal : IsRealType (CoeffPair.toMax p ψ)) (n : ℤ) :
    (sourceAngularBetaCorrection hp hp1 n s ψ).im = 0 :=
  H.beta_original_series.toSourceAngularBetaSeriesAnalyticData.correction_im_eq_zero_of_terms ψ hψ n
    (H.beta_original_im_eq_zero ψ hψ hreal n)

end SourceLemma12_12Data
end NLS.ZakharovShabat
