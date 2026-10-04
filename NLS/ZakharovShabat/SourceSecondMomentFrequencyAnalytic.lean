import NLS.ZakharovShabat.SourceAbelianMomentSeries
import NLS.ComplexAnalysis.LocalAnalyticApproximationOn
import NLS.ComplexAnalysis.BanachSmoothAnalyticOn

/-! # Analytic renormalized frequencies from second moments

The absolutely convergent moment sum defines a complex analytic function
on a connected neighborhood of the real source locus. Its symmetric
partial sums converge uniformly on a neighborhood of every source.
-/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {W V : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The moment-sum candidate for the renormalized frequency in Theorem 20.4. -/
def SourceAbelianMomentAtlas.renormalizedFrequency
    (A : SourceAbelianMomentAtlas hp hp1 W s) (n : ℤ) (ψ : CoeffPair p) : ℂ :=
  -(4/(2*Real.pi):ℂ)*(∑' k : ℤ, A.moment n k 2 ψ)

/-- Absolute convergence, local uniform convergence, and complex
analyticity of the renormalized moment sum for every selected index. -/
theorem SourceAbelianMomentAtlas.exists_analytic_renormalizedFrequency
    (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 V s)
    (hV : IsOpen V) (hrealV : realTypeSourceLocus p ⊆ V) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ IsConnected U ∧ realTypeSourceLocus p ⊆ U ∧
      U ⊆ A.domain ∩ V ∧
      (∀ ψ ∈ U, ∀ n : ℤ, Summable (fun k => ‖A.moment n k 2 ψ‖)) ∧
      (∀ n : ℤ, AnalyticOnNhd ℂ (A.renormalizedFrequency n) U) ∧
      ∀ φ ∈ U, ∃ T : Set (CoeffPair p), IsOpen T ∧ φ ∈ T ∧ T ⊆ U ∧ ∀ n : ℤ,
        TendstoUniformlyOn
          (fun (N : ℕ) ψ => -(4/(2*Real.pi):ℂ)*
            ∑ k ∈ Finset.Icc (-(N : ℤ)) N, A.moment n k 2 ψ)
          (A.renormalizedFrequency n) atTop T := by
  classical
  obtain ⟨U,hU,hUc,hreal,hUV,hsum,huniform⟩ := A.exists_secondMoment_series hs hV hrealV
  have hanalytic (n : ℤ) : AnalyticOnNhd ℂ (fun ψ => ∑' k : ℤ, A.moment n k 2 ψ) U := by
    have hpartial (N : ℕ) : AnalyticOnNhd ℂ
        (fun ψ => ∑ k ∈ Finset.Icc (-(N : ℤ)) N, A.moment n k 2 ψ) U := by
      intro ψ hψ
      apply Finset.analyticAt_fun_sum
      intro k _
      exact A.analytic_moment n k 2 ψ (hUV hψ).1
    have happrox := HasLocalUniformAnalyticApproximationOn.of_open_local_uniform hU hpartial
      (fun φ hφ => by
        obtain ⟨T,hT,hφT,_,hconv⟩ := huniform φ hφ
        exact ⟨T,hT,hφT,hconv n⟩)
    exact analyticOnNhd_of_complexSmoothOn _ hU happrox.contDiffOn
  refine ⟨U,hU,hUc,hreal,hUV,hsum,?_,?_⟩
  · intro n ψ hψ
    exact analyticAt_const.mul (hanalytic n ψ hψ)
  · intro φ hφ
    obtain ⟨T,hT,hφT,hTU,hconv⟩ := huniform φ hφ
    refine ⟨T,hT,hφT,hTU,?_⟩
    intro n
    exact (-(4/(2*Real.pi):ℂ) • ContinuousLinearMap.id ℂ ℂ).uniformContinuous.comp_tendstoUniformlyOn (hconv n)

end NLS.ZakharovShabat
