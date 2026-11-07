import NLS.Articles.KdVPseudomeasures.OriginalHillClassicalSolutionAdapter

/-! Uniqueness and universal rough compact-time approximation for arbitrary
jointly smooth real mean-zero classical space-time solutions. There is no
assumption of strong Sobolev time differentiability or a coordinate ODE. -/
noncomputable section
open Set Complex MeasureTheory Filter Topology NLS.KdV NLS.WeightedCoeff NLS.Fourier NLS.ZakharovShabat
open scoped ContDiff ComplexConjugate
namespace NLS.Articles.KdVPseudomeasures

theorem tendstoUniformlyOn_hillClassicalSmoothSolutions
    {ι : Type*} {l : Filter ι} (T : ℝ) (f : ι → ℝ × ℝ → ℂ)
    (hf : ∀ j, ContDiff ℝ ∞ (f j))
    (hp : ∀ j t, Function.Periodic (fun x => f j (t, x)) 1)
    (hr : ∀ j t x, conj (f j (t, x)) = f j (t, x))
    (h0 : ∀ j t, (∫ x in (0 : ℝ)..1, f j (t, x)) = 0)
    (hPDE : ∀ j t x, HasDerivAt (fun r => f j (r, x))
      (classicalKdVVectorField (fun y => f j (t, y)) x) t)
    (q : HillRealMeanZeroSource)
    (hinit : Tendsto (fun j => hillIntegerSourceInclusion 4
      (hillClassicalSmoothCurve (f j) (hf j) (hp j) (hr j) (h0 j) 0)) l (𝓝 q)) :
    TendstoUniformlyOn (fun j t => hillIntegerSourceInclusion 4
      (hillClassicalSmoothCurve (f j) (hf j) (hp j) (hr j) (h0 j) t))
      (hillRoughCanonicalKdVFlow q) l (Icc (-T) T) := by
  exact tendstoUniformlyOn_hillSmoothStrongKdVSolution_of_rough_initial_convergence T _
    (fun j => hillClassicalSmoothCurve_is_strong (f j) (hf j) (hp j) (hr j) (h0 j) (hPDE j)) q hinit

theorem hillClassicalSmoothSolutions_eq_of_initial_eq
    (f g : ℝ × ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hpf : ∀ t, Function.Periodic (fun x => f (t, x)) 1)
    (hpg : ∀ t, Function.Periodic (fun x => g (t, x)) 1)
    (hrf : ∀ t x, conj (f (t, x)) = f (t, x))
    (hrg : ∀ t x, conj (g (t, x)) = g (t, x))
    (h0f : ∀ t, (∫ x in (0 : ℝ)..1, f (t, x)) = 0)
    (h0g : ∀ t, (∫ x in (0 : ℝ)..1, g (t, x)) = 0)
    (hPDEf : ∀ t x, HasDerivAt (fun r => f (r, x))
      (classicalKdVVectorField (fun y => f (t, y)) x) t)
    (hPDEg : ∀ t x, HasDerivAt (fun r => g (r, x))
      (classicalKdVVectorField (fun y => g (t, y)) x) t)
    (hinit : ∀ x, f (0, x) = g (0, x)) : f = g := by
  have hi : hillClassicalSmoothCurve f hf hpf hrf h0f 0 =
      hillClassicalSmoothCurve g hg hpg hrg h0g 0 := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    funext k
    rw [hillClassicalSmoothCurve_coefficients, hillClassicalSmoothCurve_coefficients,
      funext hinit]
  funext p
  rw [hillClassicalSmoothSolution_physical_eq_canonicalFlow f hf hpf hrf h0f hPDEf,
    hillClassicalSmoothSolution_physical_eq_canonicalFlow g hg hpg hrg h0g hPDEg, hi]

end NLS.Articles.KdVPseudomeasures
