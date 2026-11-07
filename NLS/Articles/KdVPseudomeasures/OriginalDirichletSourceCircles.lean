import NLS.Articles.KdVPseudomeasures.OriginalDirichletRiesz
import NLS.KdV.HminusOneDirichletSourceCircles

/-! The literal source Dirichlet circles are valid isolating contours
UNIFORMLY on an open neighborhood in the ORIGINAL complex H^-1 norm.
The entire original distribution and every original positive index are retained. -/
noncomputable section
open Set Complex Metric
namespace NLS.Articles.KdVPseudomeasures
open NLS.KdV NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

/-- Source equation (6) has a locally uniform o(n) error on the full complex
original distribution domain, with one common cutoff for all nearby sources. -/
theorem exists_uniform_small_originalComplexDirichletDisplacement
    (q : OriginalComplexHminusOnePotential) {delta : ℝ} (hd : 0 < delta) :
    ∃ N : ℕ, ∃ U : Set (FourierLebesgueSpace (2:ℝ) (-1) 2),
      0 < N ∧ IsOpen U ∧ q.val ∈ U ∧
      ∀ a : OriginalComplexHminusOnePotential, a.val ∈ U →
        ∀ n : ℕ+, N < (n:ℕ) →
          ‖originalComplexDirichletLabels a n-((Real.pi:ℂ)*(n:ℕ))^2‖ < delta*(n:ℝ) := by
  let F := periodOneOriginalExtract
  obtain ⟨N,V,hN,hV,hqV,he⟩ :=
    exists_uniform_small_hillHminusDirichletDisplacement (F q.val) hd
  exact ⟨N,F ⁻¹' V,hN,hV.preimage F.continuous,hqV,fun a ha n hn => he (F a.val) ha n hn⟩

/-- ONE original complex H^-1 norm neighborhood makes ALL high source
circles actual resolvent contours. Their closed disks isolate precisely the
same-index original Dirichlet labels, with ACTUAL algebraic multiplicity one.
All high labels have analytic extensions to that SAME open norm neighborhood. -/
theorem exists_uniform_originalComplexDirichlet_sourceCircles
    (q : OriginalComplexHminusOnePotential) :
    ∃ N : ℕ, ∃ U : Set (FourierLebesgueSpace (2:ℝ) (-1) 2),
      0 < N ∧ IsOpen U ∧ q.val ∈ U ∧
      (∀ n : ℕ+, N < (n:ℕ) → AnalyticOnNhd ℂ
        (fun a => hillHminusDirichletComplexLabels (periodOneOriginalExtract a) n) U) ∧
      ∀ a : OriginalComplexHminusOnePotential, a.val ∈ U →
        ∀ n : ℕ+, N < (n:ℕ) →
          sphere (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ) ⊆ singularDirichletResolventSet a.val ∧
          originalComplexDirichletLabels a n ∈ ball (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ) ∧
          (∀ z ∈ closedBall (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ),
            z ∈ singularDirichletSpectrum a.val ↔ z = originalComplexDirichletLabels a n) ∧
          singularDirichletAlgebraicMultiplicity a.val (originalComplexDirichletLabels a n) = 1 := by
  let F := periodOneOriginalExtract
  obtain ⟨N,V,hN,hV,hqV,han,hcircle⟩ :=
    exists_uniform_hillHminusDirichlet_sourceCircles (F q.val)
  refine ⟨N,F ⁻¹' V,hN,hV.preimage F.continuous,hqV,?_,?_⟩
  · intro n hn a ha
    exact (han n hn (F a) ha).comp (f := F) (F.analyticAt a)
  · intro a ha n hn
    have h := hcircle (F a.val) ha n hn
    change (sphere (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ) ⊆
      singularDirichletResolventSet (periodOneOriginal (periodOneOriginalExtract a.val))) ∧
      originalComplexDirichletLabels a n ∈ ball (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ) ∧
      (∀ z ∈ closedBall (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ),
        z ∈ singularDirichletSpectrum (periodOneOriginal (periodOneOriginalExtract a.val)) ↔
          z = originalComplexDirichletLabels a n) ∧
      singularDirichletAlgebraicMultiplicity (periodOneOriginal (periodOneOriginalExtract a.val))
        (originalComplexDirichletLabels a n) = 1 at h
    rw [originalComplexDirichlet_distribution a] at h
    exact h

end NLS.Articles.KdVPseudomeasures
