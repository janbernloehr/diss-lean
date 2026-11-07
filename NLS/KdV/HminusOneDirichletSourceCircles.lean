import NLS.KdV.HminusOneDirichletUniformDisplacement
import NLS.KdV.HminusOneDirichletUniformSimplicity

/-! Validity and same-index isolation of the LITERAL source Dirichlet
circles |z-(n*pi)^2|=n, uniformly on original complex H^-1 neighborhoods. -/
noncomputable section
open Set Complex Metric NLS.ComplexAnalysis
namespace NLS.KdV

/-- A uniform high displacement bound and the intrinsic ordering isolate
one actual original label from the ENTIRE native complex spectrum. -/
theorem hillHminusDirichlet_sourceCircle_of_displacement
    (q : PeriodOneHminusOne) (K : ℕ)
    (herr : ∀ m : ℕ+, K < (m:ℕ) →
      ‖hillHminusDirichletComplexLabels q m-((Real.pi:ℂ)*(m:ℕ))^2‖ < (m:ℝ)/4)
    (n : ℕ+) (hn : K+1 < (n:ℕ)) :
    sphere (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ) ⊆ singularDirichletResolventSet (periodOneOriginal q) ∧
      hillHminusDirichletComplexLabels q n ∈ ball (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ) ∧
      ∀ z ∈ closedBall (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ),
        z ∈ singularDirichletSpectrum (periodOneOriginal q) ↔ z = hillHminusDirichletComplexLabels q n := by
  have hmono : Monotone (fun m : ℕ+ => (hillHminusDirichletComplexLabels q m).re) := by
    intro i j hij
    exact re_le_of_complexLexLE (monotone_hillHminusDirichletComplexLabels q hij)
  obtain ⟨hl,hother⟩ := squaredFrequencyCircle_isolates_of_monotone
    (hillHminusDirichletComplexLabels q) hmono K herr n hn
  have hiso (z : ℂ) (hz : z ∈ closedBall (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ))
      (hs : z ∈ singularDirichletSpectrum (periodOneOriginal q)) :
      z = hillHminusDirichletComplexLabels q n := by
    obtain ⟨m,rfl⟩ := (hillHminusDirichletComplexLabels_spectrum_iff q z).mp hs
    by_cases hmn : m = n
    · rw [hmn]
    · exact False.elim ((not_lt.mpr (by simpa only [mem_closedBall,dist_eq_norm] using hz))
        (hother m hmn))
  refine ⟨?_,hl,fun z hz => ⟨hiso z hz,?_⟩⟩
  · intro z hz
    by_contra hr
    have hs : z ∈ singularDirichletSpectrum (periodOneOriginal q) := hr
    have he := hiso z (sphere_subset_closedBall hz) hs
    have hb : z ∈ ball (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ) := he ▸ hl
    exact (ne_of_lt (mem_ball.mp hb)) (mem_sphere.mp hz)
  · rintro rfl
    exact (hillHminusDirichletComplexLabels_spectrum_iff q _).mpr ⟨n,rfl⟩

/-- ONE original complex H^-1 norm neighborhood supports ALL sufficiently
high literal source circles. Each circle is entirely in the actual resolvent,
its closed disk contains exactly its original-index label, that eigenvalue has
actual algebraic multiplicity one, and every high label is analytic on the
SAME neighborhood. No source-circle hypotheses are supplied. -/
theorem exists_uniform_hillHminusDirichlet_sourceCircles (q : PeriodOneHminusOne) :
    ∃ N : ℕ, ∃ V : Set PeriodOneHminusOne,
      0 < N ∧ IsOpen V ∧ q ∈ V ∧
      (∀ n : ℕ+, N < (n:ℕ) →
        AnalyticOnNhd ℂ (fun a => hillHminusDirichletComplexLabels a n) V) ∧
      ∀ a ∈ V, ∀ n : ℕ+, N < (n:ℕ) →
        sphere (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ) ⊆ singularDirichletResolventSet (periodOneOriginal a) ∧
        hillHminusDirichletComplexLabels a n ∈ ball (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ) ∧
        (∀ z ∈ closedBall (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ),
          z ∈ singularDirichletSpectrum (periodOneOriginal a) ↔ z = hillHminusDirichletComplexLabels a n) ∧
        singularDirichletAlgebraicMultiplicity (periodOneOriginal a)
          (hillHminusDirichletComplexLabels a n) = 1 := by
  obtain ⟨K,U,hK,hU,hqU,herror⟩ :=
    exists_uniform_small_hillHminusDirichletDisplacement q (delta := 1/4) (by norm_num)
  obtain ⟨M,W,_,hW,hqW,han,hsimple⟩ :=
    exists_uniform_simple_analytic_hillHminusDirichletComplexLabels q
  let N := max (K+1) M
  let V := U ∩ W
  refine ⟨N,V,by dsimp [N]; omega,hU.inter hW,⟨hqU,hqW⟩,
    fun n hn => (han n ((le_max_right _ _).trans_lt hn)).mono inter_subset_right,?_⟩
  intro a ha n hn
  have he (m : ℕ+) (hm : K < (m:ℕ)) :
      ‖hillHminusDirichletComplexLabels a m-((Real.pi:ℂ)*(m:ℕ))^2‖ < (m:ℝ)/4 := by
    simpa only [one_div,div_eq_mul_inv,one_mul,mul_comm] using herror a ha.1 m hm
  obtain ⟨hc,hl,hiso⟩ := hillHminusDirichlet_sourceCircle_of_displacement a K he n
    ((le_max_left _ _).trans_lt hn)
  exact ⟨hc,hl,hiso,(hsimple a ha.2 n ((le_max_right _ _).trans_lt hn)).1⟩

end NLS.KdV
