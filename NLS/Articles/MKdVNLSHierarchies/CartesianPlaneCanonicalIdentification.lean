import NLS.MKdV.MiuraCartesianPlaneCanonical

/-! # Actual Gardner fields and the canonical bracket in each Cartesian plane

Every selected Cartesian gradient has a genuine L2 spatial derivative
on the original real H1 domain. The actual plane brackets have their
canonical values, including at closed gaps. Cross-mode zero brackets,
the full infinite-dimensional inverse and the independent angle system
remain separate obligations.
-/
noncomputable section
open Set Complex NLS.MKdV NLS.Poisson NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.Articles.MKdVNLSHierarchies

theorem physical_Cartesian_actual_Gardner_fields (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (hn : 1 ≤ n)
    (P : (ℂ × ℂ) →L[ℂ] ℂ) :
    TemperedDistribution.derivCLM ℂ
        (NLS.Fourier.periodOneL2Distribution (l2ScalarGradient (miuraCartesianObservable n P) (scalarInclusion a))) =
      NLS.Fourier.periodOneL2Distribution
        (l2GardnerDirection (miuraCartesianObservable n P) (scalarInclusion a)) :=
  miuraCartesianObservable_Gardner_distribution a ha n hn P

theorem physical_Cartesian_plane_Gardner_brackets (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (hn : 1 ≤ n) :
    l2GardnerBracket (miuraCartesianX n) (miuraCartesianX n) (scalarInclusion a) = 0 ∧
    l2GardnerBracket (miuraCartesianX n) (miuraCartesianY n) (scalarInclusion a) = 1 ∧
    l2GardnerBracket (miuraCartesianY n) (miuraCartesianX n) (scalarInclusion a) = -1 ∧
    l2GardnerBracket (miuraCartesianY n) (miuraCartesianY n) (scalarInclusion a) = 0 := by
  refine ⟨miuraCartesianGardnerBracket_self a ha n hn (ContinuousLinearMap.fst ℂ ℂ ℂ),
    miuraCartesianPlane_Gardner_canonical a ha n hn,?_,
      miuraCartesianGardnerBracket_self a ha n hn (ContinuousLinearMap.snd ℂ ℂ ℂ)⟩
  have h := miuraCartesianGardnerBracket_antisymm a ha n n hn hn
    (ContinuousLinearMap.snd ℂ ℂ ℂ) (ContinuousLinearMap.fst ℂ ℂ ℂ)
  change l2GardnerBracket (miuraCartesianY n) (miuraCartesianX n) (scalarInclusion a) =
    -l2GardnerBracket (miuraCartesianX n) (miuraCartesianY n) (scalarInclusion a) at h
  rwa [miuraCartesianPlane_Gardner_canonical a ha n hn] at h

theorem physical_Cartesian_Gardner_bracket_analytic_extension (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (P Q : (ℂ × ℂ) →L[ℂ] ℂ) :
    AnalyticAt ℂ (miuraCartesianGardnerBracketExtension m n P Q) a ∧
      miuraCartesianGardnerBracketExtension m n P Q a =
        l2GardnerBracket (miuraCartesianObservable m P) (miuraCartesianObservable n Q) (scalarInclusion a) :=
  ⟨analyticAt_miuraCartesianGardnerBracketExtension a ha m n hm hn P Q,
    miuraCartesianGardnerBracketExtension_eq_actual a ha m n hn P Q⟩

end NLS.Articles.MKdVNLSHierarchies
