import NLS.ZakharovShabat.SourcePsiFullProductInterpolation
import NLS.ZakharovShabat.SourcePsiFullProductGapZeros
import NLS.ZakharovShabat.SourceAngularBetaRegularAnalytic

/-! # Interpolation from opposite boundary-root values

A real full-product variation whose values at the Dirichlet and Neumann
roots are opposite has a zero in each real periodic gap. Full-product
interpolation then forces the direction to vanish.
-/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Opposite real values at two boundary roots give a zero in their periodic gap. -/
theorem exists_zero_in_sourcePeriodicSegment_of_opposite_boundary_values
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (F : ℂ → ℂ)
    (hF : Continuous F) (hreal : ∀ x : ℝ, (F (x : ℂ)).im = 0) (n : ℤ)
    (hop : F (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ n) =
      -F (canonicalPeriodOneBoundaryRoots hp hp1 .neumann φ n)) :
    ∃ z ∈ sourcePeriodicSegment hp hp1 φ n, F z = 0 := by
  let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ n
  let ν := canonicalPeriodOneBoundaryRoots hp hp1 .neumann φ n
  have hμ := canonicalPeriodOneBoundaryRoots_mem_sourcePeriodicSegment_of_realType hp hp1 .dirichlet φ hφ n
  have hν := canonicalPeriodOneBoundaryRoots_mem_sourcePeriodicSegment_of_realType hp hp1 .neumann φ hφ n
  have hs : IsPreconnected (sourcePeriodicSegment hp hp1 φ n) :=
    (convex_segment _ _).isPreconnected
  have hc : ContinuousOn (fun z : ℂ => (F z).re) (sourcePeriodicSegment hp hp1 φ n) :=
    (Complex.continuous_re.comp hF).continuousOn
  have he : (F μ).re = -(F ν).re := by
    simpa only [neg_re] using congrArg Complex.re hop
  have hz : ∃ z ∈ sourcePeriodicSegment hp hp1 φ n, (F z).re = 0 := by
    by_cases hm : (F μ).re ≤ 0
    · exact hs.intermediate_value hμ hν hc ⟨hm, by linarith⟩
    · exact hs.intermediate_value hν hμ hc ⟨by linarith, le_of_lt (lt_of_not_ge hm)⟩
  obtain ⟨z,hz,hzero⟩ := hz
  refine ⟨z,hz,Complex.ext hzero ?_⟩
  have him := sourcePeriodicSegment_im_eq_zero_of_realType hp hp1 φ hφ n z hz
  have hez : (z.re : ℂ) = z := Complex.ext rfl (by simpa using him.symm)
  simpa only [hez, zero_im] using hreal z.re

/-- A full real root variation with opposite Dirichlet/Neumann values vanishes. -/
theorem sourcePsiFullProductVariation_direction_zero_of_opposite_boundary_values
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (a h : Coeff p)
    (ha : a ∈ sourcePeriodicGapRootSet hp hp1 φ)
    (hr : ∀ n : ℤ, (displacedRoots a n).im = 0)
    (hh : ∀ n : ℤ, (h n).im = 0)
    (hop : ∀ n : ℤ,
      sourcePsiFullProductVariation a h (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ n) =
        -sourcePsiFullProductVariation a h (canonicalPeriodOneBoundaryRoots hp hp1 .neumann φ n)) :
    h = 0 := by
  have hzero (n : ℤ) : ∃ z ∈ sourcePeriodicSegment hp hp1 φ n,
      sourcePsiFullProductVariation a h z = 0 :=
    exists_zero_in_sourcePeriodicSegment_of_opposite_boundary_values hp hp1 φ hφ
      (sourcePsiFullProductVariation a h)
      (continuousOn_univ.mp (analyticOnNhd_sourcePsiFullProductVariation hp hp1 a h).continuousOn)
      (sourcePsiFullProductVariation_im_eq_zero_of_real_data hp hp1 a h hr hh) n (hop n)
  choose ρ hρ hz using hzero
  exact sourcePsiFullProductVariation_direction_zero_of_gapZero_sequence hp hp1 φ hφ ρ
    (memℓp_sourcePeriodicSegment_samples hp hp1 φ ρ hρ) hρ a h ha hz

end NLS.ZakharovShabat
