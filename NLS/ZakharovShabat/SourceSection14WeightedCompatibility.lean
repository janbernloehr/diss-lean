import NLS.ZakharovShabat.SourceBirkhoffWeightedComplexExponent
import NLS.ZakharovShabat.SourceBirkhoffWeightedRealAnalytic
import NLS.ZakharovShabat.SourceBirkhoffWeightedJacobianInjective

/-! # Constructed weighted analytic maps and exponent compatibility

Actual Section 14 constructions give native weighted real analyticity and
injective weighted Jacobians for every spectral weight. Independently chosen
families at two finite exponents agree on their entire complex intersection,
and their full bounded derivatives commute with the same inclusions.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- One actual family gives full real weighted analyticity and derivative injectivity for all weights. -/
theorem sourceSection14_weighted_real_analytic (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W₀ B W : Set (CoeffPair p), ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
      ∃ D : SourceSection14Data hp hp1 W₀ B W s, ∀ w : SpectralWeight,
        AnalyticOnNhd ℝ (D.complex.originalWeightedRealMap w) univ ∧
        ∀ a : weightedRealSourceSubmodule (p := p) w,
          Function.Injective (fderiv ℂ (originalWeightedBirkhoffMap hp hp1 s w) a.val) := by
  obtain ⟨W₀,B,W,s,D⟩ := sourceSection14 hp hp1
  exact ⟨W₀,B,W,s,D,fun w => ⟨D.complex.originalWeightedRealMap_analytic w,
    D.complex.originalWeightedBirkhoffMap_fderiv_injective w⟩⟩

/-- Constructed domains and full map/derivative compatibility at two exponents, uniformly in the weight. -/
theorem sourceSection14_weighted_complex_compatible
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hq : q ≠ ⊤) (hq1 : 1 < q) (hpq : p ≤ q) :
    ∃ W₀ B W : Set (CoeffPair p), ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
      ∃ D : SourceSection14Data hp hp1 W₀ B W s,
        ∃ A C V : Set (CoeffPair q), ∃ t : (n : ℤ) → CoeffPair q → DeletedCoeff q n,
          ∃ E : SourceSection14Data hq hq1 A C V t, ∀ w : SpectralWeight,
            IsOpen (D.complex.originalWeightedComplexDomain w) ∧
            (∀ a : weightedRealSourceSubmodule (p := p) w,
              a.val ∈ D.complex.originalWeightedComplexDomain w) ∧
            AnalyticOnNhd ℂ (originalWeightedBirkhoffMap hp hp1 s w) (D.complex.originalWeightedComplexDomain w) ∧
            IsOpen (E.complex.originalWeightedComplexDomain w) ∧
            (∀ a : weightedRealSourceSubmodule (p := q) w,
              a.val ∈ E.complex.originalWeightedComplexDomain w) ∧
            AnalyticOnNhd ℂ (originalWeightedBirkhoffMap hq hq1 t w) (E.complex.originalWeightedComplexDomain w) ∧
            ∀ a ∈ D.complex.originalWeightedComplexDomain w,
              WeightedCoeffPair.exponentInclusion (sourceFrequencyWeight w) hpq a ∈ E.complex.originalWeightedComplexDomain w →
              WeightedCoeffPair.exponentInclusion (sourceFrequencyWeight w) hpq (originalWeightedBirkhoffMap hp hp1 s w a) =
                originalWeightedBirkhoffMap hq hq1 t w (WeightedCoeffPair.exponentInclusion (sourceFrequencyWeight w) hpq a) ∧
              (WeightedCoeffPair.exponentInclusion (sourceFrequencyWeight w) hpq).comp
                (fderiv ℂ (originalWeightedBirkhoffMap hp hp1 s w) a) =
                  (fderiv ℂ (originalWeightedBirkhoffMap hq hq1 t w)
                    (WeightedCoeffPair.exponentInclusion (sourceFrequencyWeight w) hpq a)).comp
                    (WeightedCoeffPair.exponentInclusion (sourceFrequencyWeight w) hpq) := by
  obtain ⟨W₀,B,W,s,D⟩ := sourceSection14 hp hp1
  obtain ⟨A,C,V,t,E⟩ := sourceSection14 hq hq1
  refine ⟨W₀,B,W,s,D,A,C,V,t,E,fun w => ?_⟩
  have hd := D.complex.originalWeightedComplexDomain_spec w
  have he := E.complex.originalWeightedComplexDomain_spec w
  exact ⟨hd.1,hd.2.1,hd.2.2.1,he.1,he.2.1,he.2.2.1,fun a ha ha' =>
    ⟨D.weighted_complex_exponent E w hpq a ha ha',D.weighted_complex_fderiv_exponent E w hpq a ha ha'⟩⟩

end NLS.ZakharovShabat
