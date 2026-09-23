import NLS.ZakharovShabat.FiniteSourceRealization
import NLS.ZakharovShabat.ClassicalBoundaryInterlacing
import NLS.ZakharovShabat.ExponentSourcePotentials

/-! # Indexed boundary interlacing for finite source Fourier input
The common continuous physical representative proves the Hilbert case.
Exponent compatibility then gives the same signed-index inequalities for
finite Fourier input in every finite source exponent greater than one.
-/

noncomputable section
open Set Complex
open scoped ENNReal ComplexConjugate
namespace NLS.ZakharovShabat

/-- Every real-type finite source boundary root lies in its original periodic gap at p=2. -/
theorem canonicalPeriodOneBoundaryRoots_mem_gap_finite_two (b : BoundaryCondition)
    (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) (ha : ∀ n, a.2 n = conj (a.1 (-n))) (n : ℤ) :
    (canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) b (CoeffPair.ofFinsupp (p := 2) a) n).re ∈
      Icc (canonicalPeriodicLeft (by simp) (by norm_num) (periodOnePotential (CoeffPair.ofFinsupp (p := 2) a))
        (periodOnePotential_mem _) n).re
      (canonicalPeriodicRight (by simp) (by norm_num) (periodOnePotential (CoeffPair.ofFinsupp (p := 2) a))
        (periodOnePotential_mem _) n).re := by
  have hr : IsRealType (CoeffPair.toMax 2 (CoeffPair.ofFinsupp a)) := ha
  obtain ⟨hp, hb⟩ := finiteSource_physical_compatibility a
  exact canonicalBoundaryRoots_mem_gap_of_continuous b
    ⟨periodOnePotential (CoeffPair.ofFinsupp a), periodOnePotential_mem _⟩
    (isRealType_periodOnePotential _ hr)
    (periodOneBoundaryPotential (by simp) (by norm_num) (CoeffPair.ofFinsupp a))
    (isRealType_periodOneBoundaryPotential (by simp) (by norm_num) _ hr)
    (finiteSourceCurve a) hp hb (finiteSourceCurve_realType a ha) n

/-- Both original periodic endpoints of fixed finite input agree across exponents. -/
theorem canonicalPeriodicEndpoints_finite_exponent {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hp1 : 1 < p) (hq1 : 1 < q) (h : p ≤ q)
    (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) :
    canonicalPeriodicLeft hp hp1 (periodOnePotential (CoeffPair.ofFinsupp (p := p) a)) (periodOnePotential_mem _) =
      canonicalPeriodicLeft hq hq1 (periodOnePotential (CoeffPair.ofFinsupp (p := q) a)) (periodOnePotential_mem _) ∧
    canonicalPeriodicRight hp hp1 (periodOnePotential (CoeffPair.ofFinsupp (p := p) a)) (periodOnePotential_mem _) =
      canonicalPeriodicRight hq hq1 (periodOnePotential (CoeffPair.ofFinsupp (p := q) a)) (periodOnePotential_mem _) := by
  have he := canonicalPeriodicEndpoints_periodOne_exponent hp hq hp1 hq1 h
    (CoeffPair.ofFinsupp (p := p) a)
  have hs := CoeffPair.exponentInclusion_ofFinsupp h a
  exact ⟨he.1.trans (congrArg (fun ψ : CoeffPair q =>
    canonicalPeriodicLeft hq hq1 (periodOnePotential ψ) (periodOnePotential_mem ψ)) hs),
    he.2.trans (congrArg (fun ψ : CoeffPair q =>
      canonicalPeriodicRight hq hq1 (periodOnePotential ψ) (periodOnePotential_mem ψ)) hs)⟩

/-- Every real-type finite source boundary root retains its gap index at any finite p>1. -/
theorem canonicalPeriodOneBoundaryRoots_mem_gap_finite {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition)
    (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) (ha : ∀ n, a.2 n = conj (a.1 (-n))) (n : ℤ) :
    (canonicalPeriodOneBoundaryRoots hp hp1 b (CoeffPair.ofFinsupp (p := p) a) n).re ∈
      Icc (canonicalPeriodicLeft hp hp1 (periodOnePotential (CoeffPair.ofFinsupp (p := p) a))
        (periodOnePotential_mem _) n).re
      (canonicalPeriodicRight hp hp1 (periodOnePotential (CoeffPair.ofFinsupp (p := p) a))
        (periodOnePotential_mem _) n).re := by
  have htwo := canonicalPeriodOneBoundaryRoots_mem_gap_finite_two b a ha n
  rcases le_total p 2 with h | h
  · have hb := canonicalPeriodOneBoundaryRoots_exponent hp (by simp) hp1 (by norm_num) h b
      (CoeffPair.ofFinsupp (p := p) a)
    have he := canonicalPeriodicEndpoints_finite_exponent hp (by simp) hp1 (by norm_num) h a
    simp only [CoeffPair.exponentInclusion_ofFinsupp] at hb
    rw [hb, he.1, he.2]
    exact htwo
  · have hb := canonicalPeriodOneBoundaryRoots_exponent (by simp) hp (by norm_num) hp1 h b
      (CoeffPair.ofFinsupp (p := 2) a)
    have he := canonicalPeriodicEndpoints_finite_exponent (by simp) hp (by norm_num) hp1 h a
    simp only [CoeffPair.exponentInclusion_ofFinsupp] at hb
    rw [← hb, ← he.1, ← he.2]
    exact htwo

end NLS.ZakharovShabat
