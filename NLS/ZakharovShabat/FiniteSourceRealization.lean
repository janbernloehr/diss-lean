import NLS.Fourier.FinitePeriodOneRealization
import NLS.SequenceSpaces.FiniteSourceCoefficients
import NLS.ZakharovShabat.ClassicalIntervalEigenvalues
import NLS.ZakharovShabat.PeriodOneEmbedding
import NLS.ZakharovShabat.PeriodOneBoundaryAsymptotics
import NLS.ZakharovShabat.RealType
import NLS.FunctionalAnalysis.LinearVolterra

/-! # Common physical representatives for finite source potentials
The original periodic potential and the reflected ordinary boundary potential
have the same finite Fourier polynomial on the unit interval. Its restriction
is a continuous Volterra curve, with pointwise real type for real-type input.
-/

noncomputable section
open Set Complex MeasureTheory
open NLS.Fourier NLS.LinearVolterra
open scoped ENNReal ComplexConjugate
namespace NLS.ZakharovShabat

/-- Finite source polynomials restricted to the unit interval. -/
def finiteSourceCurve (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) : Curve (ℂ × ℂ) :=
  ⟨fun t => BoundaryCondition.periodOnePair a t,
    (BoundaryCondition.continuous_periodOnePair a).comp continuous_subtype_val⟩

/-- Constant extension recovers the original polynomial throughout the unit interval. -/
theorem extend_finiteSourceCurve (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) (x : ℝ) (hx : x ∈ Icc 0 1) :
    extend (finiteSourceCurve a) x = BoundaryCondition.periodOnePair a x :=
  extend_coe (finiteSourceCurve a) ⟨x,hx⟩

/-- The original periodic coefficient potential reconstructs the finite source on the whole period. -/
theorem physicalBase_periodOnePotential_finite (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) :
    physicalBase (periodOnePotential (CoeffPair.ofFinsupp (p := 2) a))
      =ᵐ[volume.restrict (Ioc 0 2)] BoundaryCondition.periodOnePair a := by
  filter_upwards [circlePullback_periodDouble_ofFinsupp a.1,
    circlePullback_periodDouble_ofFinsupp a.2] with x h₁ h₂
  exact Prod.ext h₁ h₂

/-- The finite ordinary source extension is the original physical Dirichlet potential. -/
theorem periodOneBoundaryPotential_finite_eq (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ))
    (ha : MemLp (BoundaryCondition.periodOnePair a) 2 (volume.restrict (Ioc 0 1))) :
    (periodOneBoundaryPotential (by simp) (by norm_num) (CoeffPair.ofFinsupp (p := 2) a)).val =
      BoundaryCondition.dirichletPotentialCoefficients (BoundaryCondition.periodOnePair a) ha := by
  change BoundaryCondition.intervalExtensionCLM .dirichlet (by norm_num) (by simp)
    (BoundaryCondition.finitePairCoeffs a) = _
  rw [BoundaryCondition.intervalExtensionCLM_finite]
  apply Prod.ext
  · ext n
    exact (BoundaryCondition.finiteIntervalExtension_coefficient_fst .dirichlet (by norm_num) a n).symm
  · ext n
    exact (BoundaryCondition.finiteIntervalExtension_coefficient_snd .dirichlet (by norm_num) a n).symm

/-- Both original realizations share the continuous finite source curve on the unit interval. -/
theorem finiteSource_physical_compatibility (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) :
    (physicalBase (periodOnePotential (CoeffPair.ofFinsupp (p := 2) a))
      =ᵐ[volume.restrict (Ioc 0 1)] extend (finiteSourceCurve a)) ∧
    (physicalBase (periodOneBoundaryPotential (by simp) (by norm_num)
      (CoeffPair.ofFinsupp (p := 2) a)).val
      =ᵐ[volume.restrict (Ioc 0 1)] extend (finiteSourceCurve a)) := by
  have he : BoundaryCondition.periodOnePair a =ᵐ[volume.restrict (Ioc 0 1)]
      extend (finiteSourceCurve a) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact (extend_finiteSourceCurve a x (Ioc_subset_Icc_self hx)).symm
  have hp : physicalBase (periodOnePotential (CoeffPair.ofFinsupp (p := 2) a))
      =ᵐ[volume.restrict (Ioc 0 1)] BoundaryCondition.periodOnePair a :=
    ae_restrict_of_ae_restrict_of_subset
    (Ioc_subset_Ioc_right (show (1 : ℝ) ≤ 2 by norm_num)) (physicalBase_periodOnePotential_finite a)
  have ha : MemLp (BoundaryCondition.periodOnePair a) 2 (volume.restrict (Ioc 0 1)) :=
    memLp_prod_iff.mpr ⟨memLp_two_interval (continuous_polynomial a.1) 0 1 (by norm_num),
      memLp_two_interval (continuous_polynomial a.2) 0 1 (by norm_num)⟩
  refine ⟨hp.trans he, ?_⟩
  rw [periodOneBoundaryPotential_finite_eq a ha]
  exact (BoundaryCondition.physicalBase_dirichletPotentialCoefficients_restrict _ ha).trans he

/-- Real-type finite coefficients give a pointwise real-type physical curve. -/
theorem finiteSourceCurve_realType (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ))
    (ha : ∀ n, a.2 n = conj (a.1 (-n))) :
    ∀ t, (finiteSourceCurve a t).2 = conj (finiteSourceCurve a t).1 :=
  fun t => polynomial_conj_of_coefficients a.1 a.2 ha t

/-- The original periodic source embedding preserves real type at every Banach exponent. -/
theorem isRealType_periodOnePotential {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) : IsRealType (periodOnePotential φ) := by
  intro n
  change Coeff.periodDouble φ.snd n = conj (Coeff.periodDouble φ.fst (-n))
  by_cases hn : n % 2 = 0
  · have he : n = 2*(n/2) := by omega
    rw [he, show -(2*(n/2)) = 2*(-(n/2)) by ring, Coeff.periodDouble_even, Coeff.periodDouble_even]
    exact hφ (n/2)
  · have he : n = 2*(n/2)+1 := by omega
    have hm : -(2*(n/2)+1) = 2*(-(n/2)-1)+1 := by ring
    rw [he, hm, Coeff.periodDouble_odd, Coeff.periodDouble_odd, map_zero]

end NLS.ZakharovShabat
