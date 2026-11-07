import NLS.Articles.KdVPseudomeasures.SpectralChainJets
import NLS.KdV.PseudomeasureMultiplicityOrder

/-!
# Physical multiplicity and actual determinant order on original source spaces

These statements identify the full original operator's algebraic multiplicity,
not just its geometric eigenspace dimension. Every original H1 chain domain
and the source's exact original endpoint norm are retained.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal Matrix.Norms.Elementwise Classical
namespace NLS.Articles.KdVPseudomeasures
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue NLS.KdV NLS.ComplexAnalysis

/-- Every actual finite original root-space level is linearly equivalent to
the corresponding actual effective-matrix formal Taylor kernel. -/
def sourceHillRootTaylorKernelEquiv (r : ℝ) (hr : AdmissiblePredualOrder r)
    (n : ℕ) (hn : 1 ≤ n) (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2)
    (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (hd : sourceEndpointDeterminant r hr n (q,z) = 0)
    (p : FormalMultilinearSeries ℂ ℂ (Matrix (Fin 2) (Fin 2) ℂ))
    (hp : HasFPowerSeriesAt
      (endpointReducedMatrixSpectral r hr.1 hr.2 n (sourceEndpointCoefficients r q) z) p 0) (N : ℕ) :
    singularHillRootSpace (sourceComplexHminusOne r hr q) z N ≃ₗ[ℂ]
      LinearMap.ker (matrixTaylorJetMap (matrixFormalTaylor p) N) := by
  have hi := sourceEndpointDeterminant_zero_interior r hr n hn q hs z hz hd
  have hsE : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖sourceEndpointCoefficients r q‖ ≤ 1/2 := by
    simpa only [norm_sourceEndpointCoefficients] using hs
  rw [← sourceEndpointCoefficients_HminusOne_complex r hr q]
  exact (singularHillChainRootEquiv _ z N).symm.trans
    (endpointChainTaylorKernelEquiv r hr.1 hr.2 n hn (sourceEndpointCoefficients r q) z hsE p hp N hi)

/-- The actual physical source multiplicity equals the actual determinant
order on the full closed corrected strip, including repeated eigenvalues. -/
theorem sourceHillAlgebraicMultiplicity_eq_analyticOrderAt (r : ℝ) (hr : AdmissiblePredualOrder r)
    (n : ℕ) (hn : 1 ≤ n) (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2)
    (z : ℂ) (hz : z ∈ reducedHillStrip n) :
    (sourceHillAlgebraicMultiplicity r hr q z : ℕ∞) =
      analyticOrderAt (fun y => sourceEndpointDeterminant r hr n (q,y)) z := by
  have hsE : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖sourceEndpointCoefficients r q‖ ≤ 1/2 := by
    simpa only [norm_sourceEndpointCoefficients] using hs
  rw [sourceHillAlgebraicMultiplicity_eq]
  exact endpointHillAlgebraicMultiplicity_eq_analyticOrderAt r hr.1 hr.2 n hn
    (sourceEndpointCoefficients r q) hsE z hz

/-- Equality also holds for natural multiplicities, with no finite-order premise supplied by a caller. -/
theorem sourceHillAlgebraicMultiplicity_eq_analyticOrderNatAt (r : ℝ) (hr : AdmissiblePredualOrder r)
    (n : ℕ) (hn : 1 ≤ n) (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2)
    (z : ℂ) (hz : z ∈ reducedHillStrip n) :
    sourceHillAlgebraicMultiplicity r hr q z =
      analyticOrderNatAt (fun y => sourceEndpointDeterminant r hr n (q,y)) z := by
  simpa only [ENat.toNat_natCast, analyticOrderNatAt] using congrArg ENat.toNat
    (sourceHillAlgebraicMultiplicity_eq_analyticOrderAt r hr n hn q hs z hz)

/-- The corrected strip contains exactly two eigenvalues of the original
physical operator counted with its actual algebraic multiplicities. -/
theorem sourceHill_strip_algebraic_count_two (r : ℝ) (hr : AdmissiblePredualOrder r)
    (n : ℕ) (hn : 1 ≤ n) (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2) :
    (∑ᶠ z : ℂ, if z ∈ reducedHillStrip n then sourceHillAlgebraicMultiplicity r hr q z else 0) = 2 := by
  have hsE : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖sourceEndpointCoefficients r q‖ ≤ 1/2 := by
    simpa only [norm_sourceEndpointCoefficients] using hs
  simpa only [sourceHillAlgebraicMultiplicity_eq r hr q] using
    endpointHill_strip_algebraic_count_two r hr.1 hr.2 n hn (sourceEndpointCoefficients r q) hsE

/-- One cutoff, chosen before the potential on every exact original norm
ball, gives both the full multiplicity correspondence and physical two-count. -/
theorem sourceLemma2_11_uniform_algebraic_count (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ) :
    ∃ M : ℕ, 1 ≤ M ∧ ∀ q : FourierLebesgueSpace (2:ℝ) (-r) ⊤, ‖q‖ ≤ R →
      ∀ (n : ℕ) (_hn : 1 ≤ n), M ≤ n →
        (∀ z ∈ reducedHillStrip n, (sourceHillAlgebraicMultiplicity r hr q z : ℕ∞) =
          analyticOrderAt (fun y => sourceEndpointDeterminant r hr n (q,y)) z) ∧
        (∑ᶠ z : ℂ, if z ∈ reducedHillStrip n then sourceHillAlgebraicMultiplicity r hr q z else 0) = 2 := by
  obtain ⟨M,hM,hcut⟩ := exists_endpointHill_cutoff r hr.2 R
  refine ⟨M,hM,?_⟩
  intro q hq n hn hnM
  have hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2 :=
    (mul_le_mul_of_nonneg_left hq (mul_nonneg (endpointHillConstant_pos r hr.2).le
      (Real.rpow_nonneg (by positivity) _))).trans (hcut n hnM)
  exact ⟨fun z hz => sourceHillAlgebraicMultiplicity_eq_analyticOrderAt r hr n hn q hs z hz,
    sourceHill_strip_algebraic_count_two r hr n hn q hs⟩

end NLS.Articles.KdVPseudomeasures
