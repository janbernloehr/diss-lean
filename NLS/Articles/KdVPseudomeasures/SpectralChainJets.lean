import NLS.Articles.KdVPseudomeasures.SpectralMultiplicity
import NLS.Articles.KdVPseudomeasures.SpectralReconstruction
import NLS.KdV.PseudomeasureChainJets

/-!
# Original physical finite chains and their reduced Taylor conditions

Every coefficient belongs to the original H1 domain. The finite chain spaces
have the exact actual physical root-space dimensions, and their two-mode jets
are injective and annihilated by the reduced pencil to the retained order.
Surjectivity onto the formal matrix Taylor kernel is not asserted here.
-/
noncomputable section
open Filter Topology
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue NLS.KdV NLS.FunctionalAnalysis

/-- Original source finite H1 coefficient chains are linearly equivalent to
the actual physical root-space level, through the same original final vector. -/
def sourceHillChainRootEquiv (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (z : ℂ) (N : ℕ) :
    singularHillChainSpace (sourceComplexHminusOne r hr q) z N ≃ₗ[ℂ]
      singularHillRootSpace (sourceComplexHminusOne r hr q) z N :=
  singularHillChainRootEquiv (sourceComplexHminusOne r hr q) z N

/-- Every original source finite chain coefficient space is finite dimensional. -/
theorem finiteDimensional_sourceHillChainSpace (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (z : ℂ) (N : ℕ) :
    FiniteDimensional ℂ (singularHillChainSpace (sourceComplexHminusOne r hr q) z N) := by
  rw [← sourceEndpointCoefficients_HminusOne_complex r hr q]
  exact finiteDimensional_endpointHillChainSpace r hr.1 hr.2 (sourceEndpointCoefficients r q) z N

/-- The eventual dimension of original H1 coefficient chains is exactly
the source operator's actual algebraic multiplicity. -/
theorem eventually_finrank_sourceHillChainSpace (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (z : ℂ) :
    ∀ᶠ N : ℕ in atTop,
      Module.finrank ℂ (singularHillChainSpace (sourceComplexHminusOne r hr q) z N) =
        sourceHillAlgebraicMultiplicity r hr q z := by
  have h := eventually_finrank_endpointHillChainSpace r hr.1 hr.2 (sourceEndpointCoefficients r q) z
  filter_upwards [h] with N hN
  rw [sourceHillAlgebraicMultiplicity_eq r hr q z,
    ← sourceEndpointCoefficients_HminusOne_complex r hr q]
  exact hN

/-- At every actual determinant zero, all finite physical chains are
determined by their retained two-mode coefficient vectors. -/
theorem sourceHillChainCoordinates_injective (r : ℝ) (hr : AdmissiblePredualOrder r)
    (n : ℕ) (hn : 1 ≤ n) (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2)
    (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (hd : sourceEndpointDeterminant r hr n (q,z) = 0) (N : ℕ) :
    Function.Injective (singularHillChainCoordinates (sourceComplexHminusOne r hr q) z N n) := by
  have hi := sourceEndpointDeterminant_zero_interior r hr n hn q hs z hz hd
  have hsE : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖sourceEndpointCoefficients r q‖ ≤ 1/2 := by
    simpa only [norm_sourceEndpointCoefficients] using hs
  rw [← sourceEndpointCoefficients_HminusOne_complex r hr q]
  exact endpointHillChainCoordinates_injective r hr.1 hr.2 n hn (sourceEndpointCoefficients r q) z hsE N hi

/-- The actual reduced residual of every original physical N-chain has
zero spectral derivatives at every order below N, at every actual root. -/
theorem sourceHillChain_reduced_derivatives_zero (r : ℝ) (hr : AdmissiblePredualOrder r)
    (n : ℕ) (hn : 1 ≤ n) (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2)
    (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (hd : sourceEndpointDeterminant r hr n (q,z) = 0) (N : ℕ)
    (v : Fin N → FourierLebesgueSpace (2:ℝ) 1 2)
    (hv : v ∈ singularHillChainSpace (sourceComplexHminusOne r hr q) z N)
    (k : ℕ) (hk : k < N) :
    iteratedDeriv k (fun t : ℂ =>
      endpointReducedFamily r hr.1 hr.2 n (sourceEndpointCoefficients r q,z+t)
        (endpointHillH1Coordinates n (pencilChainPolynomial N v t))) 0 = 0 := by
  have hi := sourceEndpointDeterminant_zero_interior r hr n hn q hs z hz hd
  have hsE : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖sourceEndpointCoefficients r q‖ ≤ 1/2 := by
    simpa only [norm_sourceEndpointCoefficients] using hs
  have hvE : v ∈ singularHillChainSpace
      (endpointHillHminusOne SpectralWeight.one r hr.2 (sourceEndpointCoefficients r q)) z N := by
    simpa only [sourceEndpointCoefficients_HminusOne_complex r hr] using hv
  exact endpointHillChain_reduced_derivatives_zero r hr.1 hr.2 n hn
    (sourceEndpointCoefficients r q) z hsE N v hi hvE k hk

/-- The original chain polynomial and its analytic H1 reconstruction have
an explicit analytic remainder divisible by the chain-length power. -/
theorem sourceHillChain_reconstruction_germ (r : ℝ) (hr : AdmissiblePredualOrder r)
    (n : ℕ) (hn : 1 ≤ n) (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2)
    (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (hd : sourceEndpointDeterminant r hr n (q,z) = 0) (N : ℕ)
    (v : Fin N → FourierLebesgueSpace (2:ℝ) 1 2)
    (hv : v ∈ singularHillChainSpace (sourceComplexHminusOne r hr q) z N) :
    ∃ H : ℂ → FourierLebesgueSpace (2:ℝ) 1 2, AnalyticAt ℂ H 0 ∧
      (fun t : ℂ => pencilChainPolynomial N v t -
        sourceEndpointReconstruction r hr n (q,z+t)
          (endpointHillH1Coordinates n (pencilChainPolynomial N v t))) =ᶠ[𝓝 0]
        (fun t : ℂ => t^N • H t) := by
  have hi := sourceEndpointDeterminant_zero_interior r hr n hn q hs z hz hd
  have hsE : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖sourceEndpointCoefficients r q‖ ≤ 1/2 := by
    simpa only [norm_sourceEndpointCoefficients] using hs
  have hvE : v ∈ singularHillChainSpace
      (endpointHillHminusOne SpectralWeight.one r hr.2 (sourceEndpointCoefficients r q)) z N := by
    simpa only [sourceEndpointCoefficients_HminusOne_complex r hr] using hv
  exact ⟨endpointHillChainReconstructionRemainder r hr.1 hr.2 n (sourceEndpointCoefficients r q) z N v,
    analyticAt_endpointHillChainReconstructionRemainder r hr.1 hr.2 n hn
      (sourceEndpointCoefficients r q) z hsE N v hi.le,
    endpointHillChain_reconstruction_germ r hr.1 hr.2 n hn
      (sourceEndpointCoefficients r q) z hsE N v hi hvE⟩

end NLS.Articles.KdVPseudomeasures
