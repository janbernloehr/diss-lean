import NLS.FunctionalAnalysis.PencilRootChains
import NLS.KdV.PseudomeasureRootSpaces
import NLS.KdV.PseudomeasureInhomogeneousReduction
import NLS.ComplexAnalysis.PoweredAnalyticJet

/-!
# Finite physical Hill chains and their exact domain polynomials

The chain coefficient vectors retain the original H1 domain and are linearly
equivalent to the actual finite physical root spaces. Their polynomial solves
the full physical pencil with precisely its final, high-order forcing term.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue NLS.FunctionalAnalysis

/-- All N-term root chains of the actual original singular Hill operator. -/
def singularHillChainSpace (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (z : ℂ) (N : ℕ) :
    Submodule ℂ (Fin N → FourierLebesgueSpace (2:ℝ) 1 2) :=
  pencilChainSpace singularHillDomainInclusion.toLinearMap
    (singularHillOperator q-z • singularHillDomainInclusion).toLinearMap N

/-- Every actual chain is linearly identified with its original final root vector. -/
def singularHillChainRootEquiv (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (z : ℂ) (N : ℕ) :
    singularHillChainSpace q z N ≃ₗ[ℂ] singularHillRootSpace q z N :=
  pencilChainRootEquiv singularHillDomainInclusion.toLinearMap
    (singularHillOperator q-z • singularHillDomainInclusion).toLinearMap
      singularHillDomainInclusion_injective N

/-- No dimension is lost by retaining every original H1 coefficient of a finite chain. -/
theorem finrank_singularHillChainSpace (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (z : ℂ) (N : ℕ) :
    Module.finrank ℂ (singularHillChainSpace q z N) =
      Module.finrank ℂ (singularHillRootSpace q z N) :=
  (singularHillChainRootEquiv q z N).finrank_eq

/-- Original H1 chain polynomials are analytic in the full H1 norm. -/
theorem analyticAt_singularHillChainPolynomial (N : ℕ)
    (v : Fin N → FourierLebesgueSpace (2:ℝ) 1 2) (t : ℂ) :
    AnalyticAt ℂ (pencilChainPolynomial N v) t := by
  unfold pencilChainPolynomial
  apply Finset.analyticAt_fun_sum Finset.univ
  intro j _
  exact (analyticAt_id.pow j.val).smul analyticAt_const

/-- A finite physical chain polynomial solves the affine singular pencil
with exactly the Nth-power final forcing term, for every complex increment. -/
theorem singularHillChainPolynomial_pencil (q : FourierLebesgueSpace (2:ℝ) (-1) 2)
    (z : ℂ) (N : ℕ) (v : Fin N → FourierLebesgueSpace (2:ℝ) 1 2)
    (hv : v ∈ singularHillChainSpace q z N) (t : ℂ) :
    ((z+t) • singularHillDomainInclusion - singularHillOperator q)
      (pencilChainPolynomial N v t) = t^N •
      singularHillDomainInclusion
        (pencilChainEndpoint (LinearMap.id : FourierLebesgueSpace (2:ℝ) 1 2 →ₗ[ℂ]
          FourierLebesgueSpace (2:ℝ) 1 2) N v) := by
  have he : (z+t) • singularHillDomainInclusion - singularHillOperator q =
      t • singularHillDomainInclusion -
        (singularHillOperator q-z • singularHillDomainInclusion) := by module
  rw [he]
  exact (pencilChainPolynomial_pencil singularHillDomainInclusion.toLinearMap
    (singularHillOperator q-z • singularHillDomainInclusion).toLinearMap N v hv t).trans
      (congrArg (fun x => t^N • x) (pencilChainEndpoint_factor singularHillDomainInclusion.toLinearMap N v))

/-- Each full-domain finite chain space is finite dimensional for the source endpoint range. -/
theorem finiteDimensional_endpointHillChainSpace (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) (z : ℂ) (N : ℕ) :
    FiniteDimensional ℂ (singularHillChainSpace
      (endpointHillHminusOne SpectralWeight.one r hr1 q) z N) := by
  let := finiteDimensional_endpointHillRootSpaceTop r hr hr1 q z
  have hle : singularHillRootSpace (endpointHillHminusOne SpectralWeight.one r hr1 q) z N ≤
      singularHillRootSpaceTop (endpointHillHminusOne SpectralWeight.one r hr1 q) z :=
    le_iSup (pencilRootSpace singularHillDomainInclusion.toLinearMap
      (singularHillOperator (endpointHillHminusOne SpectralWeight.one r hr1 q)-
        z • singularHillDomainInclusion).toLinearMap) N
  let := FiniteDimensional.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)
  exact FiniteDimensional.of_injective
    (singularHillChainRootEquiv (endpointHillHminusOne SpectralWeight.one r hr1 q) z N).toLinearMap
      (singularHillChainRootEquiv (endpointHillHminusOne SpectralWeight.one r hr1 q) z N).injective

/-- The eventual dimension of physical finite coefficient chains is the
actual original algebraic multiplicity, with no semisimplicity hypothesis. -/
theorem eventually_finrank_endpointHillChainSpace (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) (z : ℂ) :
    ∀ᶠ N : ℕ in atTop,
      Module.finrank ℂ (singularHillChainSpace
        (endpointHillHminusOne SpectralWeight.one r hr1 q) z N) =
        endpointHillAlgebraicMultiplicity r hr hr1 q z := by
  obtain ⟨M,hM⟩ := endpointHillRootSpace_stabilizes r hr hr1 q z
  filter_upwards [eventually_ge_atTop M] with N hN
  rw [finrank_singularHillChainSpace, hM N hN]
  rfl

/-- The affine polynomial forcing is endpoint data with exactly the
same original H-minus-one distribution as its final H1 chain coefficient. -/
theorem endpointHillChainPolynomial_forcing (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) (z : ℂ) (N : ℕ)
    (v : Fin N → FourierLebesgueSpace (2:ℝ) 1 2)
    (hv : v ∈ singularHillChainSpace (endpointHillHminusOne SpectralWeight.one r hr1 q) z N)
    (t : ℂ) :
    endpointPhysicalPencilFamily r hr1 (q,z+t) (pencilChainPolynomial N v t) =
      endpointHillHminusOne SpectralWeight.one r hr1
        (t^N • H1EndpointInclusion r hr
          (pencilChainEndpoint (LinearMap.id : FourierLebesgueSpace (2:ℝ) 1 2 →ₗ[ℂ]
            FourierLebesgueSpace (2:ℝ) 1 2) N v)) := by
  rw [map_smul, endpointHillHminusOne_H1EndpointInclusion]
  exact singularHillChainPolynomial_pencil _ z N v hv t

/-- The two original physical Fourier coordinates of every coefficient of a finite chain. -/
def singularHillChainCoordinates (q : FourierLebesgueSpace (2:ℝ) (-1) 2)
    (z : ℂ) (N n : ℕ) : singularHillChainSpace q z N →ₗ[ℂ] (Fin N → ℂ × ℂ) where
  toFun v j := endpointHillH1Coordinates n (v.val j)
  map_add' := by intro v w; funext j; exact (endpointHillH1Coordinates n).map_add _ _
  map_smul' := by intro c v; funext j; exact (endpointHillH1Coordinates n).map_smul c _

end NLS.KdV
