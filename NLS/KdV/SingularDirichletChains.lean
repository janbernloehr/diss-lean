import NLS.KdV.SingularDirichletAlgebraicMultiplicity
import NLS.KdV.SingularDirichletForcedCharts
import NLS.ComplexAnalysis.AffinePencilJets
import NLS.ComplexAnalysis.PoweredAnalyticJet

/-! # Full native Dirichlet chains and their finite analytic jets

Every coefficient belongs to the entire zero-trace H1 domain. Evaluation
of the final vector identifies these chains with the actual partial
operator's root spaces. Their physical inhomogeneous rows retain the
preceding coefficient. Finite jets characterize the same chain space.
-/
noncomputable section
open Set Filter Topology MeasureTheory
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue NLS.FunctionalAnalysis NLS.ComplexAnalysis
local instance dirichletChainsH1NormedGroup : NormedAddCommGroup UnitDirichletH1 :=
  unitDirichletSubspace.normedAddCommGroup
local instance dirichletChainsH1NormedSpace : NormedSpace ℂ UnitDirichletH1 :=
  unitDirichletSubspace.normedSpace
local instance dirichletChainsBaseNormedGroup : NormedAddCommGroup UnitDirichletHminus := inferInstance
local instance dirichletChainsBaseNormedSpace : NormedSpace ℂ UnitDirichletHminus := inferInstance

/-- Finite native chains, in Taylor order, with A-lambda*J taking each
coefficient to the included preceding coefficient. -/
def singularDirichletChainSpace
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (lambda : ℂ) (N : ℕ) :
    Submodule ℂ (Fin N → UnitDirichletH1) :=
  pencilChainSpace singularDirichletDomainInclusion.toLinearMap
    (singularDirichletOperator q-lambda • singularDirichletDomainInclusion).toLinearMap N

/-- Every full-domain chain is identified with its actual final base root vector. -/
def singularDirichletChainRootEquiv
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (lambda : ℂ) (N : ℕ) :
    singularDirichletChainSpace q lambda N ≃ₗ[ℂ] singularDirichletRootSpace q lambda N := by
  rw [singularDirichletRootSpace_eq_negative_pencil]
  exact pencilChainRootEquiv singularDirichletDomainInclusion.toLinearMap
    (singularDirichletOperator q-lambda • singularDirichletDomainInclusion).toLinearMap
      singularDirichletDomainInclusion_injective N

/-- Retaining all original domain coefficients loses no actual root-space dimension. -/
theorem finrank_singularDirichletChainSpace
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (lambda : ℂ) (N : ℕ) :
    Module.finrank ℂ (singularDirichletChainSpace q lambda N) =
      Module.finrank ℂ (singularDirichletRootSpace q lambda N) :=
  (singularDirichletChainRootEquiv q lambda N).finrank_eq

/-- All finite chain spaces are finite dimensional at EVERY original complex potential. -/
theorem finiteDimensional_singularDirichletChainSpace
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (lambda : ℂ) (N : ℕ) :
    FiniteDimensional ℂ (singularDirichletChainSpace q lambda N) := by
  let := finiteDimensional_singularDirichletRootSpaceTop q lambda
  have hle : singularDirichletRootSpace q lambda N ≤ singularDirichletRootSpaceTop q lambda :=
    le_iSup (fun n => singularDirichletRootSpace q lambda n) N
  let := FiniteDimensional.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)
  exact FiniteDimensional.of_injective (singularDirichletChainRootEquiv q lambda N).toLinearMap
    (singularDirichletChainRootEquiv q lambda N).injective

/-- The eventual dimension of full native coefficient chains is the actual algebraic multiplicity. -/
theorem eventually_finrank_singularDirichletChainSpace
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (lambda : ℂ) :
    ∀ᶠ N : ℕ in atTop, Module.finrank ℂ (singularDirichletChainSpace q lambda N) =
      singularDirichletAlgebraicMultiplicity q lambda := by
  obtain ⟨M, hM⟩ := singularDirichletRootSpace_stabilizes q lambda
  filter_upwards [eventually_ge_atTop M] with N hN
  rw [finrank_singularDirichletChainSpace, hM N hN]
  rfl

/-- Appending a native coefficient is precisely the actual inhomogeneous equation. -/
theorem mem_singularDirichletChainSpace_succ
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (lambda : ℂ) (N : ℕ)
    (v : Fin (N+1) → UnitDirichletH1) :
    v ∈ singularDirichletChainSpace q lambda (N+1) ↔
      Fin.init v ∈ singularDirichletChainSpace q lambda N ∧
      singularDirichletOperator q (v (Fin.last N))-
        lambda • singularDirichletDomainInclusion (v (Fin.last N)) =
      singularDirichletDomainInclusion
        (pencilChainEndpoint (LinearMap.id : UnitDirichletH1 →ₗ[ℂ] UnitDirichletH1) N (Fin.init v)) := by
  rw [singularDirichletChainSpace, mem_pencilChainSpace_succ, pencilChainEndpoint_factor]
  rfl

/-- At every original complex source, appending a coefficient to an actual
native chain is exactly the pair of physical forced quasi-Hill rows. -/
theorem mem_singularDirichletChainSpace_succ_iff_physical_rows
    (q : PeriodOneHminusOne) (lambda : ℂ) (N : ℕ) (v : Fin (N+1) → UnitDirichletH1) :
    v ∈ singularDirichletChainSpace (periodOneOriginal q) lambda (N+1) ↔
      Fin.init v ∈ singularDirichletChainSpace (periodOneOriginal q) lambda N ∧
      let f := v (Fin.last N)
      let g := pencilChainEndpoint (LinearMap.id : UnitDirichletH1 →ₗ[ℂ] UnitDirichletH1) N (Fin.init v)
      let u := (hillHminusMiuraChartAt q).lift q
      let mu := lambda+(hillHminusMiuraChartAt q).energyShift
      ∃ G : ℝ → ℂ, Continuous G ∧ AbsolutelyContinuousOnInterval G 0 1 ∧
        MeasureTheory.MemLp (deriv G) 2 (MeasureTheory.volume.restrict (Ioc 0 1)) ∧
        (∀ᵐ x ∂MeasureTheory.volume.restrict (Ioc 0 1), HasDerivAt (unitDirichletRepresentative f)
          (unitL2SynthesisEquiv u x*unitDirichletRepresentative f x+G x) x) ∧
        (∀ᵐ x ∂MeasureTheory.volume.restrict (Ioc 0 1), HasDerivAt G
          (-mu*unitDirichletRepresentative f x-unitL2SynthesisEquiv u x*G x-
            unitDirichletRepresentative g x) x) := by
  rw [mem_singularDirichletChainSpace_succ]
  exact and_congr Iff.rfl (singularDirichlet_source_forced_iff_physical_rows q lambda
    (v (Fin.last N))
    (pencilChainEndpoint (LinearMap.id : UnitDirichletH1 →ₗ[ℂ] UnitDirichletH1) N (Fin.init v)))

/-- Full-domain native chain polynomials are analytic in the native H1 norm. -/
theorem analyticAt_singularDirichletChainPolynomial (N : ℕ)
    (v : Fin N → UnitDirichletH1) (t : ℂ) : AnalyticAt ℂ (pencilChainPolynomial N v) t :=
  analyticAt_chainPolynomial N v t

/-- Every finite chain polynomial solves the actual affine pencil up to
exactly its final, Nth-order included domain vector. -/
theorem singularDirichletChainPolynomial_residual
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (lambda : ℂ) (N : ℕ)
    (v : Fin N → UnitDirichletH1) (hv : v ∈ singularDirichletChainSpace q lambda N) (t : ℂ) :
    singularDirichletPencil q (lambda+t) (pencilChainPolynomial N v t) =
      t^N • pencilChainEndpoint singularDirichletDomainInclusion.toLinearMap N v := by
  have he : singularDirichletPencil q (lambda+t) = t • singularDirichletDomainInclusion-
      (singularDirichletOperator q-lambda • singularDirichletDomainInclusion) := by
    unfold singularDirichletPencil
    module
  rw [he]
  exact pencilChainPolynomial_pencil singularDirichletDomainInclusion.toLinearMap
    (singularDirichletOperator q-lambda • singularDirichletDomainInclusion).toLinearMap N v hv t

/-- Every retained analytic derivative of a chain's actual pencil residual vanishes. -/
theorem singularDirichletChainPolynomial_residual_derivatives_zero
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (lambda : ℂ) (N : ℕ)
    (v : Fin N → UnitDirichletH1) (hv : v ∈ singularDirichletChainSpace q lambda N)
    (k : ℕ) (hk : k < N) :
    iteratedDeriv k (fun t : ℂ =>
      singularDirichletPencil q (lambda+t) (pencilChainPolynomial N v t)) 0 = 0 := by
  have he : (fun t : ℂ => singularDirichletPencil q (lambda+t) (pencilChainPolynomial N v t)) =
      fun t : ℂ => t^N • pencilChainEndpoint singularDirichletDomainInclusion.toLinearMap N v :=
    funext fun t => singularDirichletChainPolynomial_residual q lambda N v hv t
  rw [he]
  exact iteratedDeriv_pow_smul_zero analyticAt_const N k hk

/-- Vanishing of the retained actual native residual jets also suffices
for an arbitrary native polynomial's coefficients to be a full-domain chain. -/
theorem mem_singularDirichletChainSpace_iff_residual_derivatives_zero
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (lambda : ℂ) (N : ℕ)
    (v : Fin N → UnitDirichletH1) :
    v ∈ singularDirichletChainSpace q lambda N ↔
      ∀ k : Fin N, iteratedDeriv k.val (fun t : ℂ =>
        singularDirichletPencil q (lambda+t) (pencilChainPolynomial N v t)) 0 = 0 := by
  constructor
  · intro hv k
    exact singularDirichletChainPolynomial_residual_derivatives_zero q lambda N v hv k.val k.isLt
  · intro hv
    have he : (fun t : ℂ => t • singularDirichletDomainInclusion (pencilChainPolynomial N v t)-
        (singularDirichletOperator q-lambda • singularDirichletDomainInclusion)
          (pencilChainPolynomial N v t)) =
        fun t : ℂ => singularDirichletPencil q (lambda+t) (pencilChainPolynomial N v t) := by
      funext t
      change t • singularDirichletDomainInclusion (pencilChainPolynomial N v t)-
        (singularDirichletOperator q (pencilChainPolynomial N v t)-
          lambda • singularDirichletDomainInclusion (pencilChainPolynomial N v t)) =
        (lambda+t) • singularDirichletDomainInclusion (pencilChainPolynomial N v t)-
          singularDirichletOperator q (pencilChainPolynomial N v t)
      module
    have h := analyticFiniteJet_mem_pencilChainSpace singularDirichletDomainInclusion
      (singularDirichletOperator q-lambda • singularDirichletDomainInclusion)
      (analyticAt_singularDirichletChainPolynomial N v 0) N (by rw [he]; exact hv)
    rwa [analyticFiniteJet_chainPolynomial] at h

end NLS.KdV
