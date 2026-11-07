import NLS.KdV.HminusOneDirichletChainAmplitudes
import NLS.Fourier.UnitDirichletRepresentativeLinear

/-! # Exact linear equivalence of native chains and scalar characteristic Taylor kernels

Both directions use the full native H1 domain and the actual rough physical
state jets. Linearity follows from the unchanged interval representatives;
no multiplicity or semisimplicity assumption enters either construction.
-/
noncomputable section
open Set Complex NLS.LinearVolterra NLS.FunctionalAnalysis NLS.ComplexAnalysis
namespace NLS.KdV
open NLS.Fourier

/-- The unique actual native chain associated with a scalar characteristic Taylor-kernel vector. -/
def singularDirichletTaylorKernelLift
    (q : PeriodOneHminusOne) (lambda : ℂ) (p : FormalMultilinearSeries ℂ ℂ ℂ)
    (hp : HasFPowerSeriesAt (fun t : ℂ => hillHminusDirichlet q (lambda+t)) p 0) (N : ℕ)
    (a : LinearMap.ker (scalarTaylorJetMap (scalarFormalTaylor p) N)) :
    singularDirichletChainSpace (periodOneOriginal q) lambda N :=
  Classical.choose (exists_native_chain_of_scalarTaylorKernel q lambda p hp N a.val a.property)

theorem singularDirichletTaylorKernelLift_position
    (q : PeriodOneHminusOne) (lambda : ℂ) (p : FormalMultilinearSeries ℂ ℂ ℂ)
    (hp : HasFPowerSeriesAt (fun t : ℂ => hillHminusDirichlet q (lambda+t)) p 0) (N : ℕ)
    (a : LinearMap.ker (scalarTaylorJetMap (scalarFormalTaylor p) N)) (k : Fin N)
    (x : ℝ) (hx : x ∈ Icc (0:ℝ) 1) :
    unitDirichletRepresentative ((singularDirichletTaylorKernelLift q lambda p hp N a).val k) x =
      (extend (hillHminusDirichletStateJet q lambda N a.val k) x).1 :=
  Classical.choose_spec (exists_native_chain_of_scalarTaylorKernel q lambda p hp N a.val a.property) k x hx

/-- The scalar Taylor-kernel reconstruction is COMPLEX LINEAR on the entire kernel. -/
def singularDirichletTaylorKernelToChain
    (q : PeriodOneHminusOne) (lambda : ℂ) (p : FormalMultilinearSeries ℂ ℂ ℂ)
    (hp : HasFPowerSeriesAt (fun t : ℂ => hillHminusDirichlet q (lambda+t)) p 0) (N : ℕ) :
    LinearMap.ker (scalarTaylorJetMap (scalarFormalTaylor p) N) →ₗ[ℂ]
      singularDirichletChainSpace (periodOneOriginal q) lambda N where
  toFun := singularDirichletTaylorKernelLift q lambda p hp N
  map_add' a b := by
    apply Subtype.ext
    funext k
    apply unitDirichletRepresentative_injective_on_interval
    intro x hx
    change unitDirichletRepresentative ((singularDirichletTaylorKernelLift q lambda p hp N (a+b)).val k) x =
      unitDirichletRepresentative
        ((singularDirichletTaylorKernelLift q lambda p hp N a).val k+
          (singularDirichletTaylorKernelLift q lambda p hp N b).val k) x
    rw [unitDirichletRepresentative_add, singularDirichletTaylorKernelLift_position _ _ _ _ _ (a+b) k x hx,
      singularDirichletTaylorKernelLift_position _ _ _ _ _ a k x hx,
      singularDirichletTaylorKernelLift_position _ _ _ _ _ b k x hx]
    exact congrArg (fun v : Fin N → Curve (ℂ × ℂ) => (extend (v k) x).1)
      ((hillHminusDirichletStateJet q lambda N).map_add a.val b.val)
  map_smul' c a := by
    apply Subtype.ext
    funext k
    apply unitDirichletRepresentative_injective_on_interval
    intro x hx
    change unitDirichletRepresentative ((singularDirichletTaylorKernelLift q lambda p hp N (c • a)).val k) x =
      unitDirichletRepresentative (c • (singularDirichletTaylorKernelLift q lambda p hp N a).val k) x
    rw [unitDirichletRepresentative_smul, singularDirichletTaylorKernelLift_position _ _ _ _ _ (c • a) k x hx,
      singularDirichletTaylorKernelLift_position _ _ _ _ _ a k x hx]
    exact congrArg (fun v : Fin N → Curve (ℂ × ℂ) => (extend (v k) x).1)
      ((hillHminusDirichletStateJet q lambda N).map_smul c a.val)

/-- The actual native chain lift loses no scalar Taylor-kernel vector. -/
theorem singularDirichletTaylorKernelToChain_injective
    (q : PeriodOneHminusOne) (lambda : ℂ) (p : FormalMultilinearSeries ℂ ℂ ℂ)
    (hp : HasFPowerSeriesAt (fun t : ℂ => hillHminusDirichlet q (lambda+t)) p 0) (N : ℕ) :
    Function.Injective (singularDirichletTaylorKernelToChain q lambda p hp N) := by
  intro a b hab
  apply Subtype.ext
  apply hillHminusDirichletStateJet_positions_injective q lambda N a.val b.val
  intro k t
  have h1 := singularDirichletTaylorKernelLift_position q lambda p hp N a k t.val t.property
  have h2 := singularDirichletTaylorKernelLift_position q lambda p hp N b k t.val t.property
  have he := congrArg (fun v : singularDirichletChainSpace (periodOneOriginal q) lambda N => v.val k) hab
  change (singularDirichletTaylorKernelLift q lambda p hp N a).val k =
    (singularDirichletTaylorKernelLift q lambda p hp N b).val k at he
  rw [he,extend_coe _ t] at h1
  rw [extend_coe _ t] at h2
  exact h1.symm.trans h2

/-- Every arbitrary native chain is reached by the scalar Taylor-kernel lift. -/
theorem singularDirichletTaylorKernelToChain_surjective
    (q : PeriodOneHminusOne) (lambda : ℂ) (p : FormalMultilinearSeries ℂ ℂ ℂ)
    (hp : HasFPowerSeriesAt (fun t : ℂ => hillHminusDirichlet q (lambda+t)) p 0) (N : ℕ) :
    Function.Surjective (singularDirichletTaylorKernelToChain q lambda p hp N) := by
  intro v
  obtain ⟨a,ha,hpos⟩ := exists_scalarTaylorKernel_of_native_chain q lambda p hp N v
  refine ⟨⟨a,ha⟩,?_⟩
  apply Subtype.ext
  funext k
  apply unitDirichletRepresentative_injective_on_interval
  intro x hx
  exact (singularDirichletTaylorKernelLift_position q lambda p hp N ⟨a,ha⟩ k x hx).trans
    (hpos k x hx).symm

/-- EXACT linear equivalence of every actual native finite-chain space
with the ORIGINAL scalar characteristic Taylor kernel at the same length. -/
def singularDirichletChainTaylorKernelEquiv
    (q : PeriodOneHminusOne) (lambda : ℂ) (p : FormalMultilinearSeries ℂ ℂ ℂ)
    (hp : HasFPowerSeriesAt (fun t : ℂ => hillHminusDirichlet q (lambda+t)) p 0) (N : ℕ) :
    singularDirichletChainSpace (periodOneOriginal q) lambda N ≃ₗ[ℂ]
      LinearMap.ker (scalarTaylorJetMap (scalarFormalTaylor p) N) :=
  (LinearEquiv.ofBijective (singularDirichletTaylorKernelToChain q lambda p hp N)
    ⟨singularDirichletTaylorKernelToChain_injective q lambda p hp N,
      singularDirichletTaylorKernelToChain_surjective q lambda p hp N⟩).symm

theorem finrank_singularDirichletChain_eq_scalarTaylorKernel
    (q : PeriodOneHminusOne) (lambda : ℂ) (p : FormalMultilinearSeries ℂ ℂ ℂ)
    (hp : HasFPowerSeriesAt (fun t : ℂ => hillHminusDirichlet q (lambda+t)) p 0) (N : ℕ) :
    Module.finrank ℂ (singularDirichletChainSpace (periodOneOriginal q) lambda N) =
      Module.finrank ℂ (LinearMap.ker (scalarTaylorJetMap (scalarFormalTaylor p) N)) :=
  (singularDirichletChainTaylorKernelEquiv q lambda p hp N).finrank_eq

end NLS.KdV
