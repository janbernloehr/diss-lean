import NLS.ZakharovShabat.AuxiliarySpectrum
import NLS.ZakharovShabat.BoundaryDisplacementSummability
import NLS.ZakharovShabat.BoundedIntervalExtension

/-!
# Starred coefficient eigenvalue asymptotics

The source uses the Neumann potential extension for both auxiliary problems.
Its phase-conjugated potential lies in the ordinary Dirichlet subspace. The
proved actual spectral equivalence identifies the high-disc trace branch as
an auxiliary eigenvalue. Pullback gives both starred ℓp displacement sequences
and quantitative tails on the same period-one potential neighborhood.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The potential phase map restricted to the correct reflected subspaces. -/
def auxiliaryPotentialToDirichlet : neumannSubspace (p := p) →L[ℂ] dirichletSubspace (p := p) :=
  (auxiliaryPotential.toContinuousLinearEquiv.toContinuousLinearMap.comp (neumannSubspace (p := p)).subtypeL).codRestrict _
    (fun φ => (auxiliaryPotential_mem_dirichlet_iff φ.val).mpr φ.property)

/-- The completed source Neumann potential extension, in the exact source pair topology. -/
def auxiliaryPeriodOnePotential (hp : p ≠ ⊤) (hp1 : 1 < p) : CoeffPair p →L[ℂ] neumannSubspace (p := p) :=
  (BoundaryCondition.intervalExtensionToBoundary .neumann hp1 hp).comp (CoeffPair.toMax p).toContinuousLinearMap

/-- The high-index auxiliary branch defined by the conjugate ordinary trace. -/
def auxiliaryEigenvalue (hp : p ≠ ⊤) (b : BoundaryCondition) (φ : PairSpace p) (n : ℤ) : ℂ :=
  b.eigenvalue hp (auxiliaryPotential φ) n

/-- The unique high-disc spectral value is an eigenvalue of the actual auxiliary restriction. -/
theorem auxiliarySpectrum_inter_disk (hp : p ≠ ⊤) (b : BoundaryCondition) (φ : PairSpace p)
    (hφ : φ ∈ neumannSubspace) {N : ℕ}
    (h : BoundaryCountingData hp (auxiliaryPotential φ) ((auxiliaryPotential_mem_dirichlet_iff φ).mpr hφ) N)
    (n : ℤ) (hn : N < n.natAbs) :
    b.auxiliarySpectrum hp φ hφ ∩ Metric.ball ((Real.pi : ℂ)*n) (Real.pi/4) = {auxiliaryEigenvalue hp b φ n} := by
  ext z
  rw [BoundaryCondition.auxiliarySpectrum_eq, Set.mem_inter_iff, ← BoundaryCondition.mem_enclosedSpectrum,
    (h.eigenvalue_spec b n hn).1]
  exact Finset.mem_singleton

/-- The source auxiliary branch on original period-one coefficient potentials. -/
def auxiliaryPeriodOneEigenvalue (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition) (φ : CoeffPair p) (n : ℤ) : ℂ :=
  auxiliaryEigenvalue hp b (auxiliaryPeriodOnePotential hp hp1 φ).val n

/-- The starred part of Corollary 6.2 for the actual coefficient auxiliary spectra. -/
theorem exists_uniform_auxiliaryPeriodOneAsymptotics (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (CoeffPair p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧ ∀ ψ ∈ U, ∀ b : BoundaryCondition,
        Memℓp (fun n : ℤ => auxiliaryPeriodOneEigenvalue hp hp1 b ψ n-(Real.pi : ℂ)*n) p ∧
        (∀ n : ℤ, N₀ ≤ n.natAbs →
          b.auxiliarySpectrum hp (auxiliaryPeriodOnePotential hp hp1 ψ).val (auxiliaryPeriodOnePotential hp hp1 ψ).property ∩
            Metric.ball ((Real.pi : ℂ)*n) (Real.pi/4) = {auxiliaryPeriodOneEigenvalue hp hp1 b ψ n}) ∧
        ∀ N : ℕ, N₀ ≤ N →
          Summable (spectralDisplacementPowerTail p N (auxiliaryPeriodOneEigenvalue hp hp1 b ψ)) ∧
          (∑' n : ℤ, spectralDisplacementPowerTail p N (auxiliaryPeriodOneEigenvalue hp hp1 b ψ) n) ≤
            rootDisplacementBudget SpectralWeight.one
              (unitBaseEquiv.symm (auxiliaryPotential (auxiliaryPeriodOnePotential hp hp1 ψ).val)) N := by
  let F := (auxiliaryPotentialToDirichlet (p := p)).comp (auxiliaryPeriodOnePotential hp hp1)
  obtain ⟨N₁,hN₁,U₁,ho₁,hc₁,hφ₁,h0₁,hbound⟩ := exists_uniform_boundaryDisplacementSummability hp hp1 (F φ)
  obtain ⟨N₂,U₂,_,ho₂,hc₂,hφ₂,h0₂,hcount,_⟩ := exists_uniform_analytic_boundaryEigenvalues hp (F φ)
  refine ⟨max N₁ (N₂+1),hN₁.trans (le_max_left _ _),F ⁻¹' (U₁ ∩ U₂),
    (ho₁.inter ho₂).preimage F.continuous,
    (hc₁.inter hc₂).linear_preimage (F.restrictScalars ℝ).toLinearMap,
    ⟨hφ₁,hφ₂⟩,by simpa using And.intro h0₁ h0₂,?_⟩
  intro ψ hψ b
  have hb := hbound (F ψ) hψ.1 b
  refine ⟨hb.1,?_,fun N hN => hb.2 N (by omega)⟩
  intro n hn
  exact auxiliarySpectrum_inter_disk hp b _ _ (hcount (F ψ) hψ.2 N₂ le_rfl) n (by omega)

/-- Both free auxiliary branches have the signed free eigenvalue. -/
@[simp] theorem auxiliaryPeriodOneEigenvalue_zero (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition) (n : ℤ) :
    auxiliaryPeriodOneEigenvalue hp hp1 b 0 n = (Real.pi : ℂ)*n := by
  simp only [auxiliaryPeriodOneEigenvalue, auxiliaryEigenvalue, map_zero, ZeroMemClass.coe_zero,
    BoundaryCondition.eigenvalue_zero]

end NLS.ZakharovShabat
