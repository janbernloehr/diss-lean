import NLS.ZakharovShabat.BoundaryDisplacementSummability
import NLS.ZakharovShabat.BoundedIntervalExtension

/-!
# Ordinary boundary asymptotics for period-one Fourier–Lebesgue potentials

The completed Dirichlet potential extension is a bounded complex-linear map
from the source period-one coefficient pair space. Pulling back the common
boundary neighborhood yields both ordinary displacement sequences in ℓp,
with locally uniform quantitative tails for every finite p>1. The auxiliary
starred boundary problems require the distinct Section 5 phase-twisted realization.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The reflected potential used by both ordinary boundary problems, on the source pair norm. -/
def periodOneBoundaryPotential (hp : p ≠ ⊤) (hp1 : 1 < p) :
    CoeffPair p →L[ℂ] dirichletSubspace (p := p) :=
  (BoundaryCondition.intervalExtensionToBoundary .dirichlet hp1 hp).comp (CoeffPair.toMax p).toContinuousLinearMap

/-- The actual trace-defined high-index ordinary boundary branch after the interval extension. -/
def periodOneBoundaryEigenvalue (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition)
    (φ : CoeffPair p) (n : ℤ) : ℂ := b.eigenvalue hp (periodOneBoundaryPotential hp hp1 φ).val n

/-- Ordinary Corollary 6.2: both source coefficient displacement sequences lie in ℓp, with common quantitative tails. -/
theorem exists_uniform_periodOneBoundaryAsymptotics (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (CoeffPair p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧ ∀ ψ ∈ U, ∀ b : BoundaryCondition,
        Memℓp (fun n : ℤ => periodOneBoundaryEigenvalue hp hp1 b ψ n-(Real.pi : ℂ)*n) p ∧
        ∀ N : ℕ, N₀ ≤ N →
          Summable (spectralDisplacementPowerTail p N (periodOneBoundaryEigenvalue hp hp1 b ψ)) ∧
          (∑' n : ℤ, spectralDisplacementPowerTail p N (periodOneBoundaryEigenvalue hp hp1 b ψ) n) ≤
            rootDisplacementBudget SpectralWeight.one
              (unitBaseEquiv.symm (periodOneBoundaryPotential hp hp1 ψ).val) N := by
  let F := periodOneBoundaryPotential hp hp1
  obtain ⟨N,hN,V,ho,hc,hφ,h0,hbound⟩ := exists_uniform_boundaryDisplacementSummability hp hp1 (F φ)
  refine ⟨N,hN,F ⁻¹' V,ho.preimage F.continuous,hc.linear_preimage (F.restrictScalars ℝ).toLinearMap,
    hφ,by simpa using h0,?_⟩
  intro ψ hψ b
  exact hbound (F ψ) hψ b

/-- Both ordinary free branches retain every signed index under the completed interval extension. -/
@[simp] theorem periodOneBoundaryEigenvalue_zero (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition) (n : ℤ) :
    periodOneBoundaryEigenvalue hp hp1 b 0 n = (Real.pi : ℂ)*n := by
  simp only [periodOneBoundaryEigenvalue, map_zero, ZeroMemClass.coe_zero, BoundaryCondition.eigenvalue_zero]

end NLS.ZakharovShabat
