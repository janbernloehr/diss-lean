import NLS.ZakharovShabat.SourceAngularThetaRectangularDifferential
import NLS.ZakharovShabat.SourceAngularThetaRealCotangent

/-! # The actual angle Hamiltonian vector field

The existing branch-independent angle cotangent gives the Hamiltonian
vector with the original Fourier reflection and Poisson signs. It is
analytic on the open-gap domain and preserves the real source form.
-/
noncomputable section
open Set NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual source Hamiltonian of the local angle representatives. -/
def sourceAngularThetaHamiltonianVector (hp : p ≠ ⊤) (hp1 : 1 < p)
    (h2p : (2 : ℝ≥0∞) ≤ p) (k : ℤ)
    (s : (j : ℤ) → CoeffPair p → DeletedCoeff p j) (φ : CoeffPair p) : CoeffPair p :=
  sourceHamiltonianDirection h2p (sourceAngularThetaDifferential hp hp1 k s φ)

namespace SourceAngularThetaCommonDomainData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (j : ℤ) → CoeffPair p → DeletedCoeff p j}

/-- The vector field is analytic wherever the selected gap is open. -/
theorem analyticOnNhd_thetaHamiltonian
    (E : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)
    (h2p : (2 : ℝ≥0∞) ≤ p) (k : ℤ) :
    AnalyticOnNhd ℂ (sourceAngularThetaHamiltonianVector hp hp1 h2p k s)
      {φ : CoeffPair p | φ ∈ W ∧ canonicalPeriodicGap hp hp1
        (periodOnePotential φ) (periodOnePotential_mem φ) k ≠ 0} := by
  intro φ hφ
  exact ((sourceHamiltonianDirection h2p).analyticAt _).comp
    (E.analyticOnNhd_thetaDifferential k φ hφ)

/-- The source Hamiltonian direction of the angle is real type. -/
theorem thetaHamiltonian_realType
    (E : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)
    (h2p : (2 : ℝ≥0∞) ≤ p) (k : ℤ) (φ : realTypeSourceSubmodule p)
    (hk : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) k ≠ 0) :
    IsRealType (CoeffPair.toMax p (sourceAngularThetaHamiltonianVector hp hp1 h2p k s φ.val)) :=
  (E.isSourceRealCotangent_thetaDifferential k φ hk).hamiltonianDirection_realType h2p

end SourceAngularThetaCommonDomainData
end NLS.ZakharovShabat
