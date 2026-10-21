import NLS.Dynamics.PhaseAlmostPeriodic
import NLS.ZakharovShabat.SourceHamiltonianRenormalizedFlow

/-! # Almost periodicity of the actual Hamiltonian source flows

The original global Birkhoff inverse transfers phase recurrence to the
full source norm for 1 < p <= 2, for ordinary and renormalized NLS.
-/

noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {W : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
variable {W₀ B X : Set (CoeffPair p)} {t : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

namespace SourceAbelianMomentAtlas

/-- The ordinary Hamiltonian-oriented orbit is almost periodic in the original
source norm, for every source in the surjective range 1 < p ≤ 2. -/
theorem bohrAlmostPeriodic_hamiltonianOrdinarySourceFlow
    (A : SourceAbelianMomentAtlas hp hp1 W s)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t) (hp2 : p ≤ 2)
    (φ : realTypeSourceSubmodule p) :
    Dynamics.BohrAlmostPeriodic (A.hamiltonianOrdinarySourceFlow D hp2 φ) := by
  exact Birkhoff.bohrAlmostPeriodic_hamiltonianPhaseFlow_comp hp
    (A.ordinaryPhaseFrequency hp2 φ) (sourceComplexBirkhoffMap hp hp1 t φ.val)
    (fun z => (D.realHomeomorph hp2).symm (Birkhoff.decodeReal z))
    ((D.realHomeomorph hp2).symm.continuous.comp Birkhoff.decodeReal.continuous)

/-- The renormalized Hamiltonian-oriented flow has the same full source-norm
uniform recurrence, with its own actual frequency sequence. -/
theorem bohrAlmostPeriodic_hamiltonianRenormalizedSourceFlow
    (A : SourceAbelianMomentAtlas hp hp1 W s)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t) (hp2 : p ≤ 2)
    (φ : realTypeSourceSubmodule p) :
    Dynamics.BohrAlmostPeriodic (A.hamiltonianRenormalizedSourceFlow D hp2 φ) := by
  exact Birkhoff.bohrAlmostPeriodic_hamiltonianPhaseFlow_comp hp
    (A.phaseFrequency φ) (sourceComplexBirkhoffMap hp hp1 t φ.val)
    (fun z => (D.realHomeomorph hp2).symm (Birkhoff.decodeReal z))
    ((D.realHomeomorph hp2).symm.continuous.comp Birkhoff.decodeReal.continuous)

end SourceAbelianMomentAtlas
end NLS.ZakharovShabat
