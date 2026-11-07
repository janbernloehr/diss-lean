import NLS.KdV.HillMiuraFreeIsospectral
import NLS.KdV.HillMiuraDiscriminantSourceDerivative
import NLS.KdV.HillCanonicalActionIsospectral

/-! The derivative of an actual local Miura lift sends every native
Hill isospectral direction to an actual Dirac isospectral direction.
In particular it transports the native Gardner action directions;
no identification with a Dirac Poisson bracket is required. -/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV.HillHminusMiuraActionBall

theorem fderiv_diracSource_isospectral (B : HillHminusMiuraActionBall)
    (q : PeriodOneHminusOne) (hq : q ∈ B.source) (h : PeriodOneHminusOne)
    (hiso : ∀ E : ℂ, hillHminusDiscriminantCotangent E q h = 0) :
    SourceIsospectralDirection (by norm_num) (B.diracSource q)
      ((fderiv ℂ B.diracSource q) h) := by
  intro z
  change (fderiv ℂ (fun ψ : CoeffPair 2 => canonicalDiscriminant (by simp)
    (periodOnePotential ψ) z) (hillMiuraDiagonal (B.lift q)))
    ((fderiv ℂ (fun a => hillMiuraDiagonal (B.lift a)) q) h) = 0
  rw [fderiv_liftedMiuraDiscriminant_eq_native B.source B.source_open B.lift
    B.lift_analytic (B.shift:ℂ) B.image q hq z h]
  exact hiso _

theorem fderiv_diracSource_action_isospectral (B : HillHminusMiuraActionBall)
    (n : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ B.source)
    (ha : q ∈ hillHminusCanonicalActionDomain) :
    SourceIsospectralDirection (by norm_num) (B.diracSource q)
      ((fderiv ℂ B.diracSource q)
        (NLS.Poisson.gardnerHamiltonianVector (hillHminusCanonicalAction n) q)) := by
  apply B.fderiv_diracSource_isospectral q hq
  intro E
  exact hillHminusDiscriminant_action_Hamiltonian_direction E n q ha

end NLS.KdV.HillHminusMiuraActionBall
