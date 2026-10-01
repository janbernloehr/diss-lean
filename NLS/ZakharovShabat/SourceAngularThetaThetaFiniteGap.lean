import NLS.ZakharovShabat.SourceDirichletSpectralFiniteTransport
import NLS.ZakharovShabat.SourceAngularThetaThetaGlobalTransport
import NLS.ZakharovShabat.SourceAngularThetaThetaEndpoint
import NLS.ZakharovShabat.SourceFiniteGap

/-! # Actual angle/angle involution at finite-gap Hilbert sources

Every finite composition of the actual complete spectral flows preserves
the full angle/angle bracket whenever its two angle gaps start open.
Constructed endpoint moves put all nonperiodic terminals of a finite-gap
source at periodic terminals. The proved endpoint identity then makes
the original full actual bracket zero. Density and exponent extension
remain separate requirements for arbitrary sources.
-/

noncomputable section
set_option maxHeartbeats 800000
open Set Complex NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat
local instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
namespace SourceAngularThetaCommonDomainData
variable {W₀ B W : Set (CoeffPair 2)}
  {s : (j : ℤ) → CoeffPair 2 → DeletedCoeff 2 j}

/-- Actual finite spectral flow compositions preserve the full actual
angle/angle bracket. Only the two angle gaps must initially be open. -/
theorem thetaTheta_sourceDirichletSpectralFlowSequence
    (D : SourceAngularThetaCommonDomainData (p := 2) (by simp) (by norm_num) W₀ B W s)
    (n m : ℤ) (φ : realTypeSourceLocus 2) (moves : List (ℤ × ℝ))
    (hn : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0)
    (hm : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential φ.val) (periodOnePotential_mem φ.val) m ≠ 0) :
    sourceAngularThetaThetaBracket (by simp) (by norm_num) (by norm_num) n m s
      (sourceDirichletSpectralFlowSequence φ moves).val =
    sourceAngularThetaThetaBracket (by simp) (by norm_num) (by norm_num) n m s φ.val := by
  induction moves generalizing φ with
  | nil => rfl
  | cons move moves ih =>
    rw [sourceDirichletSpectralFlowSequence_cons]
    let ψ := sourceDirichletSpectralFlow move.1 φ move.2
    have hnψ : canonicalPeriodicGap (by simp) (by norm_num)
        (periodOnePotential ψ.val) (periodOnePotential_mem ψ.val) n ≠ 0 := by
      rw [canonicalPeriodicGap_sourceDirichletSpectralFlow move.1 n φ move.2]
      exact hn
    have hmψ : canonicalPeriodicGap (by simp) (by norm_num)
        (periodOnePotential ψ.val) (periodOnePotential_mem ψ.val) m ≠ 0 := by
      rw [canonicalPeriodicGap_sourceDirichletSpectralFlow move.1 m φ move.2]
      exact hm
    exact (ih ψ hnψ hmψ).trans (D.thetaTheta_sourceDirichletSpectralFlow move.1 n m φ move.2 hn hm)

/-- The full actual angle/angle bracket vanishes whenever only finitely
many actual Dirichlet terminals are nonperiodic. All endpoint moves and
bracket transport are constructed, without a supplied basepoint. -/
theorem thetaThetaBracket_eq_zero_of_finite_nonperiodic_terminals
    (D : SourceAngularThetaCommonDomainData (p := 2) (by simp) (by norm_num) W₀ B W s)
    (n m : ℤ) (φ : realTypeSourceLocus 2)
    (hn : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0)
    (hm : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential φ.val) (periodOnePotential_mem φ.val) m ≠ 0)
    (hfinite : {j : ℤ | sourceBoundaryTerminalAntiDiscriminant (by simp) (by norm_num)
      .dirichlet j φ.val ≠ 0}.Finite) :
    sourceAngularThetaThetaBracket (by simp) (by norm_num) (by norm_num) n m s φ.val = 0 := by
  obtain ⟨moves,hperiodic,_⟩ := exists_sourceDirichletSpectralFlowSequence_all_terminals_periodic φ hfinite
  let ψ := sourceDirichletSpectralFlowSequence φ moves
  have hnψ : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential ψ.val) (periodOnePotential_mem ψ.val) n ≠ 0 := by
    rw [(sourceDirichletSpectralFlowSequence_periodicData φ moves n).1]
    exact hn
  have hmψ : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential ψ.val) (periodOnePotential_mem ψ.val) m ≠ 0 := by
    rw [(sourceDirichletSpectralFlowSequence_periodicData φ moves m).1]
    exact hm
  exact (D.thetaTheta_sourceDirichletSpectralFlowSequence n m φ moves hn hm).symm.trans
    (D.thetaThetaBracket_eq_zero_of_all_terminals_periodic (by norm_num) n m ψ hnψ hmψ hperiodic)

/-- Actual finite-gap Hilbert sources satisfy the full angle/angle
involution identity for any two open angle gaps. -/
theorem thetaThetaBracket_eq_zero_of_mem_sourceFiniteGapLocus
    (D : SourceAngularThetaCommonDomainData (p := 2) (by simp) (by norm_num) W₀ B W s)
    (n m : ℤ) (φ : realTypeSourceLocus 2)
    (hn : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0)
    (hm : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential φ.val) (periodOnePotential_mem φ.val) m ≠ 0)
    (hfinite : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) :
    sourceAngularThetaThetaBracket (by simp) (by norm_num) (by norm_num) n m s φ.val = 0 :=
  D.thetaThetaBracket_eq_zero_of_finite_nonperiodic_terminals n m φ hn hm
    (finite_nonperiodic_terminals_of_mem_sourceFiniteGapLocus (by simp) (by norm_num) φ hfinite)

end SourceAngularThetaCommonDomainData
end NLS.ZakharovShabat
