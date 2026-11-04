import NLS.SequenceSpaces.BalancedQuadraticFrequencyLifting
import NLS.KdV.HillProductCoordinateVariation

/-! Balanced principal frequencies of INDEPENDENT Hill energy l2 data.
These are analytic product coordinates, not Dirac eigenvalues. The
physical energy shift and literal positive index m are retained. -/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV

def hillIndependentFrequencyDisplacement (t : ℂ × lp (fun _ : ℕ+ => ℂ) 2) : Coeff 2 :=
  LpSequence.balancedFrequencyDisplacement Real.pi Real.pi_pos t

def hillIndependentFrequency (t : ℂ × lp (fun _ : ℕ+ => ℂ) 2) (k : ℤ) : ℂ :=
  displacedRoots (hillIndependentFrequencyDisplacement t) k

theorem hillIndependentFrequency_zero (t : ℂ × lp (fun _ : ℕ+ => ℂ) 2) : hillIndependentFrequency t 0 = 0 :=
  LpSequence.balancedFrequency_zero Real.pi Real.pi_pos t

theorem hillIndependentFrequency_neg (t : ℂ × lp (fun _ : ℕ+ => ℂ) 2) (k : ℤ) :
    hillIndependentFrequency t (-k) = -hillIndependentFrequency t k :=
  LpSequence.balancedFrequency_neg Real.pi Real.pi_pos t k

theorem hillIndependentFrequency_positive (t : ℂ × lp (fun _ : ℕ+ => ℂ) 2) (m : ℕ+) :
    hillIndependentFrequency t ((m:ℕ):ℤ) = Complex.sqrt (hillEnergySequenceZero m t.2+t.1) :=
  LpSequence.balancedFrequency_positive Real.pi Real.pi_pos t m

theorem hillIndependentFrequency_positive_sq (t : ℂ × lp (fun _ : ℕ+ => ℂ) 2) (m : ℕ+) :
    hillIndependentFrequency t ((m:ℕ):ℤ)^2 = hillEnergySequenceZero m t.2+t.1 :=
  LpSequence.balancedFrequency_positive_sq Real.pi Real.pi_pos t m

theorem norm_hillIndependentFrequencyDisplacement_le (t : ℂ × lp (fun _ : ℕ+ => ℂ) 2) :
    ‖hillIndependentFrequencyDisplacement t‖ ≤ 2*Real.pi⁻¹*(‖t.2‖+2*‖t.1‖) :=
  LpSequence.norm_balancedFrequencyDisplacement_le Real.pi Real.pi_pos t

theorem analyticOnNhd_hillIndependentFrequencyDisplacement :
    AnalyticOnNhd ℂ hillIndependentFrequencyDisplacement (LpSequence.quadraticFrequencyDomain Real.pi) :=
  LpSequence.analyticOnNhd_balancedFrequencyDisplacement Real.pi Real.pi_pos

end NLS.KdV
