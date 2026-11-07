import NLS.ZakharovShabat.SourcePsiDirichletInterpolation
import NLS.KdV.HminusOneDirichletSignedSymmetry

/-! The proved arbitrary-numerator interpolation theorem transports
to the ACTUAL auxiliary Dirichlet characteristic by phase rotation
of its denominator and roots. The numerator root vector is unchanged. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV

def hillAuxiliaryPsiInterpolationTerm (n : ℤ) (a : Coeff 2) (u : Coeff 2) (m : ℤ) (w : ℂ) : ℂ :=
  sourcePsiCandidate n (hillMiuraDiracDirichlet u m,a)/
    deriv (auxiliaryPeriodOneCharacteristic (by norm_num) (by norm_num) .dirichlet (hillMiuraDiagonal u))
      (hillMiuraDiracDirichlet u m)/(w-hillMiuraDiracDirichlet u m)

theorem tendstoUniformlyOn_hillAuxiliaryPsiInterpolation
    (n : ℤ) (a : Coeff 2) (u : PeriodOneRealL2) (L : ℝ) (hL : 0 ≤ L) :
    TendstoUniformlyOn (fun N : ℕ => fun w : ℂ => ∑ m ∈ Finset.Icc (-(N:ℤ)) N,
      hillAuxiliaryPsiInterpolationTerm n a u.val m w)
      (fun w => sourcePsiCandidate n (w,a)/auxiliaryPeriodOneCharacteristic
        (by norm_num) (by norm_num) .dirichlet (hillMiuraDiagonal u.val) w)
      atTop {w | ‖w‖ ≤ L ∧ auxiliaryPeriodOneCharacteristic
        (by norm_num) (by norm_num) .dirichlet (hillMiuraDiagonal u.val) w ≠ 0} := by
  let φ : realTypeSourceLocus 2 := ⟨sourcePhase (hillMiuraDiagonal u.val),
    isRealType_sourcePhase _ (isRealType_hillMiuraDiagonal u)⟩
  have ht := tendstoUniformlyOn_sourcePsiDirichletInterpolation (by norm_num) (by norm_num) n a φ L hL
  simpa only [hillAuxiliaryPsiInterpolationTerm,sourcePsiDirichletInterpolationTerm,
    hillMiuraDiracDirichlet,canonicalAuxiliaryPeriodOneRoots_eq_sourcePhase,
    auxiliaryPeriodOneCharacteristic_eq_sourcePhase,φ] using ht

end NLS.KdV
