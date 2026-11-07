import NLS.KdV.HillAuxiliaryPsiInterpolation
import NLS.KdV.HillAbelianFrequencyDifferentials

/-! Exact scalar derivative normalization of the actual auxiliary
characteristic and the actual Hill numerator's odd frequency identity. -/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV

theorem deriv_auxiliaryDirichlet_at_Hill_root
    (q : PeriodOneHminusOne) (u : Coeff 2) (c z : ℂ)
    (himage : periodOneMiura u=q+periodOneL2Inclusion (lp.single 2 0 c))
    (hzero : hillHminusDirichlet q (z^2-c)=0) :
    deriv (auxiliaryPeriodOneCharacteristic (by norm_num) (by norm_num) .dirichlet (hillMiuraDiagonal u)) z =
      2*z^2*deriv (hillHminusDirichlet q) (z^2-c) := by
  have he : auxiliaryPeriodOneCharacteristic (by norm_num) (by norm_num) .dirichlet (hillMiuraDiagonal u) =
      (fun w => w*hillHminusDirichlet q (w^2-c)) :=
    funext (fun w => auxiliaryDirichlet_eq_mul_hillHminusDirichlet q u c w himage)
  have hg : HasDerivAt (fun w : ℂ => w^2-c) (2*z) z := by
    simpa using! (((hasDerivAt_id z).pow 2).sub_const c)
  have hS := (analyticOnNhd_hillHminusDirichlet_energy q (z^2-c) (mem_univ _)).differentiableAt.hasDerivAt
  have hd := (hasDerivAt_id z).mul (hS.comp z hg)
  change HasDerivAt (fun w => w*hillHminusDirichlet q (w^2-c)) _ z at hd
  rw [he,hd.deriv]
  dsimp only [Function.comp_def,id_eq]
  rw [hzero]
  ring

theorem HillProductEquationPatch.canonicalPsi_frequency_identity
    (P : HillProductEquationPatch) (n : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ P.source) (z : ℂ) :
    2*z*hillHminusCanonicalPsi n (z^2-(P.parent.parent.miuraBall.actionBall.shift:ℂ),q) =
      sourcePsiCandidate ((n:ℕ):ℤ) (z,(P.parent.family.roots ((n:ℕ):ℤ) (P.sourcePsi q):Coeff 2))-
        sourcePsiCandidate ((n:ℕ):ℤ) (-z,(P.parent.family.roots ((n:ℕ):ℤ) (P.sourcePsi q):Coeff 2)) := by
  change P.abelianFrequencyNumerator n (z,q) = _
  rw [P.abelianFrequencyNumerator_eq_local n z q hq]
  dsimp only [HillHminusDirichletBall.psiNumerator]
  simp only [sub_add_cancel]
  exact P.parent.family.numerator_frequency_identity n (P.parent.parent.miuraBall.actionBall.lift q) z

end NLS.KdV
