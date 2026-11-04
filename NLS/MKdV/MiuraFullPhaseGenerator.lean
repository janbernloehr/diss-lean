import NLS.MKdV.MiuraFullPhaseRotation

/-! # The actual independent phase generator on arbitrary support -/
noncomputable section
open Set Complex NLS.ZakharovShabat
namespace NLS.MKdV

theorem hasDerivAt_miuraNativeOppositeAbelianPhase_actionFlow
    (s : ℕ) (hs : 1 ≤ s) (a : MiuraRealSobolevSource s) (n : ℕ) (hn : 1 ≤ n)
    (j : ℕ) (hj : 1 ≤ j) (t : ℝ) :
    HasDerivAt (fun r => miuraNativeOppositeAbelianPhase s hs n hn (miuraNativeRealActionFlow s a j r))
      (-(if n = j then I else 0)*miuraNativeOppositeAbelianPhase s hs n hn (miuraNativeRealActionFlow s a j t)) t := by
  have he : (fun r => miuraNativeOppositeAbelianPhase s hs n hn (miuraNativeRealActionFlow s a j r)) =
      (fun r : ℝ => Complex.exp (-(if n = j then I else 0)*(r:ℂ))*miuraNativeOppositeAbelianPhase s hs n hn a) :=
    funext (miuraNativeOppositeAbelianPhase_actionFlow s hs a n hn j hj)
  rw [he]
  apply ((NLS.FunctionalAnalysis.hasDerivAt_scalarExponential (-(if n = j then I else 0)) t).mul_const
    (miuraNativeOppositeAbelianPhase s hs n hn a)).congr_deriv
  rw [miuraNativeOppositeAbelianPhase_actionFlow s hs a n hn j hj t,mul_assoc]

end NLS.MKdV
