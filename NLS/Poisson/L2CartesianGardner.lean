import NLS.Poisson.L2Gardner
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-! # Componentwise Gardner brackets of an actual Cartesian observable -/
noncomputable section
namespace NLS.Poisson

theorem l2GardnerBracket_pair (F : NLS.Coeff 2 → ℂ × ℂ) (G : NLS.Coeff 2 → ℂ)
    (a : NLS.Coeff 2) (hF : DifferentiableAt ℂ F a) :
    (l2GardnerBracket (fun b => (F b).1) G a,l2GardnerBracket (fun b => (F b).2) G a) =
      fderiv ℂ F a (l2GardnerDirection G a) := by
  have hx := ((ContinuousLinearMap.fst ℂ ℂ ℂ).hasFDerivAt.comp a hF.hasFDerivAt).fderiv
  have hy := ((ContinuousLinearMap.snd ℂ ℂ ℂ).hasFDerivAt.comp a hF.hasFDerivAt).fderiv
  change fderiv ℂ (fun b => (F b).1) a = _ at hx
  change fderiv ℂ (fun b => (F b).2) a = _ at hy
  apply Prod.ext
  · change (fderiv ℂ (fun b => (F b).1) a) _ = _
    rw [hx]
    rfl
  · change (fderiv ℂ (fun b => (F b).2) a) _ = _
    rw [hy]
    rfl

end NLS.Poisson
