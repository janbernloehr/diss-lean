import NLS.SequenceSpaces.Basic
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Complex.Basic

/-! # Real coefficient sequences and their complex inclusion

Real parts and the inclusion of real coefficients act continuously and
real linearly on the full `ℓᵖ` spaces. Coordinatewise reality characterizes
when their composition recovers the original complex sequence.
-/

noncomputable section
open scoped ENNReal
namespace NLS

/-- Real sequences indexed by the signed Fourier index. -/
abbrev RealCoeff (p : ℝ≥0∞) := lp (fun _ : ℤ => ℝ) p

namespace Coeff
variable (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- Coordinatewise real parts, as a bounded real linear map. -/
def reCLM : Coeff p →L[ℝ] RealCoeff p :=
  lp.mapCLM p (fun _ => Complex.reCLM) (norm_nonneg _) (fun _ => le_rfl)

@[simp] theorem reCLM_apply (a : Coeff p) (n : ℤ) :
    reCLM p a n = (a n).re := rfl

end Coeff
namespace RealCoeff
variable (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- The continuous real linear inclusion into complex coefficient sequences. -/
def complexCLM : RealCoeff p →L[ℝ] Coeff p :=
  lp.mapCLM p (fun _ => Complex.ofRealCLM) (norm_nonneg _) (fun _ => le_rfl)

@[simp] theorem complexCLM_apply (a : RealCoeff p) (n : ℤ) :
    complexCLM p a n = (a n : ℂ) := rfl

@[simp] theorem reCLM_complexCLM (a : RealCoeff p) :
    Coeff.reCLM p (complexCLM p a) = a := by
  ext n
  simp

/-- Taking real parts loses no information for a real complex sequence. -/
theorem complexCLM_reCLM (a : Coeff p) (ha : ∀ n : ℤ, (a n).im = 0) :
    complexCLM p (Coeff.reCLM p a) = a := by
  ext n
  apply Complex.ext <;> simp [ha]

end RealCoeff
end NLS
