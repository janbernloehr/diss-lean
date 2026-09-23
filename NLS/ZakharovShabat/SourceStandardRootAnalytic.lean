import NLS.ZakharovShabat.SourceStandardRootBranch
import Mathlib.Analysis.Complex.SqrtDeriv

/-!
# Spectral analyticity of the normalized standard root

The principal-root formula of equation (2.9) is analytic in the spectral
parameter outside the closed canonical periodic gap segment.
-/

noncomputable section
open Set Complex
open scoped ENNReal

namespace NLS.ZakharovShabat

/-- The normalized standard root is analytic wherever its denominator
is nonzero and its radicand lies in the principal slit plane. -/
theorem normalizedStandardRoot_analyticAt_of_slit
    (t g z : ℂ) (hz : t ≠ z)
    (hslit : 1-g/(4*(t-z)^2) ∈ Complex.slitPlane) :
    AnalyticAt ℂ (fun w => normalizedStandardRoot t g w) z := by
  have hlin : AnalyticAt ℂ (fun w : ℂ => t-w) z :=
    analyticAt_const.sub analyticAt_id
  have hden : AnalyticAt ℂ (fun w : ℂ => 4*(t-w)^2) z :=
    analyticAt_const.mul (hlin.pow 2)
  have hden0 : (4:ℂ)*(t-z)^2 ≠ 0 := by
    exact mul_ne_zero (by norm_num) (pow_ne_zero _ (sub_ne_zero.mpr hz))
  have hrad : AnalyticAt ℂ (fun w : ℂ => 1-g/(4*(t-w)^2)) z :=
    analyticAt_const.sub (analyticAt_const.div hden hden0)
  have hsqrt : AnalyticAt ℂ Complex.sqrt (1-g/(4*(t-z)^2)) :=
    Complex.differentiableOn_sqrt.analyticAt
      (Complex.isOpen_slitPlane.mem_nhds hslit)
  have hcomp : AnalyticAt ℂ (fun w : ℂ => Complex.sqrt (1-g/(4*(t-w)^2))) z :=
    hsqrt.comp (f := fun w : ℂ => 1-g/(4*(t-w)^2)) hrad
  have heq : (fun w => normalizedStandardRoot t g w) =
      (fun w : ℂ => t-w) * (fun w => Complex.sqrt (1-g/(4*(t-w)^2))) := by
    funext w
    rfl
  rw [heq]
  exact hlin.mul hcomp

/-- The canonical source standard root is analytic at each spectral point
outside its closed periodic gap segment. -/
theorem sourceStandardRoot_analyticAt
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ) (z : ℂ)
    (hz : z ∉ sourcePeriodicSegment hp hp1 ψ n) :
    AnalyticAt ℂ (sourceStandardRoot hp hp1 ψ n) z := by
  have hmid : z ≠ canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n := by
    intro he
    exact hz (he ▸ sourcePeriodicMidpoint_mem_segment hp hp1 ψ n)
  have hslit := sourceStandardRoot_radicand_mem_slitPlane hp hp1 ψ n z hz
  exact normalizedStandardRoot_analyticAt_of_slit _ _ _ hmid.symm hslit

/-- Spectral analyticity on the full complement of the closed gap segment. -/
theorem sourceStandardRoot_analyticOnNhd
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ) :
    AnalyticOnNhd ℂ (sourceStandardRoot hp hp1 ψ n)
      (sourcePeriodicSegment hp hp1 ψ n)ᶜ := by
  intro z hz
  exact sourceStandardRoot_analyticAt hp hp1 ψ n z hz

end NLS.ZakharovShabat
