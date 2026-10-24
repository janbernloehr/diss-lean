import NLS.ZakharovShabat.L2WholeLineWeakDerivative

/-! # Realizing whole-line square-integrable physical pairs -/
noncomputable section
set_option autoImplicit false
open MeasureTheory
namespace NLS.ZakharovShabat

theorem memLp_wholeLineVector_of_pair (F : ℝ → ℂ × ℂ) (hF : MemLp F 2 volume) :
    MemLp (fun t => WithLp.toLp 2 (F t)) 2 volume :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ ℂ ℂ).symm.toContinuousLinearMap.comp_memLp' hF

/-- The original pair as a vector in the Hermitian whole-line L2 space. -/
def wholeLineOfPair (F : ℝ → ℂ × ℂ) (hF : MemLp F 2 volume) : WholeLineL2 :=
  (memLp_wholeLineVector_of_pair F hF).toLp (fun t => WithLp.toLp 2 (F t))

theorem wholeLineOfPair_ae (F : ℝ → ℂ × ℂ) (hF : MemLp F 2 volume) :
    wholeLineOfPair F hF =ᵐ[volume] (fun t => WithLp.toLp 2 (F t)) :=
  (memLp_wholeLineVector_of_pair F hF).coeFn_toLp

theorem wholeLineL2Pair_ofPair_ae (F : ℝ → ℂ × ℂ) (hF : MemLp F 2 volume) :
    wholeLineL2Pair (wholeLineOfPair F hF) =ᵐ[volume] F := by
  filter_upwards [wholeLineOfPair_ae F hF] with t ht
  exact congrArg WithLp.ofLp ht

/-- The actual Hermitian L2 norm is the square integral of the physical fibre norm. -/
theorem norm_wholeLineOfPair_sq (F : ℝ → ℂ × ℂ) (hF : MemLp F 2 volume) :
    ‖wholeLineOfPair F hF‖ ^ 2 = ∫ t : ℝ, ‖WithLp.toLp 2 (F t)‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [wholeLineOfPair_ae F hF] with t ht
  rw [ht,real_inner_self_eq_norm_sq]

end NLS.ZakharovShabat
