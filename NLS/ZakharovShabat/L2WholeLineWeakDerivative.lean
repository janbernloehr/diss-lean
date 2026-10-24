import NLS.ZakharovShabat.L2WholeLineMinimalOperator

/-! # The locally integrable weak derivative of a whole-line operator vector

An L2 vector and an L2 candidate operator image determine the original
signed differential expression solved for the derivative. The potential
is only locally L2; Hölder's inequality gives local L1 for its products.
-/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Complex
namespace NLS.ZakharovShabat

/-- The actual pair representative of a vector in the Hermitian whole-line L2 space. -/
def wholeLineL2Pair (f : WholeLineL2) (t : ℝ) : ℂ × ℂ := (f t).ofLp

theorem memLp_wholeLineL2Pair (f : WholeLineL2) : MemLp (wholeLineL2Pair f) 2 volume :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ ℂ ℂ).toContinuousLinearMap.comp_memLp' (Lp.memLp f)

/-- Local Hölder control of the actual potential times an arbitrary L2 vector. -/
theorem locallyIntegrable_l2WholeLinePotential_mul_L2 (u : IntervalPairL2) (f : WholeLineL2) :
    LocallyIntegrable (fun t => ((l2WholeLinePotential u t).1 * (wholeLineL2Pair f t).2,
      (l2WholeLinePotential u t).2 * (wholeLineL2Pair f t).1)) volume := by
  apply locallyIntegrable_iff.mpr
  intro K hK
  have hp := memLp_l2WholeLinePotential_on_compact u hK
  have hf := (memLp_wholeLineL2Pair f).restrict K
  simpa only [IntegrableOn,Pi.mul_apply] using!
    (hp.fst.integrable_mul hf.snd).prodMk (hp.snd.integrable_mul hf.fst)

/-- The original signed expression solved for the weak derivative,
with L2 input `f` and L2 operator image `g`. -/
def wholeLineWeakDerivative (u : IntervalPairL2) (f g : WholeLineL2) (t : ℝ) : ℂ × ℂ :=
  (-I * (wholeLineL2Pair g t).1 + I * (l2WholeLinePotential u t).1 * (wholeLineL2Pair f t).2,
    -I * (l2WholeLinePotential u t).2 * (wholeLineL2Pair f t).1 + I * (wholeLineL2Pair g t).2)

/-- The derivative candidate from the actual physical expression is
locally integrable for all whole-line L2 inputs and images. -/
theorem locallyIntegrable_wholeLineWeakDerivative
    (u : IntervalPairL2) (f g : WholeLineL2) :
    LocallyIntegrable (wholeLineWeakDerivative u f g) volume := by
  have hg1 := (memLp_wholeLineL2Pair g).fst.locallyIntegrable (by norm_num)
  have hg2 := (memLp_wholeLineL2Pair g).snd.locallyIntegrable (by norm_num)
  have hp := locallyIntegrable_l2WholeLinePotential_mul_L2 u f
  apply locallyIntegrable_iff.mpr
  intro K hK
  have hpk := hp.integrableOn_isCompact hK
  have h1 := ((hg1.integrableOn_isCompact hK).const_mul (-I)).add (hpk.fst.const_mul I)
  have h2 := (hpk.snd.const_mul (-I)).add ((hg2.integrableOn_isCompact hK).const_mul I)
  change Integrable (wholeLineWeakDerivative u f g) (volume.restrict K)
  unfold wholeLineWeakDerivative
  simpa only [mul_assoc,Pi.add_apply] using! h1.prodMk h2

theorem intervalIntegrable_wholeLineWeakDerivative
    (u : IntervalPairL2) (f g : WholeLineL2) (a b : ℝ) :
    IntervalIntegrable (wholeLineWeakDerivative u f g) volume a b :=
  intervalIntegrable_iff.mpr
    (((locallyIntegrable_wholeLineWeakDerivative u f g).integrableOn_isCompact isCompact_uIcc).mono_set
      uIoc_subset_uIcc)

end NLS.ZakharovShabat
