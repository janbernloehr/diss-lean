import NLS.SequenceSpaces.PeriodOneFourierLebesgueMiuraCompact
import NLS.SequenceSpaces.FourierLebesgueCompactInclusion
import NLS.SequenceSpaces.PeriodOneFourierLebesgueFreeMassEquiv

/-! # Actual native Fourier-Lebesgue Miura derivatives and compact free remainder -/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS

/-- The literal unit-period unshifted Miura map in its native norms. -/
def periodOneFourierLebesgueMiura (s p : ℝ) (hs : -1/2≤s) (hp : 2<p)
    [Fact (1≤ENNReal.ofReal p)]
    (a : WeightedCoeff (Weight.sobolev (s+1)) (ENNReal.ofReal p)) :
    WeightedCoeff (Weight.sobolev s) (ENNReal.ofReal p) :=
  periodOneFourierLebesgueMassOperator 0 s (ENNReal.ofReal p) a+
    periodOneFourierLebesgueMiuraProduct s p hs hp a a-
      WeightedCoeff.sobolevInclusion (by linarith : s≤s+1) a

@[simp] theorem periodOneFourierLebesgueMiura_apply
    (s p : ℝ) (hs : -1/2≤s) (hp : 2<p) [Fact (1≤ENNReal.ofReal p)]
    (a : WeightedCoeff (Weight.sobolev (s+1)) (ENNReal.ofReal p)) (n : ℤ) :
    (periodOneFourierLebesgueMiura s p hs hp a).val n=
      2*(I*(Real.pi : ℂ)*n)*a.val n+∑' j : ℤ, a.val (n-j)*a.val j := by
  simp only [periodOneFourierLebesgueMiura,WeightedCoeff.sub_val,WeightedCoeff.add_val,
    periodOneFourierLebesgueMassOperator_apply,periodOneFourierLebesgueMiuraProduct_apply,
    WeightedCoeff.sobolevInclusion_apply,periodOneMassSymbol,Nat.cast_zero,zero_add,ofReal_one]
  ring

def periodOneFourierLebesgueMiuraJacobian (s p : ℝ) (hs : -1/2≤s) (hp : 2<p)
    [Fact (1≤ENNReal.ofReal p)]
    (a : WeightedCoeff (Weight.sobolev (s+1)) (ENNReal.ofReal p)) :
    WeightedCoeff (Weight.sobolev (s+1)) (ENNReal.ofReal p) →L[ℂ]
      WeightedCoeff (Weight.sobolev s) (ENNReal.ofReal p) :=
  periodOneFourierLebesgueMassOperator 0 s (ENNReal.ofReal p)+
    (periodOneFourierLebesgueMiuraProduct s p hs hp a+
      (periodOneFourierLebesgueMiuraProduct s p hs hp).flip a)-
        WeightedCoeff.sobolevInclusion (by linarith : s≤s+1)

theorem hasFDerivAt_periodOneFourierLebesgueMiura
    (s p : ℝ) (hs : -1/2≤s) (hp : 2<p) [Fact (1≤ENNReal.ofReal p)]
    (a : WeightedCoeff (Weight.sobolev (s+1)) (ENNReal.ofReal p)) :
    HasFDerivAt (periodOneFourierLebesgueMiura s p hs hp)
      (periodOneFourierLebesgueMiuraJacobian s p hs hp a) a := by
  let B := periodOneFourierLebesgueMiuraProduct s p hs hp
  have h := B.hasFDerivAt_of_bilinear (hasFDerivAt_id a) (hasFDerivAt_id a)
  have he : B.precompR _ a (ContinuousLinearMap.id ℂ _)+B.precompL _ (ContinuousLinearMap.id ℂ _) a=
      B a+B.flip a := by ext v;rfl
  rw [show id a=a from rfl,he] at h
  exact ((periodOneFourierLebesgueMassOperator 0 s (ENNReal.ofReal p)).hasFDerivAt.add h).sub
    (WeightedCoeff.sobolevInclusion (by linarith : s≤s+1)).hasFDerivAt

/-- The ACTUAL native unshifted Jacobian is a compact perturbation of
its exact free mass equivalence, at every complex native coefficient. -/
theorem isCompactOperator_periodOneFourierLebesgueMiuraJacobian_sub_free
    (s p : ℝ) (hs : -1/2≤s) (hp : 2<p) [Fact (1≤ENNReal.ofReal p)]
    (a : WeightedCoeff (Weight.sobolev (s+1)) (ENNReal.ofReal p)) :
    IsCompactOperator (periodOneFourierLebesgueMiuraJacobian s p hs hp a-
      (periodOneFourierLebesgueFreeMassEquiv 0 s (ENNReal.ofReal p)).toContinuousLinearMap) := by
  let B := periodOneFourierLebesgueMiuraProduct s p hs hp
  have hflip : B.flip a=B a := by
    ext v
    exact periodOneFourierLebesgueMiuraProduct_comm s p hs hp v a
  have hmass : (periodOneFourierLebesgueFreeMassEquiv 0 s (ENNReal.ofReal p)).toContinuousLinearMap=
      periodOneFourierLebesgueMassOperator 0 s (ENNReal.ofReal p) := by ext v;rfl
  have he : periodOneFourierLebesgueMiuraJacobian s p hs hp a-
      (periodOneFourierLebesgueFreeMassEquiv 0 s (ENNReal.ofReal p)).toContinuousLinearMap=
      B a+B a-WeightedCoeff.sobolevInclusion (by linarith : s≤s+1) := by
    rw [hmass]
    change (periodOneFourierLebesgueMassOperator 0 s (ENNReal.ofReal p)+(B a+B.flip a)-
      WeightedCoeff.sobolevInclusion (by linarith : s≤s+1))-
        periodOneFourierLebesgueMassOperator 0 s (ENNReal.ofReal p)=_
    rw [hflip]
    abel
  rw [he]
  have hB := isCompactOperator_periodOneFourierLebesgueMiuraProduct s p hs hp a
  have h2p : (2 : ℝ≥0∞)≤ENNReal.ofReal p := by exact_mod_cast ENNReal.ofReal_le_ofReal hp.le
  have hp1 : (1 : ℝ≥0∞)<ENNReal.ofReal p := lt_of_lt_of_le (by norm_num) h2p
  exact (hB.add hB).sub
    (isCompactOperator_fourierLebesgueInclusion_sub_one s (ENNReal.ofReal p) ENNReal.ofReal_ne_top hp1)

end NLS
