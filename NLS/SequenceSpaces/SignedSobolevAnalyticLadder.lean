import NLS.SequenceSpaces.SignedSobolevAnalyticEquiv

/-! Iterate the actual analytic spatial lift, retaining every coefficient
and the full analytic inverse at every integer Sobolev order. -/
noncomputable section
namespace NLS.WeightedCoeff

def signedStepOrder (s : ℝ) : ℕ → ℝ
  | 0 => s
  | n+1 => signedStepOrder s n+1

theorem signedStepOrder_eq (s : ℝ) (n : ℕ) : signedStepOrder s n=s+(n:ℝ) := by
  induction n with
  | zero => simp only [signedStepOrder,Nat.cast_zero,add_zero]
  | succ n ih => simp only [signedStepOrder,ih,Nat.cast_add,Nat.cast_one,add_assoc]

def signedIteratedInclusion (s : ℝ) : (n : ℕ) → RealSignedHilbert (signedStepOrder s n) →L[ℝ] RealSignedHilbert s
  | 0 => ContinuousLinearMap.id ℝ _
  | n+1 => (signedIteratedInclusion s n).comp (signedRealInclusion (signedStepOrder s n))

theorem signedIteratedInclusion_apply (s : ℝ) (n : ℕ)
    (a : RealSignedHilbert (signedStepOrder s n)) (k : ℤ) :
    (signedIteratedInclusion s n a).val.val.val k=a.val.val.val k := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change RealSignedHilbert (signedStepOrder s n+1) at a
    change (signedIteratedInclusion s n (signedRealInclusion (signedStepOrder s n) a)).val.val.val k=_
    rw [ih,signedRealInclusion_apply]

namespace SignedSpatialAnalyticEquiv
variable {s t : ℝ}

def iterate (e : SignedSpatialAnalyticEquiv s t) :
    (n : ℕ) → SignedSpatialAnalyticEquiv (signedStepOrder s n) (signedStepOrder t n)
  | 0 => e
  | n+1 => (e.iterate n).succ

theorem iterate_inclusion_apply (e : SignedSpatialAnalyticEquiv s t) (n : ℕ)
    (a : RealSignedHilbert (signedStepOrder s n)) (k : ℤ) :
    ((e.iterate n).equiv a).val.val.val k=
      (e.equiv (signedIteratedInclusion s n a)).val.val.val k := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change RealSignedHilbert (signedStepOrder s n+1) at a
    change ((e.iterate n).succEquiv a).val.val.val k=_
    rw [(e.iterate n).succEquiv_apply,ih]
    rfl

end SignedSpatialAnalyticEquiv
end NLS.WeightedCoeff
