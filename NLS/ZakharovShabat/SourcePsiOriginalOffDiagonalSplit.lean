import NLS.ZakharovShabat.SourcePsiOriginalNormLimit
import NLS.SequenceSpaces.NormPower

/-!
# Exact original off-diagonal decompositions

The omitted row and column of the off-diagonal Jacobian vanish. The
error norm splits into the omitted row and retained rows. Those rows
split into retained input and the limit column, with factor 2^(p-1).
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The off-diagonal part of the full original Jacobian has zero omitted row. -/
theorem sourcePsiOriginal_offDiagonal_apply_same
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (a : Coeff p) (φ : CoeffPair p) (h : Coeff p) :
    (Coeff.operatorOffDiagonal (sourcePsiOriginalFullRootJacobian hp hp1 n a φ) h) n = 0 := by
  simp [Coeff.operatorOffDiagonal,sourcePsiOriginalFullRootJacobian,
    Coeff.deletedJacobianExtension]

/-- The actual off-diagonal norm splits exactly into the distinguished row
and the retained rows, before estimating either contribution. -/
theorem sourcePsiOriginal_offDiagonalDifference_norm_rpow
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (a : Coeff p) (φ : CoeffPair p) (h : Coeff p) :
    ‖(Coeff.operatorOffDiagonal (sourcePsiOriginalLimitOperator hp hp1 a φ)-
      Coeff.operatorOffDiagonal (sourcePsiOriginalFullRootJacobian hp hp1 n a φ)) h‖ ^ p.toReal =
      ‖(Coeff.operatorOffDiagonal (sourcePsiOriginalLimitOperator hp hp1 a φ) h) n‖ ^ p.toReal+
      ∑' m : ℤ, if m = n then 0 else
        ‖((Coeff.operatorOffDiagonal (sourcePsiOriginalLimitOperator hp hp1 a φ)-
          Coeff.operatorOffDiagonal (sourcePsiOriginalFullRootJacobian hp hp1 n a φ)) h) m‖ ^ p.toReal := by
  classical
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos (zero_lt_one.trans hp1).ne' hp
  let b : Coeff p := (Coeff.operatorOffDiagonal (sourcePsiOriginalLimitOperator hp hp1 a φ)-
    Coeff.operatorOffDiagonal (sourcePsiOriginalFullRootJacobian hp hp1 n a φ)) h
  change ‖b‖ ^ p.toReal = _
  rw [lp.norm_rpow_eq_tsum hp0,((lp.memℓp b).summable hp0).tsum_eq_add_tsum_ite n]
  congr 1
  simp only [b,sub_apply,lp.coeFn_sub,Pi.sub_apply,
    sourcePsiOriginal_offDiagonal_apply_same,sub_zero]

end NLS.ZakharovShabat

namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The off-diagonal Jacobian also has zero omitted input column. -/
theorem sourcePsiOriginal_offDiagonal_single_same
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (a : Coeff p) (φ : CoeffPair p) (t : ℂ) :
    Coeff.operatorOffDiagonal (sourcePsiOriginalFullRootJacobian hp hp1 n a φ)
      (lp.single p n t) = 0 := by
  ext m
  by_cases hmn : m = n
  · subst m
    simp only [sourcePsiOriginal_offDiagonal_apply_same,lp.coeFn_zero,Pi.zero_apply]
  · simp [Coeff.operatorOffDiagonal,sourcePsiOriginalFullRootJacobian,
      Coeff.deletedJacobianExtension,Coeff.deletedOperatorExtension_single_same,
      lp.single_apply,hmn]

/-- The retained output splits into the retained-input term and the
single omitted-input column of the actual limit operator. -/
theorem sourcePsiOriginal_offDiagonal_remainingRows_split
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (a : Coeff p) (φ : CoeffPair p) (h : Coeff p) :
    Coeff.deleteCoordinate n
      ((Coeff.operatorOffDiagonal (sourcePsiOriginalLimitOperator hp hp1 a φ)-
        Coeff.operatorOffDiagonal (sourcePsiOriginalFullRootJacobian hp hp1 n a φ)) h) =
      Coeff.deleteCoordinate n
        ((Coeff.operatorOffDiagonal (sourcePsiOriginalLimitOperator hp hp1 a φ)-
          Coeff.operatorOffDiagonal (sourcePsiOriginalFullRootJacobian hp hp1 n a φ))
            (Coeff.deleteCoordinate n h)) +
      Coeff.deleteCoordinate n
        (Coeff.operatorOffDiagonal (sourcePsiOriginalLimitOperator hp hp1 a φ)
          (lp.single p n (h n))) := by
  let T := Coeff.operatorOffDiagonal (sourcePsiOriginalLimitOperator hp hp1 a φ)-
    Coeff.operatorOffDiagonal (sourcePsiOriginalFullRootJacobian hp hp1 n a φ)
  have hdec : h = Coeff.deleteCoordinate n h+lp.single p n (h n) := by
    ext m
    by_cases hmn : m = n
    · subst m
      simp
    · simp [Coeff.deleteCoordinate_apply_other n m hmn,lp.single_apply,hmn]
  have hsplit : T h = T (Coeff.deleteCoordinate n h)+T (lp.single p n (h n)) := by
    calc
      T h = T (Coeff.deleteCoordinate n h+lp.single p n (h n)) := congrArg T hdec
      _ = _ := T.map_add _ _
  change Coeff.deleteCoordinate n (T h) = _
  rw [hsplit,map_add]
  simp only [T,sub_apply,sourcePsiOriginal_offDiagonal_single_same,sub_zero]

/-- The two remaining-row contributions have the explicit power factor
2^(p-1), applied to the actual source operators. -/
theorem sourcePsiOriginal_offDiagonal_remainingRows_rpow_le
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (a : Coeff p) (φ : CoeffPair p) (h : Coeff p) :
    ‖Coeff.deleteCoordinate n
      ((Coeff.operatorOffDiagonal (sourcePsiOriginalLimitOperator hp hp1 a φ)-
        Coeff.operatorOffDiagonal (sourcePsiOriginalFullRootJacobian hp hp1 n a φ)) h)‖ ^ p.toReal ≤
      (2:ℝ) ^ (p.toReal-1) *
        (‖Coeff.deleteCoordinate n
          ((Coeff.operatorOffDiagonal (sourcePsiOriginalLimitOperator hp hp1 a φ)-
            Coeff.operatorOffDiagonal (sourcePsiOriginalFullRootJacobian hp hp1 n a φ))
              (Coeff.deleteCoordinate n h))‖ ^ p.toReal +
        ‖Coeff.deleteCoordinate n
          (Coeff.operatorOffDiagonal (sourcePsiOriginalLimitOperator hp hp1 a φ)
            (lp.single p n (h n)))‖ ^ p.toReal) := by
  rw [sourcePsiOriginal_offDiagonal_remainingRows_split]
  exact Coeff.norm_add_rpow_le_two_mul hp _ _

end NLS.ZakharovShabat
