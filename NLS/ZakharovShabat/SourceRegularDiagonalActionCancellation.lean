import NLS.ZakharovShabat.SourceNormalizedSecondMomentAnalytic
import NLS.ZakharovShabat.SourceNormalizedWeightedAction

/-! Exact cancellation of the free diagonal moment against twice the
first weighted action. All normalized factors are regular at closed gaps;
this identity alone does not assert a sequence estimate for its errors. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceFullAbelianUniformCauchyFamily
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}

def regularDiagonalSecondMomentError (C : SourceFullAbelianUniformCauchyFamily hp hp1 W)
    (s : (n : ℤ) → CoeffPair p → DeletedCoeff p n) (n : ℤ) (ψ : CoeffPair p) : ℂ :=
  4*C.normalizedSecondMoment s n n ψ-(Real.pi : ℂ)

def regularFirstWeightedActionError (C : SourceFullAbelianUniformCauchyFamily hp hp1 W)
    (n : ℤ) (ψ : CoeffPair p) : ℂ :=
  4*C.normalizedWeightedAction n 1 ψ-(Real.pi : ℂ)*n

theorem diagonal_action_cancellation
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W)
    {V : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
    (A : SourceAbelianMomentAtlas hp hp1 V s) (D : SourceAbelianMomentErrorDomain A)
    (ψ : CoeffPair p) (hψ : ψ∈D.domain)
    (hC : ψ∈ball C.discs.source.val C.discs.sourceRadius) (n : ℤ)
    (hA : sourceComplexHigherAction hp hp1 n 1 ψ=
      (sourcePeriodicGapDisplacement hp hp1 ψ n)^2*C.normalizedWeightedAction n 1 ψ) :
    -12*(n : ℂ)*(A.moment n n 2 ψ-A.moment n (-n) 2 ψ)+
        12*sourceComplexHigherAction hp hp1 n 1 ψ =
      3*(sourcePeriodicGapDisplacement hp hp1 ψ n)^2*
        (C.regularFirstWeightedActionError n ψ-(n : ℂ)*C.regularDiagonalSecondMomentError s n ψ)+
        12*(n : ℂ)*(sourcePeriodicGapDisplacement hp hp1 ψ (-n))^2*
          C.normalizedSecondMoment s n (-n) ψ := by
  rw [C.moment_two_eq_squaredGap_mul_normalized A D ψ hψ hC n n,
    C.moment_two_eq_squaredGap_mul_normalized A D ψ hψ hC n (-n),hA]
  unfold regularFirstWeightedActionError regularDiagonalSecondMomentError
  ring

theorem exists_ball_regular_diagonal_action_cancellation
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W)
    {V R : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
    (hs : SourcePsiIsolatingComplexExtension hp hp1 V s) (hV : IsOpen V)
    (A : SourceAbelianMomentAtlas hp hp1 R s) (D : SourceAbelianMomentErrorDomain A)
    (φ : realTypeSourceSubmodule p) (hφV : φ.val∈V)
    (hφC : φ.val∈ball C.discs.source.val C.discs.sourceRadius) :
    ∃ r : ℝ, 0<r ∧ ball φ.val r⊆D.domain∩V∩ball C.discs.source.val C.discs.sourceRadius ∧
      (∀ n k : ℤ, AnalyticOnNhd ℂ (C.normalizedSecondMoment s n k) (ball φ.val r)) ∧
      (∀ n : ℤ, AnalyticOnNhd ℂ (C.regularDiagonalSecondMomentError s n) (ball φ.val r) ∧
        AnalyticOnNhd ℂ (C.regularFirstWeightedActionError n) (ball φ.val r)) ∧
      ∀ ψ∈ball φ.val r, ∀ n : ℤ,
        -12*(n : ℂ)*(A.moment n n 2 ψ-A.moment n (-n) 2 ψ)+
            12*sourceComplexHigherAction hp hp1 n 1 ψ =
          3*(sourcePeriodicGapDisplacement hp hp1 ψ n)^2*
            (C.regularFirstWeightedActionError n ψ-(n : ℂ)*C.regularDiagonalSecondMomentError s n ψ)+
            12*(n : ℂ)*(sourcePeriodicGapDisplacement hp hp1 ψ (-n))^2*
              C.normalizedSecondMoment s n (-n) ψ := by
  obtain ⟨a,ha,hasub,hNa⟩ := C.exists_ball_normalizedSecondMoments hs hV φ hφV hφC
  obtain ⟨b,hb,_hbsub,hNb⟩ := C.exists_ball_normalizedWeightedActions
    (sourceHigherActionAtlas hp hp1) φ hφC
  obtain ⟨d,hd,hdsub⟩ := Metric.mem_nhds_iff.mp (D.isOpen_domain.mem_nhds (D.real_subset φ.property))
  let r := min a (min b d)
  have hra : ball φ.val r⊆ball φ.val a := ball_subset_ball (min_le_left _ _)
  have hrb : ball φ.val r⊆ball φ.val b := ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _))
  have hrd : ball φ.val r⊆ball φ.val d := ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨r,lt_min ha (lt_min hb hd),fun ψ hψ => ⟨⟨hdsub (hrd hψ),(hasub (hra hψ)).1⟩,
    (hasub (hra hψ)).2⟩,fun n k => (hNa n k).mono hra,?_,?_⟩
  · intro n
    constructor
    · exact (analyticOnNhd_const.mul ((hNa n n).mono hra)).sub analyticOnNhd_const
    · exact (analyticOnNhd_const.mul (((hNb n 1).1).mono hrb)).sub analyticOnNhd_const
  · intro ψ hψ n
    apply C.diagonal_action_cancellation A D ψ (hdsub (hrd hψ)) (hasub (hra hψ)).2 n
    simpa only [sourcePeriodicGapDisplacement_apply,sourceComplexHigherAction] using (hNb n 1).2 ψ (hrb hψ)

end SourceFullAbelianUniformCauchyFamily
end NLS.ZakharovShabat
