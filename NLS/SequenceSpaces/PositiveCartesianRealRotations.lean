import NLS.SequenceSpaces.PositiveCartesianRealParameters

/-! # Native rotations in real normalized parameters -/
noncomputable section
open Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.WeightedCoeff
variable (w : Weight) (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- Clockwise native rotations become standard real rotations at the
opposite time. The mean head is unchanged. -/
theorem positiveCartesianRealParameters_rotation (z : PositiveCartesianTarget w p)
    (k : ℤ) (hk : 0 < k) (t : ℝ) :
    positiveCartesianRealParameters w p (positiveCartesianRotation w p k t z) =
      RealCoeff.actionRotation (positiveCartesianRealParameters w p z) k (-t) := by
  have hcoord (n : ℤ) :
      (positiveCartesianRealParameters w p (positiveCartesianRotation w p k t z)).1 n =
        (RealCoeff.actionRotation (positiveCartesianRealParameters w p z) k (-t)).1 n ∧
      (positiveCartesianRealParameters w p (positiveCartesianRotation w p k t z)).2 n =
        (RealCoeff.actionRotation (positiveCartesianRealParameters w p z) k (-t)).2 n := by
    have he := positiveCartesianRotation_eval w p k n t z
    by_cases hn : n = k
    · subst n
      rw [if_pos rfl] at he
      have hx := congrArg Prod.fst he
      have hy := congrArg Prod.snd he
      change (positiveCartesianRotation w p k t z).1.1.val.val k =
        (Real.cos t : ℂ)*z.1.1.val.val k+(Real.sin t : ℂ)*z.1.2.val.val k at hx
      change (positiveCartesianRotation w p k t z).1.2.val.val k =
        -(Real.sin t : ℂ)*z.1.1.val.val k+(Real.cos t : ℂ)*z.1.2.val.val k at hy
      constructor
      · rw [(RealCoeff.actionRotation_apply_same _ k (-t)).1]
        simp only [positiveCartesianRealParameters_fst,positiveCartesianRealParameters_snd,
          hx,positiveCartesianRotation_mean,if_neg (ne_of_gt hk),add_zero,
          Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
          zero_mul,sub_zero,Real.cos_neg,Real.sin_neg]
        ring
      · rw [(RealCoeff.actionRotation_apply_same _ k (-t)).2]
        simp only [positiveCartesianRealParameters_fst,positiveCartesianRealParameters_snd,
          hy,if_neg (ne_of_gt hk),add_zero,Complex.add_re,Complex.mul_re,
          Complex.neg_re,Complex.neg_im,Complex.ofReal_re,Complex.ofReal_im,
          neg_zero,zero_mul,sub_zero,Real.cos_neg,Real.sin_neg]
        ring
    · rw [if_neg hn] at he
      have hx := congrArg Prod.fst he
      have hy := congrArg Prod.snd he
      change (positiveCartesianRotation w p k t z).1.1.val.val n = z.1.1.val.val n at hx
      change (positiveCartesianRotation w p k t z).1.2.val.val n = z.1.2.val.val n at hy
      constructor
      · rw [(RealCoeff.actionRotation_apply_ne _ k n hn (-t)).1]
        simp only [positiveCartesianRealParameters_fst]
        rw [hx,positiveCartesianRotation_mean]
      · rw [(RealCoeff.actionRotation_apply_ne _ k n hn (-t)).2]
        simp only [positiveCartesianRealParameters_snd]
        rw [hy]
  apply Prod.ext <;> ext n
  · exact (hcoord n).1
  · exact (hcoord n).2

theorem actionRotation_positiveCartesianRealParameters_negative (z : PositiveCartesianTarget w p)
    (k : ℤ) (hk : k < 0) (t : ℝ) :
    RealCoeff.actionRotation (positiveCartesianRealParameters w p z) k t =
      positiveCartesianRealParameters w p z := by
  apply RealCoeff.actionRotation_eq_self_of_action_zero
  obtain ⟨hx,hy⟩ := positiveCartesianRealParameters_negative w p z k hk
  simp [RealCoeff.pairAction,hx,hy]

/-- Equal real Cartesian radii and signed mean give equal actions in
every normalized plane, including the unused encoding slots. -/
theorem pairAction_realParameters_eq_of_radii (z v : PositiveCartesianTarget w p)
    (hz : ∀ n, (z.1.1.val.val n).im = 0 ∧ (z.1.2.val.val n).im = 0)
    (hv : ∀ n, (v.1.1.val.val n).im = 0 ∧ (v.1.2.val.val n).im = 0)
    (hm : z.2 = v.2)
    (hr : ∀ n : ℤ, 0 < n →
      (z.1.1.val.val n)^2+(z.1.2.val.val n)^2 = (v.1.1.val.val n)^2+(v.1.2.val.val n)^2)
    (n : ℤ) :
    RealCoeff.pairAction (positiveCartesianRealParameters w p z) n =
      RealCoeff.pairAction (positiveCartesianRealParameters w p v) n := by
  by_cases hn : 0 < n
  · have he := congrArg Complex.re (hr n hn)
    simp only [Complex.add_re,pow_two,Complex.mul_re,(hz n).1,(hz n).2,
      (hv n).1,(hv n).2,mul_zero,sub_zero] at he
    simp only [RealCoeff.pairAction,positiveCartesianRealParameters_fst,
      positiveCartesianRealParameters_snd,if_neg (ne_of_gt hn),add_zero]
    linear_combination (w n)^2/2*he
  · by_cases h0 : n = 0
    · subst n
      simp only [RealCoeff.pairAction,(positiveCartesianRealParameters_zero w p z).1,
        (positiveCartesianRealParameters_zero w p z).2,
        (positiveCartesianRealParameters_zero w p v).1,
        (positiveCartesianRealParameters_zero w p v).2,hm]
    · have hneg : n < 0 := by omega
      obtain ⟨hzx,hzy⟩ := positiveCartesianRealParameters_negative w p z n hneg
      obtain ⟨hvx,hvy⟩ := positiveCartesianRealParameters_negative w p v n hneg
      simp only [RealCoeff.pairAction,hzx,hzy,hvx,hvy]

end NLS.WeightedCoeff
