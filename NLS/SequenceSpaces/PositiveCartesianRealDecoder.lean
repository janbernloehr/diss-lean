import NLS.SequenceSpaces.PositiveCartesianRealRotations

/-! # Continuous decoding of real positive Cartesian parameters

The mean occupies the first zero slot. Negative slots and the second
zero slot are ignored. Decoding intertwines every positive real rotation
with the opposite native clockwise rotation, without a nonzero-radius
assumption.
-/
noncomputable section
open Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.WeightedCoeff
variable (w : Weight) (p : ℝ≥0∞) [Fact (1 ≤ p)]

def positiveCartesianRealDecoder : (RealCoeff p × RealCoeff p) →L[ℝ] PositiveCartesianTarget w p :=
  ((positiveCartesianParameterMap w p).restrictScalars ℝ).comp
    ((RealCoeff.complexCLM p).prodMap (RealCoeff.complexCLM p))

theorem positiveCartesianRealDecoder_eval (z : RealCoeff p × RealCoeff p) (n : ℤ) :
    positiveCartesianEval w p n (positiveCartesianRealDecoder w p z) =
      if 0 < n then ((z.1 n : ℂ)/(w n : ℂ),(z.2 n : ℂ)/(w n : ℂ)) else 0 := by
  change positiveCartesianEval w p n (positiveCartesianParameterMap w p _) = _
  rw [positiveCartesianParameterMap_eval]
  rfl

theorem positiveCartesianRealDecoder_real (z : RealCoeff p × RealCoeff p) :
    (∀ n, ((positiveCartesianRealDecoder w p z).1.1.val.val n).im = 0 ∧
      ((positiveCartesianRealDecoder w p z).1.2.val.val n).im = 0) ∧
      (positiveCartesianRealDecoder w p z).2.im = 0 := by
  constructor
  · intro n
    have he := positiveCartesianRealDecoder_eval w p z n
    have hx := congrArg (fun v : ℂ × ℂ => v.1.im) he
    have hy := congrArg (fun v : ℂ × ℂ => v.2.im) he
    by_cases hn : 0 < n
    · rw [if_pos hn] at hx hy
      dsimp only at hx hy
      exact ⟨hx.trans (by rw [← ofReal_div]; exact ofReal_im _),
        hy.trans (by rw [← ofReal_div]; exact ofReal_im _)⟩
    · rw [if_neg hn] at hx hy
      exact ⟨hx,hy⟩
  · change ((z.1 0 : ℝ) : ℂ).im = 0
    exact ofReal_im _

theorem positiveCartesianRealDecoder_parameters (z : PositiveCartesianTarget w p)
    (hr : ∀ n, (z.1.1.val.val n).im = 0 ∧ (z.1.2.val.val n).im = 0) (hm : z.2.im = 0) :
    positiveCartesianRealDecoder w p (positiveCartesianRealParameters w p z) = z := by
  change positiveCartesianParameterMap w p
    (((RealCoeff.complexCLM p).prodMap (RealCoeff.complexCLM p)) (positiveCartesianRealParameters w p z)) = z
  rw [complex_positiveCartesianRealParameters w p z hr hm,positiveCartesianParameterMap_section]

theorem positiveCartesianRealDecoder_rotation (z : RealCoeff p × RealCoeff p)
    (k : ℤ) (hk : 0 < k) (t : ℝ) :
    positiveCartesianRealDecoder w p (RealCoeff.actionRotation z k t) =
      positiveCartesianRotation w p k (-t) (positiveCartesianRealDecoder w p z) := by
  apply positivePairMean_ext
  · intro n hn
    change positiveCartesianEval w p n (positiveCartesianRealDecoder w p (RealCoeff.actionRotation z k t)) =
      positiveCartesianEval w p n (positiveCartesianRotation w p k (-t) (positiveCartesianRealDecoder w p z))
    rw [positiveCartesianRealDecoder_eval,if_pos hn,positiveCartesianRotation_eval]
    by_cases hnk : n = k
    · subst n
      rw [if_pos rfl,positiveCartesianRealDecoder_eval,if_pos hk]
      rw [(RealCoeff.actionRotation_apply_same z k t).1,(RealCoeff.actionRotation_apply_same z k t).2]
      apply Prod.ext <;> simp only [cartesianPlaneRotation,Real.cos_neg,Real.sin_neg,
        ofReal_add,ofReal_sub,ofReal_mul,ofReal_neg] <;> ring
    · rw [if_neg hnk,positiveCartesianRealDecoder_eval,if_pos hn]
      rw [(RealCoeff.actionRotation_apply_ne z k n hnk t).1,(RealCoeff.actionRotation_apply_ne z k n hnk t).2]
  · change ((RealCoeff.actionRotation z k t).1 0 : ℂ) = _
    rw [(RealCoeff.actionRotation_apply_ne z k 0 (ne_of_lt hk) t).1,positiveCartesianRotation_mean]
    rfl

theorem positiveCartesianRealDecoder_negative_rotation (z : RealCoeff p × RealCoeff p)
    (k : ℤ) (hk : k < 0) (t : ℝ) :
    positiveCartesianRealDecoder w p (RealCoeff.actionRotation z k t) = positiveCartesianRealDecoder w p z := by
  apply positivePairMean_ext
  · intro n hn
    change positiveCartesianEval w p n (positiveCartesianRealDecoder w p (RealCoeff.actionRotation z k t)) =
      positiveCartesianEval w p n (positiveCartesianRealDecoder w p z)
    simp only [positiveCartesianRealDecoder_eval,if_pos hn]
    rw [(RealCoeff.actionRotation_apply_ne z k n (by omega) t).1,
      (RealCoeff.actionRotation_apply_ne z k n (by omega) t).2]
  · change ((RealCoeff.actionRotation z k t).1 0 : ℂ) = (z.1 0 : ℂ)
    rw [(RealCoeff.actionRotation_apply_ne z k 0 (by omega) t).1]

end NLS.WeightedCoeff
