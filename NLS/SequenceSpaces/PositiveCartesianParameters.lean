import NLS.SequenceSpaces.PositiveCartesianRotations
import NLS.SequenceSpaces.PositiveRealWeightTransport
import NLS.SequenceSpaces.ComplexActionStationarity

/-! # Unweighted parameters for positive Cartesian pairs and a signed mean

The zero entry of the first sequence carries the mean linearly. Positive
entries carry the weighted Cartesian variables; unused entries are ignored.
The parameter map is a bounded linear split surjection.
-/
noncomputable section
open scoped ENNReal
namespace NLS.WeightedCoeff
variable (w : Weight) (p : ℝ≥0∞) [Fact (1 ≤ p)]

def positiveFromCoeff : Coeff p →L[ℂ] positiveSubmodule w p :=
  (positiveProjection w p).comp (weightIsometry w p).symm.toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem positiveFromCoeff_apply (a : Coeff p) (n : ℤ) :
    (positiveFromCoeff w p a).val.val n = if 0 < n then a n/(w n : ℂ) else 0 := by
  rw [positiveFromCoeff,ContinuousLinearMap.comp_apply,positiveProjection_apply]
  rfl

def positiveCartesianParameterMap : (Coeff p × Coeff p) →L[ℂ] PositiveCartesianTarget w p :=
  ((positiveFromCoeff w p).prodMap (positiveFromCoeff w p)).prod
    ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) p 0).comp (ContinuousLinearMap.fst ℂ _ _))

@[simp] theorem positiveCartesianParameterMap_eval (a : Coeff p × Coeff p) (n : ℤ) :
    positiveCartesianEval w p n (positiveCartesianParameterMap w p a) =
      if 0 < n then (a.1 n/(w n : ℂ),a.2 n/(w n : ℂ)) else 0 := by
  change ((positiveFromCoeff w p a.1).val.val n,(positiveFromCoeff w p a.2).val.val n) = _
  rw [positiveFromCoeff_apply,positiveFromCoeff_apply]
  split_ifs <;> rfl

@[simp] theorem positiveCartesianParameterMap_mean (a : Coeff p × Coeff p) :
    (positiveCartesianParameterMap w p a).2 = a.1 0 := rfl

def positiveToCoeff : positiveSubmodule w p →L[ℂ] Coeff p :=
  (weightIsometry w p).toContinuousLinearEquiv.toContinuousLinearMap.comp (positiveSubmodule w p).subtypeL

@[simp] theorem positiveToCoeff_apply (a : positiveSubmodule w p) (n : ℤ) :
    positiveToCoeff w p a n = (w n : ℂ)*a.val.val n := rfl

def positiveCartesianParameterSection : PositiveCartesianTarget w p →L[ℂ] (Coeff p × Coeff p) :=
  let Q := (positiveToCoeff w p).prodMap (positiveToCoeff w p)
  Q.comp (ContinuousLinearMap.fst ℂ _ ℂ)+
    (((lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) p 0).comp
      (ContinuousLinearMap.snd ℂ _ ℂ)).prod 0)

@[simp] theorem positiveCartesianParameterSection_fst (a : PositiveCartesianTarget w p) (n : ℤ) :
    (positiveCartesianParameterSection w p a).1 n =
      (w n : ℂ)*a.1.1.val.val n+if n = 0 then a.2 else 0 := by
  change positiveToCoeff w p a.1.1 n+(lp.single (E := fun _ : ℤ => ℂ) p 0 a.2) n = _
  simp [lp.single_apply,Pi.single_apply]

@[simp] theorem positiveCartesianParameterSection_snd (a : PositiveCartesianTarget w p) (n : ℤ) :
    (positiveCartesianParameterSection w p a).2 n = (w n : ℂ)*a.1.2.val.val n := by
  change positiveToCoeff w p a.1.2 n+(0 : Coeff p) n = _
  simp

@[simp] theorem positiveCartesianParameterMap_section (a : PositiveCartesianTarget w p) :
    positiveCartesianParameterMap w p (positiveCartesianParameterSection w p a) = a := by
  apply positivePairMean_ext (w := w) (p := p)
  · intro n hn
    change positiveCartesianEval w p n (positiveCartesianParameterMap w p
      (positiveCartesianParameterSection w p a)) = positiveCartesianEval w p n a
    rw [positiveCartesianParameterMap_eval,if_pos hn]
    simp only [positiveCartesianParameterSection_fst,positiveCartesianParameterSection_snd,
      if_neg (ne_of_gt hn),add_zero]
    simp only [mul_div_cancel_left₀ _ (w.complex_ne_zero n)]
    rfl
  · rw [positiveCartesianParameterMap_mean,positiveCartesianParameterSection_fst]
    rw [a.1.1.property 0 le_rfl]
    simp

/-- A positive source rotation becomes the opposite, clockwise native
rotation. Negative source rotations are annihilated; the mean is fixed. -/
theorem positiveCartesianParameterMap_rotationVector (k : ℤ) (hk : k ≠ 0)
    (a : Coeff p × Coeff p) :
    positiveCartesianParameterMap w p (Coeff.actionRotationVectorCLM p k a) =
      if 0 < k then -(positiveCartesianActionVector w p k (positiveCartesianParameterMap w p a)) else 0 := by
  apply positivePairMean_ext (w := w) (p := p)
  · intro n hn
    change positiveCartesianEval w p n (positiveCartesianParameterMap w p
      (Coeff.actionRotationVectorCLM p k a)) =
      positiveCartesianEval w p n (if 0 < k then
        -(positiveCartesianActionVector w p k (positiveCartesianParameterMap w p a)) else 0)
    rw [positiveCartesianParameterMap_eval,if_pos hn,Coeff.actionRotationVectorCLM_apply]
    split_ifs with hkp
    · rw [map_neg,positiveCartesianActionVector_eval,positiveCartesianParameterMap_eval,if_pos hn]
      by_cases hnk : n = k
      · subst n
        simp [lp.single_apply,neg_div]
      · simp [lp.single_apply,hnk]
    · have hnk : n ≠ k := by omega
      simp [lp.single_apply,hnk]
  · rw [positiveCartesianParameterMap_mean,Coeff.actionRotationVectorCLM_apply]
    change -(lp.single (E := fun _ : ℤ => ℂ) p k (a.2 k)) 0 = _
    simp only [lp.single_apply,Pi.single_eq_of_ne (Ne.symm hk),neg_zero]
    split_ifs
    · change 0 = -(0 : ℂ)
      simp
    · rfl

end NLS.WeightedCoeff
