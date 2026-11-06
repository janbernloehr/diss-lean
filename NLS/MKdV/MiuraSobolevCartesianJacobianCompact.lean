import NLS.MKdV.MiuraSobolevNLSJacobianCompact
import NLS.MKdV.MiuraSobolevCartesianFreeEquivalence

/-! # Compact Cartesian derivative remainders in every native Sobolev norm

The scaled root is a bounded analytic symbol. Multiplying its derivative
by the fixed native NLS sequence is compact; the other terms use the
weighted NLS compact remainder and the root's vanishing tail remainder.
-/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

def miuraSobolevCartesianRootSequence (s : ℕ) (a : ScalarSobolev s) : Coeff ⊤ :=
  miuraCartesianRootSequence (hierarchySobolevJetL2 s 0 (Nat.zero_le s) a)

theorem analyticAt_miuraSobolevCartesianRootSequence (s : ℕ) (a : ScalarSobolev s)
    (ha : ∀ j, a.val j = conj (a.val (-j))) :
    AnalyticAt ℂ (miuraSobolevCartesianRootSequence s) a := by
  have hr : ∀ j, hierarchySobolevJetL2 s 0 (Nat.zero_le s) a j =
      conj (hierarchySobolevJetL2 s 0 (Nat.zero_le s) a (-j)) := by
    intro j
    simpa only [hierarchySobolevJetL2_apply,pow_zero,one_mul] using ha j
  exact (analyticAt_miuraCartesianRootSequence _ hr).comp
    ((hierarchySobolevJetL2 s 0 (Nat.zero_le s)).analyticAt a)

theorem isCompactOperator_fderiv_miuraSobolevScaledNLSCoordinate_sub_free
    (s : ℕ) (L : (Coeff 2 × Coeff 2) →L[ℂ] Coeff 2) (a : ScalarSobolev s)
    (ha : ∀ j, a.val j = conj (a.val (-j))) :
    IsCompactOperator
      (fderiv ℂ (fun b => Coeff.multiplier (miuraSobolevCartesianRootSequence s b)
        (L (miuraSobolevNLSNormalizedCoordinates s b))) a-
      fderiv ℂ (fun b => Coeff.multiplier (miuraSobolevCartesianRootSequence s b)
        (L (miuraSobolevNLSNormalizedCoordinates s b))) 0) := by
  have hzero : ∀ j : ℤ, (0 : ScalarSobolev s).val j = conj ((0 : ScalarSobolev s).val (-j)) := by
    intro j
    simp
  have hF := L.hasFDerivAt.comp a (hasFDerivAt_miuraSobolevNLSNormalizedCoordinates s a ha)
  have hF₀ := L.hasFDerivAt.comp 0 (hasFDerivAt_miuraSobolevNLSNormalizedCoordinates s 0 hzero)
  change HasFDerivAt (fun b => L (miuraSobolevNLSNormalizedCoordinates s b)) _ a at hF
  change HasFDerivAt (fun b => L (miuraSobolevNLSNormalizedCoordinates s b)) _ 0 at hF₀
  have hc : IsCompactOperator
      (fderiv ℂ (fun b => L (miuraSobolevNLSNormalizedCoordinates s b)) a-
        fderiv ℂ (fun b => L (miuraSobolevNLSNormalizedCoordinates s b)) 0) := by
    rw [hF.fderiv,hF₀.fderiv,← ContinuousLinearMap.comp_sub]
    have h := (isCompactOperator_fderiv_miuraSobolevNLSNormalizedCoordinates_sub_free s a ha).clm_comp L
    rwa [(hasFDerivAt_miuraSobolevNLSNormalizedCoordinates s a ha).fderiv,
      (hasFDerivAt_miuraSobolevNLSNormalizedCoordinates s 0 hzero).fderiv] at h
  have hr : ∀ j, hierarchySobolevJetL2 s 0 (Nat.zero_le s) a j =
      conj (hierarchySobolevJetL2 s 0 (Nat.zero_le s) a (-j)) := by
    intro j
    simpa only [hierarchySobolevJetL2_apply,pow_zero,one_mul] using ha j
  have ht : IsCompactOperator (Coeff.multiplierCLM (p := 2)
      (miuraSobolevCartesianRootSequence s a-miuraSobolevCartesianRootSequence s 0)) := by
    simpa only [miuraSobolevCartesianRootSequence,map_zero] using
      isCompactOperator_miuraCartesianRootSequence_sub_free _ hr
  exact Coeff.isCompactOperator_fderiv_multiplier_sub_zero (by simp)
    (miuraSobolevCartesianRootSequence s) (fun b => L (miuraSobolevNLSNormalizedCoordinates s b)) a
    (analyticAt_miuraSobolevCartesianRootSequence s a ha).differentiableAt hF.differentiableAt
    (analyticAt_miuraSobolevCartesianRootSequence s 0 hzero).differentiableAt hF₀.differentiableAt
    (by rw [miuraSobolevNLSNormalizedCoordinates_zero,map_zero]) hc ht

def miuraSobolevCartesianRetraction (s : ℕ) : Coeff 2 →L[ℂ] MiuraPositiveSobolevHalf s :=
  (WeightedCoeff.positiveProjection (miuraCartesianWeight s) 2).comp
    (WeightedCoeff.weightIsometry (miuraCartesianWeight s) 2).symm.toContinuousLinearEquiv.toContinuousLinearMap

def miuraSobolevCartesianDenormalization (s : ℕ) :
    MiuraNormalizedCartesianTarget →L[ℂ] MiuraPositiveSobolevTarget s :=
  ((miuraSobolevCartesianRetraction s).prodMap (miuraSobolevCartesianRetraction s)).prodMap
    (ContinuousLinearMap.id ℂ ℂ)

def miuraSobolevScaledNLSCartesianMap (s : ℕ) (a : ScalarSobolev s) : MiuraNormalizedCartesianTarget :=
  ((Coeff.multiplier (miuraSobolevCartesianRootSequence s a) (miuraSobolevNLSNormalizedCoordinates s a).1,
    -(Coeff.multiplier (miuraSobolevCartesianRootSequence s a) (miuraSobolevNLSNormalizedCoordinates s a).2)),a.val 0)

theorem miuraSobolevCartesianDenormalization_map (s : ℕ) (a : ScalarSobolev s) :
    miuraSobolevCartesianDenormalization s (miuraSobolevScaledNLSCartesianMap s a) =
      miuraSobolevPositiveCartesianMap s a := by
  have he : miuraSobolevCartesianRootSequence s a =
      sourceDiagonalActionRootSequence (miuraSobolevActionSource s a) := by
    rw [miuraSobolevCartesianRootSequence,miuraCartesianRootSequence,miuraSobolevActionSource_eq_L2_diagonal]
  change
    (((WeightedCoeff.positiveProjection (miuraCartesianWeight s) 2)
      ((WeightedCoeff.weightIsometry (miuraCartesianWeight s) 2).symm
        (Coeff.multiplier (miuraSobolevCartesianRootSequence s a) (miuraSobolevNLSNormalizedCoordinates s a).1)),
     (WeightedCoeff.positiveProjection (miuraCartesianWeight s) 2)
      ((WeightedCoeff.weightIsometry (miuraCartesianWeight s) 2).symm
        (-(Coeff.multiplier (miuraSobolevCartesianRootSequence s a) (miuraSobolevNLSNormalizedCoordinates s a).2)))),a.val 0) =
    (((WeightedCoeff.positiveProjection (miuraCartesianWeight s) 2)
      ((WeightedCoeff.weightIsometry (miuraCartesianWeight s) 2).symm
        (Coeff.multiplier (sourceDiagonalActionRootSequence (miuraSobolevActionSource s a)) (miuraSobolevNLSNormalizedCoordinates s a).1)),
     (WeightedCoeff.positiveProjection (miuraCartesianWeight s) 2)
      ((WeightedCoeff.weightIsometry (miuraCartesianWeight s) 2).symm
        (-(Coeff.multiplier (sourceDiagonalActionRootSequence (miuraSobolevActionSource s a)) (miuraSobolevNLSNormalizedCoordinates s a).2)))),a.val 0)
  rw [he]

theorem hasFDerivAt_miuraSobolevScaledNLSCartesianMap (s : ℕ) (a : ScalarSobolev s)
    (ha : ∀ j, a.val j = conj (a.val (-j))) :
    HasFDerivAt (miuraSobolevScaledNLSCartesianMap s)
      (((fderiv ℂ (fun b => Coeff.multiplier (miuraSobolevCartesianRootSequence s b)
          (miuraSobolevNLSNormalizedCoordinates s b).1) a).prod
        (-(fderiv ℂ (fun b => Coeff.multiplier (miuraSobolevCartesianRootSequence s b)
          (miuraSobolevNLSNormalizedCoordinates s b).2) a))).prod
            (WeightedCoeff.evalCLM (Weight.sobolev (s : ℝ)) 2 0)) a := by
  have hm := (analyticAt_miuraSobolevCartesianRootSequence s a ha).differentiableAt
  have hz := (hasFDerivAt_miuraSobolevNLSNormalizedCoordinates s a ha).differentiableAt
  have hx := (((Coeff.multiplierBilinear (p := 2)).differentiableAt.comp a hm).clm_apply hz.fst)
  have hy := (((Coeff.multiplierBilinear (p := 2)).differentiableAt.comp a hm).clm_apply hz.snd)
  exact (hx.hasFDerivAt.prodMk hy.hasFDerivAt.neg).prodMk
    (WeightedCoeff.evalCLM (Weight.sobolev (s : ℝ)) 2 0).hasFDerivAt

/-- In the full native norms, every real Cartesian derivative is a
compact perturbation of the explicit free Banach equivalence. -/
theorem isCompactOperator_miuraSobolevCartesianJacobian_sub_free (s : ℕ) (a : ScalarSobolev s)
    (ha : ∀ j, a.val j = conj (a.val (-j))) :
    IsCompactOperator (fderiv ℂ (miuraSobolevPositiveCartesianMap s) a-
      (miuraSobolevCartesianFreeEquiv s).toContinuousLinearMap) := by
  have hzero : ∀ j : ℤ, (0 : ScalarSobolev s).val j = conj ((0 : ScalarSobolev s).val (-j)) := by
    intro j
    simp
  let X := fun b => Coeff.multiplier (miuraSobolevCartesianRootSequence s b) (miuraSobolevNLSNormalizedCoordinates s b).1
  let Y := fun b => Coeff.multiplier (miuraSobolevCartesianRootSequence s b) (miuraSobolevNLSNormalizedCoordinates s b).2
  have hx : IsCompactOperator (fderiv ℂ X a-fderiv ℂ X 0) :=
    isCompactOperator_fderiv_miuraSobolevScaledNLSCoordinate_sub_free s (ContinuousLinearMap.fst ℂ _ _) a ha
  have hy : IsCompactOperator (fderiv ℂ Y a-fderiv ℂ Y 0) :=
    isCompactOperator_fderiv_miuraSobolevScaledNLSCoordinate_sub_free s (ContinuousLinearMap.snd ℂ _ _) a ha
  have hxy := Coeff.isCompactOperator_prodCLM
    (fderiv ℂ X a-fderiv ℂ X 0) (-(fderiv ℂ Y a-fderiv ℂ Y 0)) hx hy.neg
  have hc := Coeff.isCompactOperator_prodCLM
    ((fderiv ℂ X a-fderiv ℂ X 0).prod (-(fderiv ℂ Y a-fderiv ℂ Y 0)))
    (0 : ScalarSobolev s →L[ℂ] ℂ) hxy isCompactOperator_zero
  have hd (b : ScalarSobolev s) (hb : ∀ j, b.val j = conj (b.val (-j))) :
      fderiv ℂ (miuraSobolevPositiveCartesianMap s) b =
      (miuraSobolevCartesianDenormalization s).comp
        (((fderiv ℂ X b).prod (-(fderiv ℂ Y b))).prod
          (WeightedCoeff.evalCLM (Weight.sobolev (s : ℝ)) 2 0)) := by
    have h := (miuraSobolevCartesianDenormalization s).hasFDerivAt.comp b
      (hasFDerivAt_miuraSobolevScaledNLSCartesianMap s b hb)
    have he := funext (miuraSobolevCartesianDenormalization_map s)
    change HasFDerivAt (fun c => miuraSobolevCartesianDenormalization s (miuraSobolevScaledNLSCartesianMap s c)) _ b at h
    rw [he] at h
    exact h.fderiv
  rw [← miuraSobolevCartesianFreeJacobian_eq_equiv]
  change IsCompactOperator (fderiv ℂ (miuraSobolevPositiveCartesianMap s) a-
    fderiv ℂ (miuraSobolevPositiveCartesianMap s) 0)
  have he : fderiv ℂ (miuraSobolevPositiveCartesianMap s) a-
      fderiv ℂ (miuraSobolevPositiveCartesianMap s) 0 =
      (miuraSobolevCartesianDenormalization s).comp
        (((fderiv ℂ X a-fderiv ℂ X 0).prod (-(fderiv ℂ Y a-fderiv ℂ Y 0))).prod 0) := by
    rw [hd a ha,hd 0 hzero]
    apply ContinuousLinearMap.ext
    intro h
    change miuraSobolevCartesianDenormalization s
      ((fderiv ℂ X a h,-(fderiv ℂ Y a h)),h.val 0)-
      miuraSobolevCartesianDenormalization s
      ((fderiv ℂ X 0 h,-(fderiv ℂ Y 0 h)),h.val 0) =
      miuraSobolevCartesianDenormalization s
      ((fderiv ℂ X a h-fderiv ℂ X 0 h,-(fderiv ℂ Y a h-fderiv ℂ Y 0 h)),0)
    rw [← map_sub]
    apply congrArg (miuraSobolevCartesianDenormalization s)
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · change -(fderiv ℂ Y a h)- -(fderiv ℂ Y 0 h) = -((fderiv ℂ Y a h)-(fderiv ℂ Y 0 h))
        abel
    · exact sub_self _
  rw [he]
  exact hc.clm_comp (miuraSobolevCartesianDenormalization s)

end NLS.MKdV
