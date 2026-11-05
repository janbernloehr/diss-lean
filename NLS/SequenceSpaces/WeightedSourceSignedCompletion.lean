import NLS.SequenceSpaces.SignedHolomorphicCompletion
import NLS.SequenceSpaces.ConjugateReflection

/-! # Signed holomorphic completion with a weighted source

Transport the existing Hilbert-source completion through the source weight
isometry. The source and target weights may differ; symmetric real weights
retain literal physical conjugate reflection in both spaces.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
open scoped ComplexConjugate
namespace NLS.WeightedCoeff

theorem weightIsometry_conjugateReflection (v : Weight) (hv : ∀ j, v (-j)=v j)
    (q : WeightedCoeff v 2) :
    periodOneL2Conjugation (weightIsometry v 2 q)=
      weightIsometry v 2 (conjugateReflection v hv q) := by
  change periodOneL2Conjugation (weightEquiv v 2 q)=
    weightEquiv v 2 ((weightEquiv v 2).symm (periodOneL2Conjugation (weightEquiv v 2 q)))
  rw [LinearEquiv.apply_symm_apply]

theorem weightIsometry_fixed_iff_raw (v : Weight) (hv : ∀ j, v (-j)=v j)
    (q : WeightedCoeff v 2) :
    periodOneL2Conjugation (weightIsometry v 2 q)=weightIsometry v 2 q ↔
      ∀ j : ℤ, q.val (-j)=conj (q.val j) := by
  rw [weightIsometry_conjugateReflection v hv]
  constructor
  · intro he j
    have hq := (weightIsometry v 2).injective he
    have hh := congrArg (fun a : WeightedCoeff v 2 => a.val (-j)) hq
    simpa only [conjugateReflection_apply,neg_neg] using hh.symm
  · intro hr
    apply congrArg (weightIsometry v 2)
    apply Subtype.ext
    funext j
    rw [conjugateReflection_apply,hr j,conj_conj]

def weightedSourceSignedCompletion (v w : Weight)
    (Y : WeightedCoeff v 2 → WeightedCoeff w 2) (q : WeightedCoeff v 2) : WeightedCoeff w 2 :=
  signedHolomorphicCompletion w (fun u => Y ((weightIsometry v 2).symm u)) (weightIsometry v 2 q)

theorem weightedSourceSignedCompletion_apply (v w : Weight)
    (hv : ∀ j, v (-j)=v j) (hw : ∀ j, w (-j)=w j)
    (Y : WeightedCoeff v 2 → WeightedCoeff w 2) (q : WeightedCoeff v 2) (j : ℤ) :
    (weightedSourceSignedCompletion v w Y q).val j=
      (Y q).val j+conj ((Y (conjugateReflection v hv q)).val (-j)) := by
  rw [weightedSourceSignedCompletion,signedHolomorphicCompletion_apply w hw,
    weightIsometry_conjugateReflection v hv]
  simp only [LinearIsometryEquiv.symm_apply_apply]

theorem weightedSourceSignedCompletion_analytic_bound (v w : Weight)
    (Y : WeightedCoeff v 2 → WeightedCoeff w 2) (η C : ℝ)
    (hYa : AnalyticOnNhd ℂ Y (ball (0 : WeightedCoeff v 2) η)) (hY0 : Y 0=0)
    (hYb : ∀ q∈ball (0 : WeightedCoeff v 2) η, ‖Y q‖≤C*(‖q‖+‖q‖^2)) :
    AnalyticOnNhd ℂ (weightedSourceSignedCompletion v w Y) (ball (0 : WeightedCoeff v 2) η) ∧
      weightedSourceSignedCompletion v w Y 0=0 ∧
      ∀ q∈ball (0 : WeightedCoeff v 2) η,
        ‖weightedSourceSignedCompletion v w Y q‖≤2*C*(‖q‖+‖q‖^2) := by
  let I := weightIsometry v 2
  let F : Coeff 2 → WeightedCoeff w 2 := fun u => Y (I.symm u)
  have hmem (u : Coeff 2) (hu : u∈ball 0 η) : I.symm u∈ball (0 : WeightedCoeff v 2) η := by
    simpa only [mem_ball_zero_iff,LinearIsometryEquiv.norm_map] using hu
  have hFa : AnalyticOnNhd ℂ F (ball (0 : Coeff 2) η) := fun u hu =>
    (hYa _ (hmem u hu)).comp (f := I.symm) (I.symm.toContinuousLinearEquiv.toContinuousLinearMap.analyticAt u)
  have hF0 : F 0=0 := by simp only [F,map_zero,hY0]
  have hFb (u : Coeff 2) (hu : u∈ball 0 η) : ‖F u‖≤C*(‖u‖+‖u‖^2) := by
    simpa only [F,LinearIsometryEquiv.norm_map] using hYb _ (hmem u hu)
  obtain ⟨hSa,hS0,hSb⟩ := signedHolomorphicCompletion_analytic_bound w F η C hFa hF0 hFb
  have hImem (q : WeightedCoeff v 2) (hq : q∈ball 0 η) : I q∈ball (0 : Coeff 2) η := by
    simpa only [mem_ball_zero_iff,LinearIsometryEquiv.norm_map] using hq
  refine ⟨?_,?_,?_⟩
  · intro q hq
    exact (hSa _ (hImem q hq)).comp (f := I) (I.toContinuousLinearEquiv.toContinuousLinearMap.analyticAt q)
  · simpa only [weightedSourceSignedCompletion,map_zero] using hS0
  · intro q hq
    simpa only [weightedSourceSignedCompletion,LinearIsometryEquiv.norm_map] using hSb _ (hImem q hq)

end NLS.WeightedCoeff
