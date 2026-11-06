import NLS.SequenceSpaces.SignedCartesianActions
import NLS.SequenceSpaces.PhysicalRealMeanZeroWeighted
import NLS.SequenceSpaces.WeightedNonnegativeActions
import NLS.SequenceSpaces.NonnegativeActions

/-! # The original positive action sequence in its precise weighted l1 norm

The source uses the original raw h^t coefficients. Its action weight is
exactly the Sobolev weight of order 2*t. Positive signed products are
retained literally, with zero coefficients at all nonpositive indices.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal ComplexConjugate
namespace NLS

/-- Complete normalized actions with the original positive integer labels. -/
def normalizedSignedActionSequence (a : physicalRealDeletedSubmodule) : Coeff 1 :=
  quadraticActionsExponent (q := 1) (Coeff.signedToCartesian a.val)

theorem normalizedSignedActionSequence_apply (a : physicalRealDeletedSubmodule) (n : ℤ) :
    normalizedSignedActionSequence a n = if 0<n then a.val.val n*a.val.val (-n) else 0 :=
  Coeff.quadraticActions_signedToCartesian a.val n

theorem normalizedSignedActionSequence_nonnegative (a : physicalRealDeletedSubmodule) :
    normalizedSignedActionSequence a ∈ Coeff.nonnegativeLocus 1 :=
  Coeff.quadraticActions_mem_nonnegativeLocus _ (Coeff.signedToCartesian_real a)

/-- Doubling the Sobolev order gives exactly the product of the two target weights. -/
theorem sobolev_action_weight (t : ℝ) (n : ℤ) :
    Weight.sobolev (2*t) n = Weight.sobolev t n*Weight.sobolev t (-n) := by
  rw [Weight.sobolev_neg]
  simp only [Weight.sobolev_apply]
  rw [show 2*t=t+t by ring,Real.rpow_add (by positivity)]

/-- The ACTUAL raw positive action sequence in the ORIGINAL weighted l1 space.
The explicit order equation also permits the literal weights 3 and 5. -/
def sobolevSignedActionSequence (s t : ℝ) (_hst : s=2*t)
    (z : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev t)) :
    WeightedCoeff (Weight.sobolev s) 1 :=
  (WeightedCoeff.weightIsometry (Weight.sobolev s) 1).symm
    (normalizedSignedActionSequence
      ((physicalRealMeanZeroWeightedIsometry (Weight.sobolev t) (Weight.sobolev_neg t)).symm z))

/-- Exact weighting, including every central and nonpositive zero. -/
theorem sobolevSignedActionSequence_normalized (s t : ℝ) (hst : s=2*t)
    (z : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev t)) :
    WeightedCoeff.weightIsometry (Weight.sobolev s) 1 (sobolevSignedActionSequence s t hst z) =
      normalizedSignedActionSequence
        ((physicalRealMeanZeroWeightedIsometry (Weight.sobolev t) (Weight.sobolev_neg t)).symm z) :=
  LinearIsometryEquiv.apply_symm_apply _ _

/-- Every original positive action is literally z_n*z_(-n), without a scale
change. Membership has precisely weight (1+abs(n))^(2*t) and exponent one. -/
theorem sobolevSignedActionSequence_apply (s t : ℝ) (hst : s=2*t)
    (z : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev t)) (n : ℤ) :
    (sobolevSignedActionSequence s t hst z).val n =
      if 0<n then z.val.val n*z.val.val (-n) else 0 := by
  have he := congrArg (fun a : Coeff 1 => a n) (sobolevSignedActionSequence_normalized s t hst z)
  change (Weight.sobolev s n : ℂ)*(sobolevSignedActionSequence s t hst z).val n = _ at he
  rw [normalizedSignedActionSequence_apply] at he
  by_cases hn : 0<n
  · rw [if_pos hn] at he ⊢
    have hnp : n≠0 := by omega
    have hnm : -n≠0 := by omega
    simp only [physicalRealMeanZeroWeightedIsometry_symm_apply,
      WeightedCoeff.meanZeroWeightedProjection_apply_other _ _ _ hnp,
      WeightedCoeff.meanZeroWeightedProjection_apply_other _ _ _ hnm] at he
    have hw : (Weight.sobolev s n : ℂ) =
        (Weight.sobolev t n : ℂ)*(Weight.sobolev t (-n) : ℂ) := by
      rw [hst,sobolev_action_weight,ofReal_mul]
    apply mul_left_cancel₀ ((Weight.sobolev s).complex_ne_zero n)
    rw [he,hw]
    ring
  · rw [if_neg hn] at he ⊢
    exact (mul_eq_zero.mp he).resolve_left ((Weight.sobolev s).complex_ne_zero n)

/-- Positive weighting preserves the true nonnegative action cone. -/
theorem sobolevSignedActionSequence_nonnegative (s t : ℝ) (hst : s=2*t)
    (z : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev t)) :
    sobolevSignedActionSequence s t hst z ∈ WeightedCoeff.nonnegativeLocus (Weight.sobolev s) 1 := by
  apply (WeightedCoeff.mem_nonnegativeLocus_iff _ _ _).mpr
  change WeightedCoeff.weightIsometry (Weight.sobolev s) 1 (sobolevSignedActionSequence s t hst z) ∈ _
  rw [sobolevSignedActionSequence_normalized]
  exact normalizedSignedActionSequence_nonnegative _

/-- Every original nonnegative positive-index action sequence has an actual
physical real raw target in the exact corresponding h^t norm. -/
theorem exists_sobolevSignedActionSequence_preimage (s t : ℝ) (hst : s=2*t)
    (I : WeightedCoeff (Weight.sobolev s) 1)
    (hI : I ∈ WeightedCoeff.nonnegativeLocus (Weight.sobolev s) 1)
    (hzero : ∀ n : ℤ, n ≤ 0 → I.val n = 0) :
    ∃ z : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev t),
      sobolevSignedActionSequence s t hst z = I := by
  let L := WeightedCoeff.weightIsometry (Weight.sobolev s) 1
  have hJ : L I ∈ Coeff.nonnegativeLocus 1 := (WeightedCoeff.mem_nonnegativeLocus_iff _ _ I).mp hI
  obtain ⟨w,hw,he,_⟩ := Coeff.exists_real_quadraticActions_lift (p := 2) (by simp) (L I) hJ
  let a : physicalRealDeletedSubmodule := ⟨Coeff.cartesianToSigned w,Coeff.cartesianToSigned_real w hw⟩
  have ha : normalizedSignedActionSequence a = L I := by
    ext n
    rw [normalizedSignedActionSequence_apply]
    by_cases hn : 0<n
    · rw [if_pos hn]
      change (Coeff.cartesianToSigned w).val n*(Coeff.cartesianToSigned w).val (-n) = _
      rw [Coeff.cartesianToSigned_product w n hn,he]
    · rw [if_neg hn]
      change 0=(Weight.sobolev s n : ℂ)*I.val n
      rw [hzero n (by omega),mul_zero]
  refine ⟨physicalRealMeanZeroWeightedIsometry (Weight.sobolev t) (Weight.sobolev_neg t) a,?_⟩
  apply L.injective
  rw [sobolevSignedActionSequence_normalized,LinearIsometryEquiv.symm_apply_apply,ha]

namespace WeightedCoeff

private theorem exists_analytic_cone_factor_transport
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (L : E →L[ℂ] Coeff 1) (C : Set E)
    (hC : ∀ a ∈ C, L a ∈ Coeff.nonnegativeLocus 1)
    (U : Set (Coeff 1)) (f : Coeff 1 → ℂ)
    (hU : IsOpen U) (hpos : Coeff.nonnegativeLocus 1 ⊆ U)
    (hf : AnalyticOnNhd ℂ f U) :
    ∃ V : Set E, ∃ g : E → ℂ,
      IsOpen V ∧ C ⊆ V ∧ AnalyticOnNhd ℂ g V ∧ ∀ a, g a = f (L a) := by
  refine ⟨L ⁻¹' U,f ∘ L,hU.preimage L.continuous,?_,?_,fun _ => rfl⟩
  · intro a ha
    exact hpos (hC a ha)
  · intro a ha
    exact (hf _ ha).comp (f := L) (L.analyticAt a)

/-- Positive weighting transports an analytic factor and its whole cone
neighborhood into the original weighted action norm. -/
theorem exists_analytic_action_factor_transport (w : Weight) (U : Set (Coeff 1))
    (f : Coeff 1 → ℂ) (hU : IsOpen U) (hpos : Coeff.nonnegativeLocus 1 ⊆ U)
    (hf : AnalyticOnNhd ℂ f U) :
    ∃ V : Set (WeightedCoeff w 1), ∃ g : WeightedCoeff w 1 → ℂ,
      IsOpen V ∧ nonnegativeLocus w 1 ⊆ V ∧ AnalyticOnNhd ℂ g V ∧
      ∀ a : WeightedCoeff w 1, g a = f (weightIsometry w 1 a) := by
  exact exists_analytic_cone_factor_transport
    (weightIsometry w 1).toContinuousLinearEquiv.toContinuousLinearMap (nonnegativeLocus w 1)
    (fun a ha => (mem_nonnegativeLocus_iff w 1 a).mp ha) U f hU hpos hf

end WeightedCoeff

end NLS
