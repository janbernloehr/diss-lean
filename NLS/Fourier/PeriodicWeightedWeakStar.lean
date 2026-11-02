import NLS.Fourier.PeriodicSobolevDuality
import NLS.SequenceSpaces.WeightedWeakStarLowerTopology

/-! # Weighted weak-star topology on original periodic distributions

The Fourier coefficient equivalence of the Wiener predual induces a genuine
homeomorphism between its two weak duals. This identifies the original
normalized distributional weak-star topology with the coefficient weak-star
topology used by the endpoint compactness and dynamics proofs.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.Fourier.PeriodicFourierLebesgue
open SmoothPeriodicTest
variable {L : ℝ} [Fact (0 < L)]

/-- The actual Wiener predual coefficient equivalence transports weak duals
homeomorphically, not merely by a norm-continuous inclusion. -/
def coefficientWeakDualHomeomorph (r : ℝ) :
    WeakDual ℂ (WeightedCoeff (Weight.sobolev r) 1) ≃ₜ
      WeakDual ℂ (FourierLebesgueSpace L r 1) where
  toFun f := StrongDual.toWeakDual
    (f.toStrongDual.comp (sobolevCoefficients r 1).toContinuousLinearEquiv.toContinuousLinearMap)
  invFun f := StrongDual.toWeakDual
    (f.toStrongDual.comp (sobolevCoefficients r 1).symm.toContinuousLinearEquiv.toContinuousLinearMap)
  left_inv f := by
    apply DFunLike.ext
    intro a
    change f (sobolevCoefficients r 1 ((sobolevCoefficients r 1).symm a)) = f a
    rw [LinearIsometryEquiv.apply_symm_apply]
  right_inv f := by
    apply DFunLike.ext
    intro u
    change f ((sobolevCoefficients r 1).symm (sobolevCoefficients r 1 u)) = f u
    rw [LinearIsometryEquiv.symm_apply_apply]
  continuous_toFun := by
    apply WeakDual.continuous_of_continuous_eval
    intro u
    exact WeakDual.eval_continuous (sobolevCoefficients r 1 u)
  continuous_invFun := by
    apply WeakDual.continuous_of_continuous_eval
    intro a
    exact WeakDual.eval_continuous ((sobolevCoefficients r 1).symm a)

/-- The weighted pseudomeasure as a functional on the original weighted
Wiener distribution space. The argument r is the predual order. -/
def sobolevPseudomeasureWeakStar (r : ℝ) (u : FourierLebesgueSpace L (-r) ⊤) :
    WeakDual ℂ (FourierLebesgueSpace L r 1) :=
  StrongDual.toWeakDual (sobolevDualIsometry r (by simp) u)

/-- Exact topological compatibility, including the physical Fourier reversal. -/
theorem sobolevPseudomeasureWeakStar_eq (r : ℝ) (u : FourierLebesgueSpace L (-r) ⊤) :
    sobolevPseudomeasureWeakStar r u = coefficientWeakDualHomeomorph r
      (WeightedCoeff.wienerDualRealization r (sobolevCoefficients (-r) ⊤ u)) := by
  apply DFunLike.ext
  intro v
  rfl

/-- On smooth tests the weak-star functional is exactly the original
smooth-test action, with the source period normalization retained. -/
theorem sobolevPseudomeasureWeakStar_ofSmooth (r : ℝ)
    (u : FourierLebesgueSpace L (-r) ⊤) (f : SmoothPeriodicTest L) :
    sobolevPseudomeasureWeakStar r u (ofSmooth r 1 f) = u.val f :=
  sobolevDualIsometry_ofSmooth r (by simp) u f

/-- Actual weighted coefficient norm balls are weak-star compact in the
original-distribution predual, for every positive period and real order. -/
theorem isCompact_sobolevPseudomeasureWeakStar_closedBall (r R : ℝ) :
    IsCompact (sobolevPseudomeasureWeakStar (L := L) r '' Metric.closedBall 0 R) := by
  let e := sobolevCoefficients (L := L) (-r) ⊤
  have he : e '' Metric.closedBall 0 R = Metric.closedBall 0 R := by
    ext a
    constructor
    · rintro ⟨u, hu, rfl⟩
      simpa only [Metric.mem_closedBall, dist_zero_right, LinearIsometryEquiv.norm_map] using hu
    · intro ha
      refine ⟨e.symm a, ?_, e.apply_symm_apply a⟩
      simpa only [Metric.mem_closedBall, dist_zero_right, LinearIsometryEquiv.norm_map] using ha
  have hf : sobolevPseudomeasureWeakStar (L := L) r =
      coefficientWeakDualHomeomorph r ∘ WeightedCoeff.wienerDualRealization r ∘ e :=
    funext (sobolevPseudomeasureWeakStar_eq r)
  rw [hf, Set.image_comp, Set.image_comp, he,
    WeightedCoeff.image_wienerDualRealization_closedBall]
  exact (WeightedCoeff.isCompact_weakStarBall r R).image
    (coefficientWeakDualHomeomorph (L := L) r).continuous

/-- Bounded original distributions with continuous Fourier coefficients form
a continuous map for the actual weighted Wiener weak-star topology. -/
theorem continuous_sobolevPseudomeasureWeakStar_of_bounded_coefficients (r : ℝ)
    {X : Type*} [TopologicalSpace X]
    (u : X → FourierLebesgueSpace L (-r) ⊤)
    (hb : Bornology.IsBounded (range u))
    (hc : ∀ n : ℤ, Continuous (fun x => (u x).val (mode (-n)))) :
    Continuous (fun x => sobolevPseudomeasureWeakStar r (u x)) := by
  let e := sobolevCoefficients (L := L) (-r) ⊤
  have he : Bornology.IsBounded (range (fun x => e (u x))) := by
    obtain ⟨M,hM⟩ := hb.exists_norm_le
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨M, ?_⟩
    rintro _ ⟨x,rfl⟩
    simpa only [LinearIsometryEquiv.norm_map] using hM _ ⟨x,rfl⟩
  have hb' : Bornology.IsBounded (range (fun y => WeightedCoeff.wienerDualRealization r (e (u y)))) := by
    rw [← WeakDual.isBounded_toWeakDual_preimage_iff_isBounded]
    obtain ⟨M,hM⟩ := he.exists_norm_le
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨M, ?_⟩
    intro f hf
    obtain ⟨y,hy⟩ := hf
    have hy' : f = WeightedCoeff.sobolevDualityIsometry r (by simp) (e (u y)) := by
      simpa only [StrongDual.toStrongDual_toWeakDual, WeightedCoeff.wienerDualRealization] using
        congrArg (WeakDual.toStrongDual (𝕜 := ℂ)) hy.symm
    rw [hy', LinearIsometryEquiv.norm_map]
    exact hM _ ⟨y,rfl⟩
  have hd : Continuous (fun x => WeightedCoeff.wienerDualRealization r (e (u x))) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    apply (WeightedCoeff.tendsto_weakStar_iff_coordinates_of_bounded r
      (fun y => WeightedCoeff.wienerDualRealization r (e (u y)))
      (WeightedCoeff.wienerDualRealization r (e (u x))) hb').mpr
    intro n
    simp only [e, WeightedCoeff.weakStarCoordinates_wienerDualRealization,
      sobolevCoefficients_apply]
    exact (hc n).tendsto x
  have hs := (coefficientWeakDualHomeomorph (L := L) r).continuous.comp hd
  simpa only [Function.comp_def, e, ← sobolevPseudomeasureWeakStar_eq] using hs

end NLS.Fourier.PeriodicFourierLebesgue
