import NLS.Articles.KdVPseudomeasures.OriginalHillL2OneSmoothing

/-! # Actual canonical equivalences at every nonnegative real Sobolev order

The one-smoothing remainder at the lower integer order constructs both
maps on every intermediate Hilbert scale. No fractional inverse regularity
or interpolation premise is assumed.
-/
noncomputable section
open NLS.KdV NLS.WeightedCoeff NLS.FunctionalAnalysis
namespace NLS.Articles.KdVPseudomeasures

theorem exists_hillSobolev_equiv_between_integer_orders
    (N : ℕ) (s : ℝ) (hlo : (N:ℝ) ≤ s) (hhi : s ≤ (N:ℝ)+1) :
    ∃ e : RealSignedHilbert s ≃ RealSignedHilbert (s+1/2),
      (∀ q k, (e q).val.val.val k =
        (hillRealSignedMap (hillIntegerSourceInclusion N
          (signedRealOrderInclusion (signedStepOrder 0 N) s
            (by rw [hillIntegerSobolev_source_order]; exact hlo) q))).val.val.val k) ∧
      (∀ q, AnalyticAt ℝ e q) ∧ (∀ z, AnalyticAt ℝ e.symm z) := by
  obtain ⟨R,hRa,hRc⟩ := hillIntegerNativeOneSmoothing_all N
  have hsource : signedStepOrder 0 N ≤ s := by rw [hillIntegerSobolev_source_order]; exact hlo
  have htarget : signedStepOrder (1/2) N ≤ s+1/2 := by rw [hillIntegerSobolev_target_order]; linarith
  have hsmooth : s+1/2 ≤ signedStepOrder (1/2) N+1 := by rw [hillIntegerSobolev_target_order]; linarith
  let iE := signedRealOrderInclusion (p := 2) (signedStepOrder 0 N) s hsource
  let iF := signedRealOrderInclusion (p := 2) (signedStepOrder (1/2) N) (s+1/2) htarget
  let S := signedRealOrderInclusion (p := 2) (s+1/2) (signedStepOrder (1/2) N+1) hsmooth
  let A := signedRealOrderHalfFourierEquivOfEq s (s+1/2) rfl 2
  let A₀ := hillIntegerFreeFourierEquiv N 2
  let e₀ := (hillIntegerSobolevEquiv N).equiv
  have hA (q : RealSignedHilbert s) : iF (A q) = A₀ (iE q) := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    funext k
    rw [signedRealOrderInclusion_apply,hillIntegerFreeFourierEquiv_apply,
      signedRealOrderInclusion_apply,signedRealOrderHalfFourierEquivOfEq_apply]
  have hdef (q : RealSignedHilbert (signedStepOrder 0 N)) :
      e₀ q = A₀ q+iF (S (R q)) := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    funext k
    change (e₀ q).val.val.val k = (A₀ q).val.val.val k+(iF (S (R q))).val.val.val k
    rw [hillIntegerFreeFourierEquiv_apply,signedRealOrderInclusion_apply,
      signedRealOrderInclusion_apply,hRc]
    ring
  obtain ⟨e,hinc,ha,hi⟩ := @exists_analytic_smoothingRestrictionEquiv ℝ
    (RealSignedHilbert s) (RealSignedHilbert (s+1/2))
    (RealSignedHilbert (signedStepOrder 0 N)) (RealSignedHilbert (signedStepOrder (1/2) N))
    (RealSignedHilbert (signedStepOrder (1/2) N+1))
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance inferInstance iE iF
    (signedRealOrderInclusion_injective _ _ _) (signedRealOrderInclusion_injective _ _ _)
    A A₀ S R e₀ hA hdef hRa (hillIntegerSobolevEquiv N).analytic_symm
  refine ⟨e,?_,ha,hi⟩
  intro q k
  have he := congrArg (fun z : RealSignedHilbert (signedStepOrder (1/2) N) => z.val.val.val k) (hinc q)
  rw [signedRealOrderInclusion_apply] at he
  exact he.trans (hillIntegerSobolevEquiv_apply N (iE q) k)

def hillNonnegativeSobolevSourceInclusion (s : ℝ) (hs : 0 ≤ s) :
    RealSignedHilbert s →L[ℝ] HillRealMeanZeroSource :=
  (hillIntegerSourceInclusion ⌊s⌋₊).comp
    (signedRealOrderInclusion (signedStepOrder 0 ⌊s⌋₊) s
      (by rw [hillIntegerSobolev_source_order]; exact Nat.floor_le hs))

theorem hillNonnegativeSobolevSourceInclusion_apply (s : ℝ) (hs : 0 ≤ s)
    (q : RealSignedHilbert s) (k : ℤ) :
    (hillNonnegativeSobolevSourceInclusion s hs q).val.val.val k = q.val.val.val k := by
  rw [hillNonnegativeSobolevSourceInclusion,ContinuousLinearMap.comp_apply,
    hillIntegerSourceInclusion_apply,signedRealOrderInclusion_apply]

/-- Every nonnegative real order, including every noninteger one, has the
actual canonical analytic equivalence and its actual analytic inverse. -/
theorem exists_hillNonnegativeSobolevEquiv (s : ℝ) (hs : 0 ≤ s) :
    ∃ e : RealSignedHilbert s ≃ RealSignedHilbert (s+1/2),
      (∀ q k, (e q).val.val.val k =
        (hillRealSignedMap (hillNonnegativeSobolevSourceInclusion s hs q)).val.val.val k) ∧
      (∀ q, AnalyticAt ℝ e q) ∧ (∀ z, AnalyticAt ℝ e.symm z) :=
  exists_hillSobolev_equiv_between_integer_orders ⌊s⌋₊ s (Nat.floor_le hs)
    (Nat.lt_floor_add_one s).le

end NLS.Articles.KdVPseudomeasures
