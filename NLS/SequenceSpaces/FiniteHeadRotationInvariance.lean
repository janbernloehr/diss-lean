import NLS.SequenceSpaces.TailRotationInvariance
import NLS.SequenceSpaces.FiniteCenterBall

/-! # Tail sign symmetry on balls centered at a finite head

Translation by a head-supported center leaves every tail rotation vector
unchanged. The checked zero-centered invariance theorem therefore applies
without translating the eventual quadratic quotient itself.
-/
noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

theorem actionRotationVectorCLM_head_eq_zero (S : Finset ℤ) (c : Coeff p × Coeff p)
    (hc : ∀ k ∉ S, c.1 k = 0 ∧ c.2 k = 0) (k : ℤ) (hk : k ∉ S) :
    actionRotationVectorCLM p k c = 0 := by
  rw [actionRotationVectorCLM_apply,(hc k hk).1,(hc k hk).2,lp.single_zero,neg_zero]
  rfl

theorem pairSignChange_head (S : Finset ℤ) (c : Coeff p × Coeff p)
    (hc : ∀ k ∉ S, c.1 k = 0 ∧ c.2 k = 0)
    (e d : ℤ → Bool) (he : ∀ k ∈ S, e k = false) (hd : ∀ k ∈ S, d k = false) :
    pairSignChange e d c = c := by
  apply Prod.ext <;> ext k
  · change signChange e c.1 k = c.1 k
    by_cases hk : k ∈ S
    · simp [signChange_apply,he k hk]
    · simp [signChange_apply,(hc k hk).1]
  · change signChange d c.2 k = c.2 k
    by_cases hk : k ∈ S
    · simp [signChange_apply,hd k hk]
    · simp [signChange_apply,(hc k hk).2]

/-- Tail stationarity gives arbitrary independent complex sign changes
on the smaller ball around a head-supported center. -/
theorem pairSignChange_invariant_of_tail_stationarity_at_head (hp : p ≠ ⊤)
    (S : Finset ℤ) (f : (Coeff p × Coeff p) → F) (c : Coeff p × Coeff p)
    (hc : ∀ k ∉ S, c.1 k = 0 ∧ c.2 k = 0) (R : ℝ) (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (ball c R))
    (hrot : ∀ z ∈ ball c R, ∀ k ∉ S,
      fderiv ℂ f z (actionRotationVectorCLM p k z) = 0)
    (e d : ℤ → Bool) (he : ∀ k ∈ S, e k = false) (hd : ∀ k ∈ S, d k = false)
    (z : Coeff p × Coeff p) (hz : z ∈ ball c (R/2)) :
    f (pairSignChange e d z) = f z := by
  let g : (Coeff p × Coeff p) → F := fun u => f (c+u)
  have hstay (u : Coeff p × Coeff p) (hu : u ∈ ball 0 R) : c+u ∈ ball c R := by
    simpa only [mem_ball,dist_eq_norm,add_sub_cancel_left,sub_zero] using hu
  have hg : AnalyticOnNhd ℂ g (ball 0 R) := by
    intro u hu
    exact (hf (c+u) (hstay u hu)).comp (analyticAt_const.add analyticAt_id)
  have hgrot (u : Coeff p × Coeff p) (hu : u ∈ ball 0 R) (k : ℤ) (hk : k ∉ S) :
      fderiv ℂ g u (actionRotationVectorCLM p k u) = 0 := by
    have hdg := (hf (c+u) (hstay u hu)).differentiableAt.hasFDerivAt.comp u
      ((hasFDerivAt_id u).const_add c)
    have hder : fderiv ℂ g u = fderiv ℂ f (c+u) := by
      change fderiv ℂ (f ∘ HAdd.hAdd c) u = _
      simpa only [ContinuousLinearMap.comp_id] using hdg.fderiv
    rw [hder]
    change fderiv ℂ f (c+u) (actionRotationVectorCLM p k u) = 0
    have hv : actionRotationVectorCLM p k (c+u) = actionRotationVectorCLM p k u := by
      rw [map_add,actionRotationVectorCLM_head_eq_zero S c hc k hk,zero_add]
    rw [← hv]
    exact hrot (c+u) (hstay u hu) k hk
  have hu : z-c ∈ ball (0 : Coeff p × Coeff p) (R/2) := by
    simpa only [mem_ball,dist_eq_norm,sub_zero] using hz
  have hs := pairSignChange_invariant_of_tail_rotation_stationary hp S g R hR hg hgrot e d he hd (z-c) hu
  have hfix := pairSignChange_head S c hc e d he hd
  have hleft : c+pairSignChange e d (z-c) = pairSignChange e d z := by
    rw [map_sub,hfix]
    abel
  have hright : c+(z-c) = z := by abel
  change f (c+pairSignChange e d (z-c)) = f (c+(z-c)) at hs
  simpa only [hleft,hright] using hs

end NLS.Coeff
