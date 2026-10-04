import NLS.SequenceSpaces.HeadActionPath

/-! # Analyticity and initial values of the action-preserving paths -/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.Coeff
variable {q : ℝ≥0∞} [Fact (1 ≤ q)]

theorem analyticAt_headActionFree (S : Finset ℤ) (a w : TailSumSpace q S) (k : S) :
    AnalyticAt ℂ (fun w => headActionFree S a w k) w := by
  unfold headActionFree
  by_cases hx : a.1 k ≠ 0
  · simp only [if_pos hx]
    exact ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) q k.val).analyticAt w.2).comp analyticAt_snd
  · simp only [if_neg hx]
    exact ((ContinuousLinearMap.proj k : (S → ℂ) →L[ℂ] ℂ).analyticAt w.1).comp analyticAt_fst

theorem analyticAt_headActionSolved (S : Finset ℤ) (a w : TailSumSpace q S) (k : S) :
    AnalyticAt ℂ (fun w => headActionSolved S a w k) w := by
  unfold headActionSolved
  by_cases hx : a.1 k ≠ 0
  · simp only [if_pos hx]
    exact ((ContinuousLinearMap.proj k : (S → ℂ) →L[ℂ] ℂ).analyticAt w.1).comp analyticAt_fst
  · simp only [if_neg hx]
    exact ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) q k.val).analyticAt w.2).comp analyticAt_snd

theorem analyticAt_headActionFreeLine (S : Finset ℤ) (a : TailSumSpace q S) (k : S)
    (u : TailSumSpace q S × ℂ) : AnalyticAt ℂ (headActionFreeLine S a k) u := by
  have hf : AnalyticAt ℂ (fun u : TailSumSpace q S × ℂ => headActionFree S a u.1 k) u :=
    (analyticAt_headActionFree S a u.1 k).comp analyticAt_fst
  exact hf.add (analyticAt_snd.mul (analyticAt_const.sub hf))

theorem analyticAt_headActionPathRadicand (S : Finset ℤ) (a : TailSumSpace q S) (k : S)
    (u : TailSumSpace q S × ℂ) : AnalyticAt ℂ (headActionPathRadicand S a k) u := by
  have hx : AnalyticAt ℂ (fun u : TailSumSpace q S × ℂ => u.1.1 k) u :=
    (((ContinuousLinearMap.proj k : (S → ℂ) →L[ℂ] ℂ).analyticAt u.1.1).comp analyticAt_fst).comp analyticAt_fst
  have hy : AnalyticAt ℂ (fun u : TailSumSpace q S × ℂ => u.1.2 k.val) u :=
    (((lp.evalCLM ℂ (fun _ : ℤ => ℂ) q k.val).analyticAt u.1.2).comp analyticAt_snd).comp analyticAt_fst
  exact ((hx.pow 2).add (hy.pow 2)).sub ((analyticAt_headActionFreeLine S a k u).pow 2)

theorem analyticAt_headActionPathRoot_base (S : Finset ℤ) (a : TailSumSpace q S)
    (ha : HeadNonzero S a) (k : S) (t : ℂ) : AnalyticAt ℂ (headActionPathRoot S a k) (a,t) := by
  apply ComplexAnalysis.analyticOnNhd_prescribedSquareRoot _ _
    (fun u _ => analyticAt_headActionPathRadicand S a k u)
  exact ComplexAnalysis.mem_prescribedSquareRootDomain _ _ (headActionSolved_ne_zero S a ha k) _
    (headActionPathRadicand_base S a k t)

/-- The joint path is analytic near every point of the constant base path. -/
theorem analyticAt_headActionPath_base (S : Finset ℤ) (a : TailSumSpace q S)
    (ha : HeadNonzero S a) (t : ℂ) : AnalyticAt ℂ (headActionPath S a) (a,t) := by
  have hx : AnalyticAt ℂ (fun u : TailSumSpace q S × ℂ => fun k : S =>
      if a.1 k ≠ 0 then headActionPathRoot S a k u else headActionFreeLine S a k u) (a,t) := by
    apply AnalyticAt.pi
    intro k
    by_cases hk : a.1 k ≠ 0
    · simpa only [if_pos hk] using analyticAt_headActionPathRoot_base S a ha k t
    · simpa only [if_neg hk] using analyticAt_headActionFreeLine S a k (a,t)
  have hy : AnalyticAt ℂ (fun u : TailSumSpace q S × ℂ => fun k : S =>
      if a.1 k ≠ 0 then headActionFreeLine S a k u else headActionPathRoot S a k u) (a,t) := by
    apply AnalyticAt.pi
    intro k
    by_cases hk : a.1 k ≠ 0
    · simpa only [if_pos hk] using analyticAt_headActionFreeLine S a k (a,t)
    · simpa only [if_neg hk] using analyticAt_headActionPathRoot_base S a ha k t
  have ht : AnalyticAt ℂ (fun u : TailSumSpace q S × ℂ => u.1.2) (a,t) :=
    analyticAt_snd.comp analyticAt_fst
  exact hx.prod ((ht.sub (((truncateCLM (p := q) S).analyticAt _).comp ht)).add
    (((headInsertionCLM (q := q) S).analyticAt _).comp hy))

/-- Near the base the normalized initial roots agree with the original
coordinates, so the path starts at its prescribed initial point. -/
theorem eventually_headActionPath_zero (S : Finset ℤ) (a : TailSumSpace q S) (ha : HeadNonzero S a) :
    ∀ᶠ w in 𝓝 a, headActionPath S a (w,0) = w := by
  have hr (k : S) : (fun w => headActionPathRoot S a k (w,0)) =ᶠ[𝓝 a]
      (fun w => headActionSolved S a w k) := by
    have hp : ContinuousAt (fun w : TailSumSpace q S => (w,(0 : ℂ))) a :=
      continuousAt_id.prodMk continuousAt_const
    have hc := (analyticAt_headActionPathRoot_base S a ha k 0).continuousAt.comp (f := fun w : TailSumSpace q S => (w,(0 : ℂ))) hp
    apply ComplexAnalysis.eventuallyEq_of_sq_eq_of_continuousAt _ _ a hc
      (analyticAt_headActionSolved S a a k).continuousAt (headActionPathRoot_base S a ha k 0)
      (headActionSolved_ne_zero S a ha k)
    apply Eventually.of_forall
    intro w
    have he := ComplexAnalysis.prescribedSquareRoot_sq (headActionPathRadicand S a k) _
      (headActionSolved_ne_zero S a ha k) (w,0)
    change headActionPathRoot S a k (w,0)^2 = _ at he
    change headActionPathRoot S a k (w,0)^2 = headActionSolved S a w k^2
    rw [he]
    by_cases hx : a.1 k ≠ 0 <;>
      simp [headActionPathRadicand,headActionFreeLine,headActionFree,headActionSolved,hx]
  have hall : ∀ᶠ w in 𝓝 a, ∀ k : S, headActionPathRoot S a k (w,0) = headActionSolved S a w k :=
    Filter.eventually_all.mpr hr
  filter_upwards [hall] with w hw
  apply Prod.ext
  · funext k
    change (if a.1 k ≠ 0 then headActionPathRoot S a k (w,0) else headActionFreeLine S a k (w,0)) = w.1 k
    rw [hw k]
    by_cases hx : a.1 k ≠ 0 <;> simp [headActionFreeLine,headActionFree,headActionSolved,hx]
  · ext n
    rw [headActionPath_snd]
    by_cases hn : n ∈ S
    · rw [dif_pos hn,hw ⟨n,hn⟩]
      by_cases hx : a.1 ⟨n,hn⟩ ≠ 0 <;> simp [headActionFreeLine,headActionFree,headActionSolved,hx]
    · simp [hn]

end NLS.Coeff
