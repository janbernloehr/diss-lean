import NLS.ComplexAnalysis.CircleHoleRemoval

/-!
# Finite-hole contour decomposition

For a function analytic on a closed outer disc with finitely many open
circular holes, the counterclockwise outer integral is the sum of the
counterclockwise inner integrals. Disjoint larger isolating discs allow
each hole to be filled in turn. Cauchy-transform period identities keep
the other hole integrals unchanged at every step.
-/

noncomputable section
open Set Complex Metric
open scoped Classical
namespace NLS.ComplexAnalysis

/-- A closed outer disc with a finite family of open holes removed. -/
def circleHoleDomain {ι : Type*} (d : ℂ) (S : ℝ) (s : Finset ι)
    (c : ι → ℂ) (r : ι → ℝ) : Set ℂ :=
  {z | z ∈ closedBall d S ∧ ∀ i ∈ s, z ∉ ball (c i) (r i)}

/-- Cauchy's theorem with finitely many holes. The function is analytic
near the closed perforated disc; no behavior inside the holes is assumed. -/
theorem circleIntegral_eq_sum_of_finite_holes {ι : Type*}
    (d : ℂ) (S : ℝ) (hS : 0 ≤ S) (s : Finset ι)
    (c : ι → ℂ) (r R : ι → ℝ) (f : ℂ → ℂ)
    (hr : ∀ i ∈ s, 0 < r i) (hrR : ∀ i ∈ s, r i < R i)
    (henclosed : ∀ i ∈ s, closedBall (c i) (R i) ⊆ ball d S)
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Disjoint (closedBall (c i) (R i)) (closedBall (c j) (R j)))
    (hf : AnalyticOnNhd ℂ f (circleHoleDomain d S s c r)) :
    (∮ z in C(d,S), f z) = ∑ i ∈ s, ∮ z in C(c i,r i), f z := by
  classical
  induction s using Finset.induction_on generalizing f with
  | empty =>
      have ha : AnalyticOnNhd ℂ f (closedBall d S) := by
        intro z hz
        exact hf z ⟨hz, by simp⟩
      have hd := ha.differentiableOn
      simpa only [Finset.sum_empty] using
        (DiffContOnCl.mk_ball (hd.mono ball_subset_closedBall) hd.continuousOn).circleIntegral_eq_zero hS
  | @insert i s hi ih =>
      have hi' : i ∈ insert i s := Finset.mem_insert_self i s
      have hmem (j : ι) (hj : j ∈ s) : j ∈ insert i s := Finset.mem_insert_of_mem hj
      let U := circleHoleDomain d S s c r
      have hcover : closedBall (c i) (R i) ⊆ U := by
        intro z hz
        refine ⟨ball_subset_closedBall (henclosed i hi' hz), ?_⟩
        intro j hj hzj
        have hij : i ≠ j := fun he => hi (he ▸ hj)
        exact (hdisj i hi' j (hmem j hj) hij).le_bot
          ⟨hz, (closedBall_subset_closedBall (hrR j (hmem j hj)).le) (ball_subset_closedBall hzj)⟩
      have hfu : AnalyticOnNhd ℂ f (U \ ball (c i) (r i)) := by
        intro z hz
        apply hf z
        refine ⟨hz.1.1, ?_⟩
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hjs
        · exact hz.2
        · exact hz.1.2 j hjs
      have hAnn : AnalyticOnNhd ℂ f (closedBall (c i) (R i) \ ball (c i) (r i)) :=
        hfu.mono (fun _ h => ⟨hcover h.1,h.2⟩)
      let g := circleHoleRemoval f (c i) (r i) (R i)
      have hg : AnalyticOnNhd ℂ g U := analyticOnNhd_circleHoleRemoval
        f (c i) (r i) (R i) (hr i hi') (hrR i hi') U hfu hcover
      have houter : sphere d S ⊆ circleHoleDomain d S (insert i s) c r := by
        intro z hz
        refine ⟨sphere_subset_closedBall hz, ?_⟩
        intro j hj hzj
        have houter := henclosed j hj
          ((closedBall_subset_closedBall (hrR j hj).le) (ball_subset_closedBall hzj))
        exact sphere_disjoint_ball.le_bot ⟨hz,houter⟩
      have hinner : ∀ j ∈ insert i s,
          sphere (c j) (r j) ⊆ circleHoleDomain d S (insert i s) c r := by
        intro j hj z hz
        have hzj : z ∈ closedBall (c j) (R j) :=
          (closedBall_subset_closedBall (hrR j hj).le) (sphere_subset_closedBall hz)
        refine ⟨ball_subset_closedBall (henclosed j hj hzj), ?_⟩
        intro k hk hzk
        by_cases hjk : j = k
        · subst k
          exact sphere_disjoint_ball.le_bot ⟨hz,hzk⟩
        · exact (hdisj j hj k hk hjk).le_bot
            ⟨hzj, (closedBall_subset_closedBall (hrR k hk).le) (ball_subset_closedBall hzk)⟩
      have hperiod : (∮ z in C(d,S), g z) =
          (∮ z in C(d,S), f z)-(∮ z in C(c i,r i), f z) :=
        circleIntegral_circleHoleRemoval_of_enclosed f (c i) d (r i) (R i) S
          (hr i hi') (hrR i hi') hS hAnn (hf.continuousOn.mono houter) (henclosed i hi')
      have hpreserve (j : ι) (hj : j ∈ s) :
          (∮ z in C(c j,r j), g z) = ∮ z in C(c j,r j), f z := by
        have hij : i ≠ j := fun he => hi (he ▸ hj)
        have hsmall : Disjoint (closedBall (c i) (r i)) (closedBall (c j) (r j)) :=
          (hdisj i hi' j (hmem j hj) hij).mono
            (closedBall_subset_closedBall (hrR i hi').le)
            (closedBall_subset_closedBall (hrR j (hmem j hj)).le)
        exact circleIntegral_circleHoleRemoval_of_disjoint f (c i) (c j) (r i) (R i) (r j)
          (hr i hi') (hrR i hi') (hr j (hmem j hj)).le hAnn
          (hf.continuousOn.mono (hinner j (hmem j hj))) hsmall
      have hremaining := ih g (fun j hj => hr j (hmem j hj))
        (fun j hj => hrR j (hmem j hj)) (fun j hj => henclosed j (hmem j hj))
        (fun j hj k hk hne => hdisj j (hmem j hj) k (hmem k hk) hne) hg
      have hsum : (∑ j ∈ s, ∮ z in C(c j,r j), g z) = ∑ j ∈ s, ∮ z in C(c j,r j), f z :=
        Finset.sum_congr rfl (fun j hj => hpreserve j hj)
      rw [hsum] at hremaining
      rw [Finset.sum_insert hi]
      linear_combination -hperiod + hremaining

end NLS.ComplexAnalysis
