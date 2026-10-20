import NLS.ZakharovShabat.SobolevHamiltonianNextPhaseDerivative
import Mathlib.Analysis.Calculus.MeanValue

/-! # Comparing the next phase at nearby spectral points

The nonlinear phase difference has an inverse-index Lipschitz bound on distant unit discs, uniformly on original Sobolev balls.
-/

noncomputable section
open Set Complex Metric NLS.Fourier
open scoped ContDiff ENNReal
namespace NLS.ZakharovShabat

/-- On each distant unit disc, the nonlinear part of the next phase
has an inverse-index Lipschitz constant, uniformly on original Hs balls.
This compares a boundary root and a critical point without losing a
derivative from their difference. -/
theorem exists_uniform_nlsHamiltonian_next_phase_difference_bound
    (s N : ℕ) (hs : 1 ≤ s) (hNs : N ≤ s+1) (R : ℝ) (hR : 0 ≤ R) :
    ∃ K : ℕ, 0 < K ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ ab : SobolevSource s, ‖ab‖ ≤ R → ∀ a b : ℝ → ℂ,
      ContDiff ℝ ∞ a → ContDiff ℝ ∞ b →
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.2.val j = periodOneCoefficient b j) →
      ∀ n : ℤ, K ≤ n.natAbs → ∀ z w : ℂ,
      ‖z-(Real.pi:ℂ)*n‖ ≤ 1 → ‖w-(Real.pi:ℂ)*n‖ ≤ 1 →
      ‖nlsHamiltonianPhase a b N z-nlsHamiltonianPhase a b N w+I*(z-w)‖ ≤
        C/(1+|(n:ℝ)|)*‖z-w‖ := by
  obtain ⟨K,hK,hfreq⟩ := exists_wkb_bounded_frequency_cutoff 2 (by norm_num)
  obtain ⟨A,hA,hfree⟩ := exists_uniform_nlsHamiltonian_next_phase_free_bound s N hs hNs R hR
  refine ⟨K,hK,A,hA,?_⟩
  intro ab hab a b ha hb hpa hpb hca hcb n hn z w hz hw
  let c : ℂ := (Real.pi:ℂ)*n
  let q : ℝ := 1+|(n:ℝ)|
  have hq : 0 < q := by dsimp [q]; positivity
  let f (v : ℂ) := nlsHamiltonianPhase a b N v+I*v
  have hgeom (v : ℂ) (hv : ‖v-c‖ ≤ 2) : 1 ≤ ‖v‖ ∧ q ≤ ‖v‖ := by
    have h := hfreq (fun _ => v-c) (fun _ => hv) n hn
    simpa only [c,add_sub_cancel] using h
  have hdiff (v : ℂ) (hv : ‖v-c‖ ≤ 2) : DifferentiableAt ℂ f v :=
    ((analyticAt_nlsHamiltonianPhase_spectral a b N v
      (norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one (hgeom v hv).1))).add
      (analyticAt_const.mul analyticAt_id)).differentiableAt
  have hbound (v : ℂ) (hv : ‖v-c‖ ≤ 2) : ‖f v‖ ≤ A/(2*q) := by
    apply (hfree ab hab a b ha hb hpa hpb hca hcb v (hgeom v hv).1).trans
    simp only [norm_inv,norm_mul,norm_ofNat,norm_I,mul_one,← div_eq_mul_inv]
    exact div_le_div_of_nonneg_left hA (by positivity) (by linarith [(hgeom v hv).2])
  have hder (v : ℂ) (hv : v ∈ closedBall c 1) : ‖fderiv ℂ f v‖ ≤ A/q := by
    have hv1 : ‖v-c‖ ≤ 1 := by simpa only [mem_closedBall,dist_eq_norm] using hv
    have hnear (x : ℂ) (hx : x ∈ ball v 1) : ‖x-c‖ ≤ 2 := by
      have hx1 : ‖x-v‖ < 1 := by simpa only [mem_ball,dist_eq_norm] using hx
      have ht := norm_sub_le_norm_sub_add_norm_sub x v c
      linarith
    have hd : DifferentiableOn ℂ f (ball v 1) :=
      fun x hx => (hdiff x (hnear x hx)).differentiableWithinAt
    have hm : MapsTo f (ball v 1) (closedBall (f v) (2*(A/(2*q)))) := by
      intro x hx
      rw [mem_closedBall,dist_eq_norm]
      exact (norm_sub_le _ _).trans (by
        linarith [hbound x (hnear x hx),hbound v (by linarith)])
    have h := Complex.norm_fderiv_le_div_of_mapsTo_ball hd hm (by norm_num : (0:ℝ) < 1)
    exact h.trans_eq (by ring)
  have h := (convex_closedBall c 1).norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℂ)
    (f := f) (fun v hv => hdiff v (by
      have hv1 : ‖v-c‖ ≤ 1 := by simpa only [mem_closedBall,dist_eq_norm] using hv
      linarith)) hder
    (by simpa only [mem_closedBall,dist_eq_norm] using hw)
    (by simpa only [mem_closedBall,dist_eq_norm] using hz)
  have he : nlsHamiltonianPhase a b N z-nlsHamiltonianPhase a b N w+I*(z-w) =
      f z-f w := by dsimp only [f]; ring
  rw [he]
  exact h

end NLS.ZakharovShabat
