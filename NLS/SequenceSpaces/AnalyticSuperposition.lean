import NLS.SequenceSpaces.LocallyUniformCoordinates
import NLS.SequenceSpaces.FourierTail
import NLS.SequenceSpaces.FiniteHeadTailBound
import NLS.SequenceSpaces.LocallyBoundedRealization

/-! # Analytic superposition on finite-exponent sequence spaces

A scalar analytic function with a linear bound near zero acts analytically
on lp near every sequence whose coordinates lie in its analytic locus.
The finite head is retained exactly; one common neighborhood controls the tail.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem exists_local_analytic_superposition (hp : p ≠ ⊤)
    (f : ℂ → ℂ) (L r : ℝ) (hL : 0 ≤ L) (hr : 0 < r)
    (hf : AnalyticOnNhd ℂ f (ball 0 r))
    (hbound : ∀ z ∈ ball 0 r, ‖f z‖ ≤ L*‖z‖)
    (a : Coeff p) (ha : ∀ n : ℤ, AnalyticAt ℂ f (a n)) :
    ∃ V : Set (Coeff p), IsOpen V ∧ a ∈ V ∧
      AnalyticOnNhd ℂ (fun b : Coeff p => ofFunctionOrZero p (fun n => f (b n))) V ∧
      ∀ b ∈ V, ∀ n, ofFunctionOrZero p (fun j => f (b j)) n = f (b n) := by
  classical
  obtain ⟨K,T,hT,haT,hsmall⟩ := exists_local_uniform_small_coordinates hp
    (fun b : Coeff p => b) a continuousAt_id r hr
  let S := lowFrequencies (K+1)
  have hhead : ∀ᶠ b : Coeff p in 𝓝 a, ∀ n ∈ S, AnalyticAt ℂ f (b n) := by
    rw [Finset.eventually_all]
    intro n _
    exact (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).continuous.continuousAt.preimage_mem_nhds
      (ha n).eventually_analyticAt
  obtain ⟨H,hHsub,hH,haH⟩ := _root_.mem_nhds_iff.mp hhead
  let V := T ∩ H
  have hV : IsOpen V := hT.inter hH
  have hcoord (n : ℤ) : AnalyticOnNhd ℂ (fun b : Coeff p => f (b n)) V := by
    intro b hb
    have hscalar : AnalyticAt ℂ f (b n) := by
      by_cases hn : n ∈ S
      · exact hHsub hb.2 n hn
      · apply hf _
        simp only [mem_ball,dist_zero_right]
        apply hsmall b hb.1 n
        simp only [S,mem_lowFrequencies,not_lt] at hn
        omega
    exact hscalar.comp (f := fun b : Coeff p => b n)
      ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).analyticAt b)
  obtain ⟨he,hg⟩ := analytic_realization_of_local_bounds (r := p)
    (fun b : Coeff p => fun n => f (b n)) hV hcoord (by
      intro b hb
      let head : Coeff p → Coeff p := fun c => finiteHead S (fun n => f (c n))
      have hh : ContinuousAt head b := by
        unfold head finiteHead
        apply tendsto_finsetSum S
        intro n _
        exact (lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) p n).continuous.continuousAt.comp
          (hcoord n b hb).continuousAt
      have hhb : ∀ᶠ c in 𝓝 b, ‖head c‖ < ‖head b‖+1 :=
        hh.norm.eventually (gt_mem_nhds (by linarith))
      have hcb : ∀ᶠ c : Coeff p in 𝓝 b, ‖c‖ < ‖b‖+1 :=
        continuousAt_id.norm.eventually (gt_mem_nhds (by dsimp; linarith))
      obtain ⟨W,hWsub,hW,hbW⟩ := _root_.mem_nhds_iff.mp
        (inter_mem (hV.mem_nhds hb) (inter_mem hhb hcb))
      refine ⟨W,hW,hbW,fun c hc => (hWsub hc).1,(‖head b‖+1)+L*(‖b‖+1),?_⟩
      intro c hc
      obtain ⟨hm,hn⟩ := memℓp_and_norm_ofFunctionOrZero_le_of_head_tail_bound
        (fun n => f (c n)) (fun n => f (c n)) S c 0 L hL (fun _ _ => le_rfl) (by
          intro n hn
          have hnK : K < n.natAbs := by
            simp only [S,mem_lowFrequencies,not_lt] at hn
            omega
          have hs : c n ∈ ball 0 r := by
            simpa only [mem_ball,dist_zero_right] using hsmall c (hWsub hc).1.1 n hnK
          simpa only [lp.coeFn_zero,Pi.zero_apply,norm_zero,add_zero] using hbound (c n) hs)
      refine ⟨ofFunctionOrZero p (fun n => f (c n)),
        ofFunctionOrZero_apply_of_mem p _ hm,hn.trans ?_⟩
      change ‖head c‖+L*(‖c‖+‖(0 : Coeff p)‖) ≤ _
      simp only [norm_zero,add_zero]
      exact add_le_add (hWsub hc).2.1.le (mul_le_mul_of_nonneg_left (hWsub hc).2.2.le hL))
  exact ⟨V,hV,⟨haT,haH⟩,hg,he⟩

end NLS.Coeff
