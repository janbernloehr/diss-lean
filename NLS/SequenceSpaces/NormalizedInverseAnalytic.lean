import NLS.SequenceSpaces.LocallyUniformCoordinates
import NLS.SequenceSpaces.FourierTail
import NLS.SequenceSpaces.FiniteHeadTailBound
import NLS.SequenceSpaces.LocallyBoundedRealization

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.Coeff

private theorem norm_inv_sub_one_le (z : ℂ) (hz : ‖z-1‖ < (1:ℝ)/2) :
    ‖z⁻¹-1‖ ≤ 2*‖z-1‖ := by
  have htri : 1 ≤ ‖z-1‖+‖z‖ := by
    simpa only [sub_sub_cancel,norm_one,add_comm] using norm_sub_le z (z-1)
  have hnorm : (1:ℝ)/2 < ‖z‖ := by linarith
  have hne : z ≠ 0 := norm_pos_iff.mp (by linarith)
  have he : z⁻¹-1 = -(z-1)/z := by field_simp; ring
  rw [he,norm_div,norm_neg]
  apply (div_le_iff₀ (by linarith : 0 < ‖z‖)).mpr
  nlinarith [norm_nonneg (z-1)]

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- Coordinatewise inversion preserves analytic lp normalization whenever no
coordinate vanishes. The domain is unchanged and all finite coordinates are retained. -/
theorem analytic_normalized_inverse_error (hp : p ≠ ⊤)
    {W : Set X} (hW : IsOpen W)
    (f : X → ℤ → ℂ) (hf : ∀ n, AnalyticOnNhd ℂ (fun x => f x n) W)
    (hne : ∀ x ∈ W, ∀ n, f x n ≠ 0)
    (e : X → Coeff p) (hec : ContinuousOn e W)
    (he : ∀ x ∈ W, ∀ n, e x n = f x n-1) :
    AnalyticOnNhd ℂ (fun x => ofFunctionOrZero p (fun n => (f x n)⁻¹-1)) W ∧
      ∀ x ∈ W, ∀ n, ofFunctionOrZero p (fun n => (f x n)⁻¹-1) n = (f x n)⁻¹-1 := by
  classical
  have ha (n : ℤ) : AnalyticOnNhd ℂ (fun x => (f x n)⁻¹-1) W :=
    fun x hx => ((hf n x hx).inv (hne x hx n)).sub analyticAt_const
  obtain ⟨hv,hg⟩ := analytic_realization_of_local_bounds (fun x n => (f x n)⁻¹-1) hW ha (by
    intro a haW
    have hecont := (hec a haW).continuousAt (hW.mem_nhds haW)
    obtain ⟨K,T,hT,haT,hsmall⟩ := exists_local_uniform_small_coordinates hp e a hecont
      ((1:ℝ)/2) (by norm_num)
    let S := lowFrequencies (K+1)
    let head : X → Coeff p := fun x => finiteHead S (fun n => (f x n)⁻¹-1)
    have hh : ContinuousAt head a := by
      unfold head finiteHead
      apply tendsto_finsetSum S
      intro n _
      exact (lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) p n).continuous.continuousAt.comp
        (ha n a haW).continuousAt
    have hhb : ∀ᶠ x in 𝓝 a, ‖head x‖ < ‖head a‖+1 :=
      hh.norm.eventually (gt_mem_nhds (by linarith))
    have heb : ∀ᶠ x in 𝓝 a, ‖e x‖ < ‖e a‖+1 :=
      hecont.norm.eventually (gt_mem_nhds (by linarith))
    obtain ⟨V,hVsub,hV,haV⟩ := _root_.mem_nhds_iff.mp
      (inter_mem ((hW.inter hT).mem_nhds ⟨haW,haT⟩) (inter_mem hhb heb))
    refine ⟨V,hV,haV,fun x hx => (hVsub hx).1.1,(‖head a‖+1)+2*(‖e a‖+1),?_⟩
    intro x hx
    obtain ⟨hm,hb⟩ := memℓp_and_norm_ofFunctionOrZero_le_of_head_tail_bound
      (fun n => (f x n)⁻¹-1) (fun n => (f x n)⁻¹-1) S (e x) 0 2 (by norm_num)
      (fun _ _ => le_rfl) (by
        intro n hn
        have hnK : K < n.natAbs := by
          simp only [S,mem_lowFrequencies,not_lt] at hn
          omega
        have hs : ‖f x n-1‖ < (1:ℝ)/2 := by
          rw [← he x (hVsub hx).1.1 n]
          exact hsmall x (hVsub hx).1.2 n hnK
        simpa only [lp.coeFn_zero,Pi.zero_apply,norm_zero,add_zero,he x (hVsub hx).1.1 n]
          using norm_inv_sub_one_le (f x n) hs)
    refine ⟨ofFunctionOrZero p (fun n => (f x n)⁻¹-1),
      ofFunctionOrZero_apply_of_mem p _ hm,hb.trans ?_⟩
    change ‖head x‖+2*(‖e x‖+‖(0 : Coeff p)‖) ≤ _
    simp only [norm_zero,add_zero]
    have hhx : ‖head x‖ < ‖head a‖+1 := (hVsub hx).2.1
    have hex : ‖e x‖ < ‖e a‖+1 := (hVsub hx).2.2
    exact add_le_add hhx.le (mul_le_mul_of_nonneg_left hex.le (by norm_num)))
  exact ⟨hg,hv⟩

end NLS.Coeff
