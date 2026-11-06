import NLS.Articles.KdVEstimates.ArnoldIntegerEstimates
import NLS.KdV.HillWeightedActionEstimate
import NLS.SequenceSpaces.SpectralWeightProduct

/-! # Theorem 3(ii) for the exact source weight class and actual positive-index actions. -/

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ENNReal
open NLS.KdV
namespace NLS.Articles.KdVEstimates

theorem theorem3_actions (r : ℝ) (hr0 : 0≤r) (hr1 : r≤1/2) (v : SpectralWeight) :
    let w := SpectralWeight.product (SpectralWeight.sobolev r hr0) v
    ∃ c : ℝ, 0<c ∧ ∀ p : RealHillWeightedPotential w, p.val.val 0=0 →
      (∑' k : ℕ, (w (2*((k+1 : ℕ) : ℤ)))^2*(2*Real.pi*(k+1 : ℕ))*
        hillPeriodOneAction w p.val p.property (k+1)) ≤
      c^2*((1+‖p.val‖)^2+(w.realExtension (16*‖p.val‖^(3/2-r)))^2)*‖p.val‖^2 := by
  dsimp only
  let w := SpectralWeight.product (SpectralWeight.sobolev r hr0) v
  let C : ℝ := 5000*Real.pi*Real.exp 1+(w (16 : ℤ)*w (3 : ℤ))^2
  have hC : 0≤C := by dsimp only [C]; positivity
  refine ⟨C+1,by linarith,?_⟩
  intro p hmean
  have h := hillWeightedAction_total_norm_bound w r hr0 hr1
    (fun m _ => SpectralWeight.sobolev_product_dominates v r hr0 m) p hmean
  have hz : hillWeightedActionTerm w p 0=0 := by simp [hillWeightedActionTerm]
  have hsplit := (summable_hillWeightedActionTerm w p).sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one,hz,zero_add] at hsplit
  rw [← hsplit] at h
  have hh : C≤(C+1)^2 := by nlinarith [sq_nonneg C]
  have hmul := mul_le_mul_of_nonneg_right hh
    (by positivity : 0≤((1+‖p.val‖)^2+(w.realExtension (16*‖p.val‖^(3/2-r)))^2)*‖p.val‖^2)
  have hfinal := h.trans (by simpa only [C,mul_assoc] using hmul)
  simpa only [hillWeightedActionTerm,C,w,mul_assoc] using hfinal

theorem theorem3_arnold (r : ℝ) (hr0 : 0≤r) (hr1 : r≤1/2) (v : SpectralWeight) :
    let w := SpectralWeight.product (SpectralWeight.sobolev r hr0) v
    ∃ c : ℝ, 0<c ∧ ∀ p : RealHillWeightedPotential w, p.val.val 0=0 →
      (∑' k : ℕ, (w (2*((k+1 : ℕ) : ℤ)))^2*(2*Real.pi*(k+1 : ℕ))*
        sourceArnoldAction (hillPeriodOneUnitPotential w p.val)
          (hillPeriodOneUnitPotential_even w p.val) (hillPeriodOneUnitPotential_real w p.val p.property) (k+1)) ≤
      c^2*((1+‖p.val‖)^2+(w.realExtension (16*‖p.val‖^(3/2-r)))^2)*‖p.val‖^2 := by
  obtain ⟨c,hc,hbound⟩ := theorem3_actions r hr0 hr1 v
  refine ⟨c,hc,?_⟩
  intro p hmean
  let w := SpectralWeight.product (SpectralWeight.sobolev r hr0) v
  have he (k : ℕ) : sourceArnoldAction (hillPeriodOneUnitPotential w p.val)
      (hillPeriodOneUnitPotential_even w p.val) (hillPeriodOneUnitPotential_real w p.val p.property) (k+1) =
      hillPeriodOneAction w p.val p.property (k+1) :=
    sourceArnoldAction_eq_gapIntegral _ _ _ (k+1) (by omega)
  dsimp only [w] at he
  simp_rw [he]
  exact hbound p hmean

end NLS.Articles.KdVEstimates
