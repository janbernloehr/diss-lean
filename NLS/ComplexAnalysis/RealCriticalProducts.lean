import NLS.ComplexAnalysis.RealEndpointRootSigns
import NLS.ComplexAnalysis.EndpointCriticalRatioBounds
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-! # Real endpoint roots and positivity of convergent critical products. -/

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
open NLS.ZakharovShabat
namespace NLS.ComplexAnalysis

theorem endpointRoot_real_right (a b x : ℝ) (hab : a ≤ b) (hx : b < x) :
    (endpointRoot a b x).re < 0 ∧ (endpointRoot a b x).im = 0 := by
  have hp : (endpointRoot a b x).re < 0 := by
    simpa only [endpointRoot,ofReal_div,ofReal_add,ofReal_sub,ofReal_pow,ofReal_ofNat] using
      normalizedStandardRoot_re_neg_of_gt_rightEndpoint a b x hab hx
  have hs : (x : ℂ) ∉ segment ℝ (a : ℂ) b := by
    intro h
    have hbound := re_mem_Icc_of_mem_real_segment a b hab (x : ℂ) h
    simp only [ofReal_re] at hbound
    linarith [hbound.2]
  have hi := congrArg Complex.im (endpointRoot_sq a b x hs)
  simp only [pow_two,mul_im,sub_im,ofReal_im,sub_self,mul_zero,zero_mul,add_zero] at hi
  exact ⟨hp,by nlinarith⟩

theorem critical_endpoint_ratio_real_positive (a b c x : ℝ) (hab : a ≤ b) (hc : c ∈ Icc a b)
    (hx : x < a ∨ b < x) :
    0 < (((c : ℂ)-x)/endpointRoot a b x).re ∧ (((c : ℂ)-x)/endpointRoot a b x).im = 0 := by
  have hsign : (0 < c-x ∧ 0 < (endpointRoot a b x).re ∧ (endpointRoot a b x).im = 0) ∨
      (c-x < 0 ∧ (endpointRoot a b x).re < 0 ∧ (endpointRoot a b x).im = 0) := by
    rcases hx with hl | hr
    · exact Or.inl ⟨by linarith [hc.1],endpointRoot_real_left a b x hab hl⟩
    · exact Or.inr ⟨by linarith [hc.2],endpointRoot_real_right a b x hab hr⟩
  have him : (endpointRoot a b x).im = 0 := by rcases hsign with h | h <;> exact h.2.2
  have he : endpointRoot a b x = ((endpointRoot a b x).re : ℂ) := by
    apply Complex.ext <;> simp [him]
  rw [he,← ofReal_sub,← ofReal_div]
  simp only [ofReal_re,ofReal_im]
  refine ⟨?_,trivial⟩
  rcases hsign with h | h
  · exact div_pos h.1 h.2.1
  · exact div_pos_of_neg_of_neg h.1 h.2.1

theorem HasProd.positive_real_of_each (f : ℕ → ℂ) (p : ℂ) (h : HasProd f p)
    (hf : ∀ k : ℕ, 0 < (f k).re ∧ (f k).im = 0) (hne : p ≠ 0) : 0 < p.re ∧ p.im = 0 := by
  have he (k : ℕ) : f k = ((f k).re : ℂ) := by
    apply Complex.ext <;> simp [(hf k).2]
  have hp := h.tendsto_prod_nat
  have hpartial (N : ℕ) : (∏ k ∈ Finset.range N, f k) = ((∏ k ∈ Finset.range N, (f k).re : ℝ) : ℂ) := by
    push_cast
    exact Finset.prod_congr rfl (fun k _ => he k)
  have him : p.im = 0 := by
    have hh := continuous_im.continuousAt.tendsto.comp hp
    change Tendsto (fun N => (∏ k ∈ Finset.range N, f k).im) atTop _ at hh
    simp only [hpartial,ofReal_im] at hh
    exact tendsto_nhds_unique hh tendsto_const_nhds
  have hre : 0 ≤ p.re := by
    apply ge_of_tendsto (continuous_re.continuousAt.tendsto.comp hp)
    filter_upwards with N
    change 0 ≤ (∏ k ∈ Finset.range N, f k).re
    rw [hpartial,ofReal_re]
    exact (Finset.prod_pos (fun k _ => (hf k).1)).le
  refine ⟨lt_of_le_of_ne hre ?_,him⟩
  intro heq
  apply hne
  apply Complex.ext <;> simp [heq,him]

theorem norm_endpointRoot_ge_right_distance (a b x : ℝ) (hab : a ≤ b) (hx : b < x) :
    x-b ≤ ‖endpointRoot a b x‖ := by
  have hs : (x : ℂ) ∉ segment ℝ (a : ℂ) b := by
    intro h
    have hbound := re_mem_Icc_of_mem_real_segment a b hab (x : ℂ) h
    simp only [ofReal_re] at hbound
    linarith [hbound.2]
  have h := congrArg norm (endpointRoot_sq a b x hs)
  simp only [norm_pow,norm_mul,← ofReal_sub,norm_real,Real.norm_eq_abs,
    abs_of_pos (sub_pos.mpr (hab.trans_lt hx)),abs_of_pos (sub_pos.mpr hx)] at h
  apply (sq_le_sq₀ (sub_nonneg.mpr hx.le) (norm_nonneg _)).mp
  rw [h]
  nlinarith [mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr hx.le)]

end NLS.ComplexAnalysis
