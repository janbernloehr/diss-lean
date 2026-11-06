import NLS.ComplexAnalysis.HilbertWeakWeightLimits

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal ComplexConjugate Classical

namespace NLS.ComplexAnalysis



/-- Bounded coefficient-null weights annihilate a norm-convergent
family of Hilbert inputs under the Holder product. -/
theorem tendsto_holderProduct_of_bounded_weak_weights_of_tendsto
    {ι : Type*} {l : Filter ι} (b : ι → Coeff 2) (C : ℝ)
    (hb : ∀ i, ‖b i‖ ≤ C) (hcoord : ∀ m : ℤ, Tendsto (fun i => b i m) l (𝓝 0))
    (a : ι → Coeff 2) (a0 : Coeff 2) (ha : Tendsto a l (𝓝 a0)) :
    Tendsto (fun i => Coeff.holderProduct (q := 1) (a i) (b i)) l (𝓝 0) := by
  have hnorm : Tendsto (fun i => C*‖a i-a0‖) l (𝓝 0) := by
    simpa only [sub_self,norm_zero,mul_zero] using (ha.sub (tendsto_const_nhds (x := a0))).norm.const_mul C
  have hd : Tendsto (fun i => Coeff.holderProduct (q := 1) (a i-a0) (b i)) l (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun i => norm_nonneg _) _ hnorm
    intro i
    exact (Coeff.norm_holderProduct_le (a i-a0) (b i)).trans (by
      have hh := mul_le_mul_of_nonneg_left (hb i) (norm_nonneg (a i-a0))
      simpa only [mul_comm] using hh)
  have he (i : ι) : Coeff.holderProduct (q := 1) (a i) (b i)=
      Coeff.holderProduct (q := 1) (a i-a0) (b i)+Coeff.holderProduct (q := 1) a0 (b i) := by
    ext m
    simp only [Coeff.holderProduct_apply,lp.coeFn_sub,Pi.sub_apply,lp.coeFn_add,Pi.add_apply]
    ring
  simp_rw [he]
  simpa only [add_zero] using hd.add (tendsto_holderProduct_of_bounded_weak_weights b C hb hcoord a0)

theorem tendsto_hilbertWeightedProduct_of_bounded_weak_weights_of_tendsto
    {ι : Type*} {l : Filter ι} (b : ι → Coeff 2) (C : ℝ)
    (hb : ∀ i, ‖b i‖ ≤ C) (hcoord : ∀ m : ℤ, Tendsto (fun i => b i m) l (𝓝 0))
    (a : ι → Coeff 2) (a0 : Coeff 2) (ha : Tendsto a l (𝓝 a0)) :
    Tendsto (fun i => hilbertWeightedProduct (b i) (a i)) l (𝓝 1) := by
  have ht := (tendsto_holderProduct_of_bounded_weak_weights_of_tendsto b C hb hcoord a a0 ha).norm
  have hs : Tendsto (fun i => ∑' m : ℤ, ‖a i m*b i m‖) l (𝓝 0) := by
    simpa only [lp.norm_eq_tsum_rpow (by norm_num : (0 : ℝ) < (1 : ℝ≥0∞).toReal),
      ENNReal.toReal_one,one_div,inv_one,Real.rpow_one,Coeff.holderProduct_apply,lp.coeFn_zero,Pi.zero_apply,norm_zero,tsum_zero] using ht
  apply tendsto_tprod_one_add_of_tsum_norm_tendsto_zero
  · exact Eventually.of_forall (fun i => summable_norm_hilbertProductInput (b i) (a i))
  · exact hs

end NLS.ComplexAnalysis
