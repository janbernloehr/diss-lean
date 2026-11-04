import NLS.ComplexAnalysis.HilbertWeightedProduct
import NLS.SequenceSpaces.HolderEmbedding
import NLS.SequenceSpaces.Truncation
import NLS.ComplexAnalysis.SmallAbsoluteProducts
import Mathlib.Analysis.Normed.Operator.NormedSpace

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal ComplexConjugate

namespace NLS.ComplexAnalysis



theorem tendsto_holderProduct_of_bounded_weak_weights
    {ι : Type*} {l : Filter ι} (b : ι → Coeff 2) (C : ℝ)
    (hb : ∀ i, ‖b i‖ ≤ C) (hcoord : ∀ m : ℤ, Tendsto (fun i => b i m) l (𝓝 0))
    (a : Coeff 2) : Tendsto (fun i => Coeff.holderProduct (q := 1) a (b i)) l (𝓝 0) := by
  let T : ι → Coeff 2 →L[ℂ] Coeff 1 := fun i => (Coeff.holderProduct (p := 2) (r := 2) (q := 1)).flip (b i)
  have hbound : ∃ D : ℝ, ∀ i (v : Coeff 2), ‖T i v‖ ≤ D*‖v‖ := by
    refine ⟨C,?_⟩
    intro i v
    exact (Coeff.norm_holderProduct_le v (b i)).trans (by
      have ht := mul_le_mul_of_nonneg_left (hb i) (norm_nonneg v)
      simpa only [mul_comm] using ht)
  have heq : Equicontinuous ((↑) ∘ T) := ((NormedSpace.equicontinuous_TFAE T).out 3 1).mp hbound
  apply (heq a).tendsto_of_mem_closure (f := fun _ => (0 : Coeff 1)) tendsto_const_nhds _
    (Coeff.dense_finiteSupport (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) a)
  intro v hv
  obtain ⟨s,hs⟩ := hv
  have hvs : v = Coeff.truncate s v := by
    ext m
    by_cases hm : m ∈ s <;> simp [Coeff.truncate_apply,hm,hs]
  rw [hvs,Coeff.truncate]
  simp only [Function.comp_apply,map_sum]
  have hsingle (m : ℤ) : Tendsto (fun i => T i (lp.single 2 m (v m))) l (𝓝 (0 : Coeff 1)) := by
    have he (i : ι) : T i (lp.single 2 m (v m)) = lp.single 1 m (v m*b i m) := by
      ext j
      by_cases hj : j = m
      · subst j
        simp only [T,ContinuousLinearMap.flip_apply,Coeff.holderProduct_apply,lp.single_apply,Pi.single_eq_same]
      · simp only [T,ContinuousLinearMap.flip_apply,Coeff.holderProduct_apply,
          lp.single_apply_ne _ _ _ hj,zero_mul]
    simp_rw [he]
    have hm : Tendsto (fun i => v m*b i m) l (𝓝 0) := by
      simpa only [mul_zero] using (hcoord m).const_mul (v m)
    have ht := ((lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) 1 m).continuous.tendsto 0).comp hm
    have hsingleApply (c : ℂ) : (lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) 1 m) c = lp.single 1 m c := rfl
    simpa only [Function.comp_def,hsingleApply,lp.single_zero] using ht
  simpa only [Finset.sum_const_zero] using tendsto_finsetSum s (fun m _ => hsingle m)

theorem tendsto_hilbertWeightedProduct_of_bounded_weak_weights
    {ι : Type*} {l : Filter ι} (b : ι → Coeff 2) (C : ℝ)
    (hb : ∀ i, ‖b i‖ ≤ C) (hcoord : ∀ m : ℤ, Tendsto (fun i => b i m) l (𝓝 0))
    (a : Coeff 2) : Tendsto (fun i => hilbertWeightedProduct (b i) a) l (𝓝 1) := by
  have ht := (tendsto_holderProduct_of_bounded_weak_weights b C hb hcoord a).norm
  have hs : Tendsto (fun i => ∑' m : ℤ, ‖a m*b i m‖) l (𝓝 0) := by
    simpa only [lp.norm_eq_tsum_rpow (by norm_num : (0 : ℝ) < (1 : ℝ≥0∞).toReal),
      ENNReal.toReal_one,one_div,inv_one,Real.rpow_one,Coeff.holderProduct_apply,lp.coeFn_zero,Pi.zero_apply,norm_zero,tsum_zero] using ht
  apply tendsto_tprod_one_add_of_tsum_norm_tendsto_zero
  · exact Eventually.of_forall (fun i => summable_norm_hilbertProductInput (b i) a)
  · exact hs

end NLS.ComplexAnalysis
