import NLS.ComplexAnalysis.HilbertProductDeletion
import NLS.ComplexAnalysis.BanachTaylorBounds
import NLS.SequenceSpaces.Truncation
import Mathlib.Analysis.Normed.Operator.NormedSpace

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal ComplexConjugate Classical

namespace NLS.ComplexAnalysis



private theorem norm_deleted_hilbert_weight_le (b : Coeff 2) (m : ℤ) :
    ‖Coeff.deleteCoordinate m b‖≤‖b‖ := by
  apply lp.norm_mono (by norm_num : (2:ℝ≥0∞)≠0)
  intro j
  by_cases hj : j=m
  · subst j
    rw [Coeff.deleteCoordinate_apply_same,norm_zero]
    exact norm_nonneg _
  · rw [Coeff.deleteCoordinate_apply_other m j hj]

private theorem hilbertWeightedProduct_deleted_add_single (b a : Coeff 2) (m : ℤ) (s : ℂ) :
    hilbertWeightedProduct (Coeff.deleteCoordinate m b) (a+lp.single (E := fun _ : ℤ => ℂ) 2 m s)=
      hilbertWeightedProduct (Coeff.deleteCoordinate m b) a := by
  unfold hilbertWeightedProduct
  apply tprod_congr
  intro j
  by_cases hj : j=m
  · subst j
    rw [Coeff.deleteCoordinate_apply_same]
    simp only [mul_zero]
  · simp only [lp.coeFn_add,Pi.add_apply,lp.single_apply_ne _ _ _ hj,add_zero]

/-- Every scalar input coordinate enters the entire product affinely,
including when other product factors vanish. -/
theorem hilbertWeightedProduct_add_single (b a : Coeff 2) (m : ℤ) (s : ℂ) :
    hilbertWeightedProduct b (a+lp.single (E := fun _ : ℤ => ℂ) 2 m s)=hilbertWeightedProduct b a+
      s*b m*hilbertWeightedProduct (Coeff.deleteCoordinate m b) a := by
  rw [hilbertWeightedProduct_eq_factor_mul_deleted b (a+lp.single (E := fun _ : ℤ => ℂ) 2 m s) m,
    hilbertWeightedProduct_eq_factor_mul_deleted b a m,hilbertWeightedProduct_deleted_add_single]
  simp only [lp.coeFn_add,Pi.add_apply,lp.single_apply,Pi.single_eq_same]
  ring

/-- Actual derivative on a coordinate vector, with no division by factors. -/
theorem fderiv_hilbertWeightedProduct_single (b a : Coeff 2) (m : ℤ) :
    fderiv ℂ (hilbertWeightedProduct b) a (lp.single (E := fun _ : ℤ => ℂ) 2 m 1)=
      b m*hilbertWeightedProduct (Coeff.deleteCoordinate m b) a := by
  let S := lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) 2 m
  have hs : HasDerivAt (fun s : ℂ => a+lp.single (E := fun _ : ℤ => ℂ) 2 m s) (lp.single (E := fun _ : ℤ => ℂ) 2 m 1) 0 := by
    convert! (S.hasFDerivAt (x := (0:ℂ))).hasDerivAt.const_add a using 1
  have hf := (analyticOnNhd_hilbertWeightedProduct b a (mem_univ _)).differentiableAt.hasFDerivAt
  have hf' : HasFDerivAt (hilbertWeightedProduct b) (fderiv ℂ (hilbertWeightedProduct b) a)
      (a+lp.single (E := fun _ : ℤ => ℂ) 2 m (0:ℂ)) := by simpa only [lp.single_zero,add_zero] using hf
  have hd := hf'.comp_hasDerivAt 0 hs
  have he : (fun s : ℂ => hilbertWeightedProduct b (a+lp.single (E := fun _ : ℤ => ℂ) 2 m s))=
      (fun s : ℂ => hilbertWeightedProduct b a+s*(b m*hilbertWeightedProduct (Coeff.deleteCoordinate m b) a)) := by
    funext s
    rw [hilbertWeightedProduct_add_single]
    ring
  have hknown : HasDerivAt (fun s : ℂ => hilbertWeightedProduct b (a+lp.single (E := fun _ : ℤ => ℂ) 2 m s))
      (b m*hilbertWeightedProduct (Coeff.deleteCoordinate m b) a) 0 := by
    rw [he]
    convert! ((hasDerivAt_id (0:ℂ)).mul_const (b m*hilbertWeightedProduct (Coeff.deleteCoordinate m b) a)).const_add
      (hilbertWeightedProduct b a) using 1
    simp only [one_mul]
  exact hd.unique hknown

/-- The actual product derivatives have a common local operator bound. -/
theorem norm_fderiv_hilbertWeightedProduct_le (b a : Coeff 2) :
    ‖fderiv ℂ (hilbertWeightedProduct b) a‖≤2*Real.exp ((‖a‖+2)*‖b‖) := by
  have hb (v : Coeff 2) (hv : v∈ball a (1+1)) :
      ‖hilbertWeightedProduct b v‖≤Real.exp ((‖a‖+2)*‖b‖) := by
    have hv' : ‖v-a‖<2 := by simpa only [mem_ball,dist_eq_norm,show (1:ℝ)+1=2 by norm_num] using hv
    have hnorm : ‖v‖≤‖a‖+2 := (norm_le_norm_sub_add v a).trans (by linarith)
    exact (norm_hilbertWeightedProduct_le b v).trans
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hnorm (norm_nonneg b)))
  have hh := norm_fderiv_le_of_ball_bound (hilbertWeightedProduct b) a a 1 1 _ (by norm_num)
    ((analyticOnNhd_hilbertWeightedProduct b).differentiableOn.mono (subset_univ _)) hb (mem_ball_self (by norm_num))
  simpa only [div_one] using hh

/-- Bounded coefficient-null weights give strong convergence to zero
of the actual entire product derivatives on every fixed direction. -/
theorem tendsto_fderiv_hilbertWeightedProduct_of_bounded_weak_weights
    {ι : Type*} {l : Filter ι} (b : ι → Coeff 2) (C : ℝ)
    (hb : ∀ i, ‖b i‖≤C) (hcoord : ∀ m : ℤ, Tendsto (fun i => b i m) l (𝓝 0))
    (a h : Coeff 2) : Tendsto (fun i => fderiv ℂ (hilbertWeightedProduct (b i)) a h) l (𝓝 0) := by
  let T : ι → Coeff 2 →L[ℂ] ℂ := fun i => fderiv ℂ (hilbertWeightedProduct (b i)) a
  let M := 2*Real.exp ((‖a‖+2)*C)
  have hop (i : ι) : ‖T i‖≤M := (norm_fderiv_hilbertWeightedProduct_le (b i) a).trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hb i) (by positivity))) (by norm_num))
  have hbound : ∃ D : ℝ, ∀ i (v : Coeff 2), ‖T i v‖≤D*‖v‖ :=
    ⟨M,fun i v => (T i).le_opNorm v |>.trans (mul_le_mul_of_nonneg_right (hop i) (norm_nonneg v))⟩
  have heq : Equicontinuous ((↑) ∘ T) := ((NormedSpace.equicontinuous_TFAE T).out 3 1).mp hbound
  have hsingle (m : ℤ) : Tendsto (fun i => T i (lp.single (E := fun _ : ℤ => ℂ) 2 m 1)) l (𝓝 0) := by
    have hz : Tendsto (fun i => ‖b i m‖*Real.exp (‖a‖*C)) l (𝓝 0) := by
      simpa only [norm_zero,zero_mul] using (hcoord m).norm.mul_const (Real.exp (‖a‖*C))
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) (Eventually.of_forall (fun i => ?_)) hz
    rw [show T i (lp.single (E := fun _ : ℤ => ℂ) 2 m 1)=b i m*hilbertWeightedProduct (Coeff.deleteCoordinate m (b i)) a from
      fderiv_hilbertWeightedProduct_single (b i) a m,norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact (norm_hilbertWeightedProduct_le _ _).trans (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left ((norm_deleted_hilbert_weight_le (b i) m).trans (hb i)) (norm_nonneg a)))
  apply (heq h).tendsto_of_mem_closure (f := fun _ => (0:ℂ)) tendsto_const_nhds _
    (Coeff.dense_finiteSupport (by norm_num : (2:ℝ≥0∞)≠⊤) h)
  intro v hv
  obtain ⟨s,hs⟩ := hv
  have hv' : v=Coeff.truncate s v := by
    ext m
    by_cases hm : m∈s <;> simp [Coeff.truncate_apply,hm,hs]
  rw [hv',Coeff.truncate]
  simp only [Function.comp_apply,map_sum]
  have hcol (m : ℤ) : Tendsto (fun i => T i (lp.single (E := fun _ : ℤ => ℂ) 2 m (v m))) l (𝓝 0) := by
    have he : (lp.single (E := fun _ : ℤ => ℂ) 2 m (v m) : Coeff 2)=v m • lp.single (E := fun _ : ℤ => ℂ) 2 m 1 := by
      ext j
      by_cases hj : j=m <;> simp [lp.single_apply,hj]
    simp_rw [he,map_smul,smul_eq_mul]
    simpa only [mul_zero] using (hsingle m).const_mul (v m)
  simpa only [Finset.sum_const_zero] using tendsto_finsetSum s (fun m _ => hcol m)

end NLS.ComplexAnalysis
