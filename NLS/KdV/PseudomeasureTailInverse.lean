import NLS.KdV.PseudomeasurePerturbation
import NLS.FunctionalAnalysis.NeumannCompositionBound
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Uniform endpoint contraction cutoff and tail inverse

For each regularity and potential norm bound, one cutoff works for every
spectral weight, every potential in that ball, and every lambda in the
corrected radius-6n strip. Both opposite shifted endpoint operators are covered.
-/
noncomputable section
open Filter Topology
open scoped ENNReal
namespace NLS.KdV

theorem endpointHillConstant_pos (r : ℝ) (hr1 : r<1/2) : 0 < endpointHillConstant r := by
  unfold endpointHillConstant
  have hh : 0 < 1-2*r := by linarith
  positivity

/-- The constant increases with roughness r=-s, as required by the source. -/
theorem endpointHillConstant_mono {r t : ℝ} (hrt : r≤t) (ht : t<1/2) :
    endpointHillConstant r ≤ endpointHillConstant t := by
  unfold endpointHillConstant
  exact add_le_add le_rfl
    (div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith))

/-- One cutoff for all potentials in a bounded set; dependence on w is absent. -/
theorem exists_endpointHill_cutoff (r : ℝ) (hr1 : r<1/2) (R : ℝ) :
    ∃ N : ℕ, 1≤N ∧ ∀ n : ℕ, N≤n →
      endpointHillConstant r * (n:ℝ)^(r-1/2) * R ≤ 1/2 := by
  have ht : Tendsto (fun n : ℕ => (n:ℝ)^(r-1/2)) atTop (𝓝 0) := by
    have hh := (tendsto_rpow_neg_atTop (show 0<(1/2:ℝ)-r by linarith)).comp
      tendsto_natCast_atTop_atTop
    simpa only [Function.comp_def, show -((1/2:ℝ)-r)=r-1/2 by ring] using hh
  have hlim : Tendsto (fun n : ℕ => endpointHillConstant r*(n:ℝ)^(r-1/2)*R) atTop (𝓝 0) := by
    simpa only [mul_zero,zero_mul] using (ht.const_mul (endpointHillConstant r)).mul_const R
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2)))
  exact ⟨max N 1, le_max_right _ _, fun n hn => (hN n ((le_max_left N 1).trans hn)).le⟩

/-- Op-norm form of the full +n shifted endpoint estimate. -/
theorem norm_endpointHillPerturbation_operator_le (w : SpectralWeight) (r : ℝ) (hr : 0≤r) (hr1 : r<1/2)
    (n : ℕ) (hn : 1≤n) (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (q : WeightedCoeff (w.negativeSobolev r) ⊤) :
    ‖endpointHillPerturbation w r hr hr1 n hn z hz q‖ ≤
      endpointHillConstant r * (n:ℝ)^(r-1/2) * ‖q‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (mul_nonneg (endpointHillConstant_pos r hr1).le (Real.rpow_nonneg (by positivity) _)) (norm_nonneg q))
  exact norm_endpointHillPerturbation_le w r hr hr1 n hn z hz q

/-- Op-norm form for the -n shifted realization of the same Fourier operator. -/
theorem norm_endpointHillPerturbationMinus_operator_le (w : SpectralWeight) (r : ℝ) (hr : 0≤r) (hr1 : r<1/2)
    (n : ℕ) (hn : 1≤n) (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (q : WeightedCoeff (w.negativeSobolev r) ⊤) :
    ‖endpointHillPerturbationMinus w r hr hr1 n hn z hz q‖ ≤
      endpointHillConstant r * (n:ℝ)^(r-1/2) * ‖q‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (mul_nonneg (endpointHillConstant_pos r hr1).le (Real.rpow_nonneg (by positivity) _)) (norm_nonneg q))
  exact norm_endpointHillPerturbationMinus_le w r hr hr1 n hn z hz q

/-- Source Corollary 2.5: one potential-norm cutoff simultaneously controls
both shifted endpoint norms, uniformly in lambda and spectral weight. -/
theorem exists_endpointHill_uniform_contraction (r : ℝ) (hr : 0≤r) (hr1 : r<1/2) (R : ℝ) :
    ∃ N : ℕ, 1≤N ∧ ∀ (w : SpectralWeight)
      (q : WeightedCoeff (w.negativeSobolev r) ⊤), ‖q‖≤R →
      ∀ (n : ℕ) (hn : 1≤n), N≤n → ∀ (z : ℂ) (hz : z ∈ reducedHillStrip n),
        ‖endpointHillPerturbation w r hr hr1 n hn z hz q‖ ≤ 1/2 ∧
        ‖endpointHillPerturbationMinus w r hr hr1 n hn z hz q‖ ≤ 1/2 := by
  obtain ⟨N,hN,hcut⟩ := exists_endpointHill_cutoff r hr1 R
  refine ⟨N,hN,?_⟩
  intro w q hq n hn hnN z hz
  have hb : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2 :=
    (mul_le_mul_of_nonneg_left hq (mul_nonneg (endpointHillConstant_pos r hr1).le
      (Real.rpow_nonneg (by positivity) _))).trans (hcut n hnN)
  exact ⟨(norm_endpointHillPerturbation_operator_le w r hr hr1 n hn z hz q).trans hb,
    (norm_endpointHillPerturbationMinus_operator_le w r hr hr1 n hn z hz q).trans hb⟩

/-- The actual source tail equation has a two-sided bounded inverse in the
+n shifted endpoint space whenever its explicit norm criterion is satisfied. -/
theorem exists_endpointHill_tail_inverse (w : SpectralWeight) (r : ℝ) (hr : 0≤r) (hr1 : r<1/2)
    (n : ℕ) (hn : 1≤n) (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (q : WeightedCoeff (w.negativeSobolev r) ⊤)
    (hsmall : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2) :
    ∃ K : WeightedCoeff ((w.negativeSobolev r).shift (n:ℤ)) ⊤ →L[ℂ]
        WeightedCoeff ((w.negativeSobolev r).shift (n:ℤ)) ⊤,
      (ContinuousLinearMap.id ℂ _-endpointHillPerturbation w r hr hr1 n hn z hz q).comp K = ContinuousLinearMap.id ℂ _ ∧
      K.comp (ContinuousLinearMap.id ℂ _-endpointHillPerturbation w r hr hr1 n hn z hz q) = ContinuousLinearMap.id ℂ _ ∧
      ‖K‖≤2 := by
  let E := WeightedCoeff ((w.negativeSobolev r).shift (n:ℤ)) ⊤
  let T := endpointHillPerturbation w r hr hr1 n hn z hz q
  have hT : ‖T‖≤(1/2:ℝ) := (norm_endpointHillPerturbation_operator_le w r hr hr1 n hn z hz q).trans hsmall
  have hnear : ‖(ContinuousLinearMap.id ℂ E).comp
      (ContinuousLinearMap.id ℂ E-(ContinuousLinearMap.id ℂ E-T))‖ ≤ (1/2:ℝ) := by
    have he : ContinuousLinearMap.id ℂ E-(ContinuousLinearMap.id ℂ E-T)=T := by abel
    simpa only [he,ContinuousLinearMap.id_comp] using hT
  obtain ⟨K,h1,h2,hK⟩ := NLS.exists_inverse_norm_le_two_mul_of_composition_near
    (ContinuousLinearMap.id ℂ E-T) (ContinuousLinearMap.id ℂ E) (ContinuousLinearMap.id ℂ E)
    (by simp) (by simp) hnear
  refine ⟨K,h1,h2,?_⟩
  have hid : ‖ContinuousLinearMap.id ℂ E‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  exact hK.trans (by nlinarith)

/-- The same bounded two-sided inverse in the -n shifted endpoint space. -/
theorem exists_endpointHill_tail_inverseMinus (w : SpectralWeight) (r : ℝ) (hr : 0≤r) (hr1 : r<1/2)
    (n : ℕ) (hn : 1≤n) (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (q : WeightedCoeff (w.negativeSobolev r) ⊤)
    (hsmall : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2) :
    ∃ K : WeightedCoeff ((w.negativeSobolev r).shift (-(n:ℤ))) ⊤ →L[ℂ]
        WeightedCoeff ((w.negativeSobolev r).shift (-(n:ℤ))) ⊤,
      (ContinuousLinearMap.id ℂ _-endpointHillPerturbationMinus w r hr hr1 n hn z hz q).comp K = ContinuousLinearMap.id ℂ _ ∧
      K.comp (ContinuousLinearMap.id ℂ _-endpointHillPerturbationMinus w r hr hr1 n hn z hz q) = ContinuousLinearMap.id ℂ _ ∧
      ‖K‖≤2 := by
  let E := WeightedCoeff ((w.negativeSobolev r).shift (-(n:ℤ))) ⊤
  let T := endpointHillPerturbationMinus w r hr hr1 n hn z hz q
  have hT : ‖T‖≤(1/2:ℝ) := (norm_endpointHillPerturbationMinus_operator_le w r hr hr1 n hn z hz q).trans hsmall
  have hnear : ‖(ContinuousLinearMap.id ℂ E).comp
      (ContinuousLinearMap.id ℂ E-(ContinuousLinearMap.id ℂ E-T))‖ ≤ (1/2:ℝ) := by
    have he : ContinuousLinearMap.id ℂ E-(ContinuousLinearMap.id ℂ E-T)=T := by abel
    simpa only [he,ContinuousLinearMap.id_comp] using hT
  obtain ⟨K,h1,h2,hK⟩ := NLS.exists_inverse_norm_le_two_mul_of_composition_near
    (ContinuousLinearMap.id ℂ E-T) (ContinuousLinearMap.id ℂ E) (ContinuousLinearMap.id ℂ E)
    (by simp) (by simp) hnear
  refine ⟨K,h1,h2,?_⟩
  have hid : ‖ContinuousLinearMap.id ℂ E‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  exact hK.trans (by nlinarith)

/-- Uniform invertibility of both actual shifted tail operators on each
potential norm ball, with one cutoff independent of the spectral weight. -/
theorem exists_endpointHill_uniform_tail_isUnit (r : ℝ) (hr : 0≤r) (hr1 : r<1/2) (R : ℝ) :
    ∃ N : ℕ, 1≤N ∧ ∀ (w : SpectralWeight)
      (q : WeightedCoeff (w.negativeSobolev r) ⊤), ‖q‖≤R →
      ∀ (n : ℕ) (hn : 1≤n), N≤n → ∀ (z : ℂ) (hz : z ∈ reducedHillStrip n),
        IsUnit (1-endpointHillPerturbation w r hr hr1 n hn z hz q) ∧
        IsUnit (1-endpointHillPerturbationMinus w r hr hr1 n hn z hz q) := by
  obtain ⟨N,hN,hsmall⟩ := exists_endpointHill_uniform_contraction r hr hr1 R
  refine ⟨N,hN,?_⟩
  intro w q hq n hn hnN z hz
  have hs := hsmall w q hq n hn hnN z hz
  exact ⟨isUnit_one_sub_of_norm_lt_one (hs.1.trans_lt (by norm_num)),
    isUnit_one_sub_of_norm_lt_one (hs.2.trans_lt (by norm_num))⟩

/-- The canonical tail inverse on the one original unshifted endpoint carrier.
It is obtained from the proved shifted inverse by coefficient-preserving transport. -/
def endpointHillTailInverse (w : SpectralWeight) (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (q : WeightedCoeff (w.negativeSobolev r) ⊤)
    (hsmall : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2) :
    WeightedCoeff (w.negativeSobolev r) ⊤ →L[ℂ] WeightedCoeff (w.negativeSobolev r) ⊤ :=
  (w.negativeShiftEquiv r hr (n:ℤ) ⊤).symm.toContinuousLinearMap.comp
    ((Classical.choose (exists_endpointHill_tail_inverse w r hr hr1 n hn z hz q hsmall)).comp
      (w.negativeShiftEquiv r hr (n:ℤ) ⊤).toContinuousLinearMap)

/-- Left inverse of the actual unshifted endpoint tail equation. -/
theorem endpointHillTailInverse_left (w : SpectralWeight) (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (q : WeightedCoeff (w.negativeSobolev r) ⊤)
    (hsmall : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2)
    (a : WeightedCoeff (w.negativeSobolev r) ⊤) :
    endpointHillTailInverse w r hr hr1 n hn z hz q hsmall
      (a-unshiftedEndpointHillPerturbation w r hr hr1 n hn z hz q a) = a := by
  let e := w.negativeShiftEquiv r hr (n:ℤ) ⊤
  let K := Classical.choose (exists_endpointHill_tail_inverse w r hr hr1 n hn z hz q hsmall)
  have h := congrArg (fun A => A (e a))
    (Classical.choose_spec (exists_endpointHill_tail_inverse w r hr hr1 n hn z hz q hsmall)).2.1
  change K (e a-endpointHillPerturbation w r hr hr1 n hn z hz q (e a)) = e a at h
  change e.symm (K (e (a-e.symm (endpointHillPerturbation w r hr hr1 n hn z hz q (e a))))) = a
  rw [map_sub, ContinuousLinearEquiv.apply_symm_apply, h, ContinuousLinearEquiv.symm_apply_apply]

/-- Right inverse of the actual unshifted endpoint tail equation. -/
theorem endpointHillTailInverse_right (w : SpectralWeight) (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (q : WeightedCoeff (w.negativeSobolev r) ⊤)
    (hsmall : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2)
    (a : WeightedCoeff (w.negativeSobolev r) ⊤) :
    endpointHillTailInverse w r hr hr1 n hn z hz q hsmall a -
      unshiftedEndpointHillPerturbation w r hr hr1 n hn z hz q
        (endpointHillTailInverse w r hr hr1 n hn z hz q hsmall a) = a := by
  let e := w.negativeShiftEquiv r hr (n:ℤ) ⊤
  let K := Classical.choose (exists_endpointHill_tail_inverse w r hr hr1 n hn z hz q hsmall)
  apply e.injective
  change e (e.symm (K (e a))-e.symm
    (endpointHillPerturbation w r hr hr1 n hn z hz q (e (e.symm (K (e a)))))) = e a
  simp only [map_sub, ContinuousLinearEquiv.apply_symm_apply]
  exact congrArg (fun A => A (e a))
    (Classical.choose_spec (exists_endpointHill_tail_inverse w r hr hr1 n hn z hz q hsmall)).1

/-- Uniqueness of every original endpoint tail solution. -/
theorem endpointHillTailInverse_unique (w : SpectralWeight) (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (q : WeightedCoeff (w.negativeSobolev r) ⊤)
    (hsmall : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2)
    (a b : WeightedCoeff (w.negativeSobolev r) ⊤)
    (hab : a-unshiftedEndpointHillPerturbation w r hr hr1 n hn z hz q a = b) :
    a = endpointHillTailInverse w r hr hr1 n hn z hz q hsmall b := by
  rw [← hab, endpointHillTailInverse_left]

/-- The canonical inverse has the source's norm bound two in both opposite
shifted norms, on the same original carrier and for every source weight. -/
theorem negativeShiftedNorm_endpointHillTailInverse_le (w : SpectralWeight)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2) (n : ℕ) (hn : 1 ≤ n)
    (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (q : WeightedCoeff (w.negativeSobolev r) ⊤)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2)
    (a : WeightedCoeff (w.negativeSobolev r) ⊤) :
    w.negativeShiftedNorm r hr (n:ℤ) ⊤ (endpointHillTailInverse w r hr hr1 n hn z hz q hs a) ≤
        2*w.negativeShiftedNorm r hr (n:ℤ) ⊤ a ∧
      w.negativeShiftedNorm r hr (-(n:ℤ)) ⊤ (endpointHillTailInverse w r hr hr1 n hn z hz q hs a) ≤
        2*w.negativeShiftedNorm r hr (-(n:ℤ)) ⊤ a := by
  constructor
  · let e := w.negativeShiftEquiv r hr (n:ℤ) ⊤
    let K := Classical.choose (exists_endpointHill_tail_inverse w r hr hr1 n hn z hz q hs)
    change ‖e (e.symm (K (e a)))‖ ≤ 2*‖e a‖
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact (K.le_opNorm (e a)).trans (mul_le_mul_of_nonneg_right
      (Classical.choose_spec (exists_endpointHill_tail_inverse w r hr hr1 n hn z hz q hs)).2.2
        (norm_nonneg _))
  · let e := w.negativeShiftEquiv r hr (-(n:ℤ)) ⊤
    let K := Classical.choose (exists_endpointHill_tail_inverseMinus w r hr hr1 n hn z hz q hs)
    let y := endpointHillTailInverse w r hr hr1 n hn z hz q hs a
    have he := congrArg e (endpointHillTailInverse_right w r hr hr1 n hn z hz q hs a)
    rw [map_sub] at he
    change e y-e (unshiftedEndpointHillPerturbation w r hr hr1 n hn z hz q y) = e a at he
    change w.negativeShiftEquiv r hr (-(n:ℤ)) ⊤ y -
      w.negativeShiftEquiv r hr (-(n:ℤ)) ⊤
        (unshiftedEndpointHillPerturbation w r hr hr1 n hn z hz q y) = e a at he
    rw [negativeShift_unshiftedEndpointHillPerturbation] at he
    have hL := congrArg (fun T => T (e y))
      (Classical.choose_spec (exists_endpointHill_tail_inverseMinus w r hr hr1 n hn z hz q hs)).2.1
    change K (e y-endpointHillPerturbationMinus w r hr hr1 n hn z hz q (e y)) = e y at hL
    rw [he] at hL
    change ‖e y‖ ≤ 2*‖e a‖
    rw [← hL]
    exact (K.le_opNorm (e a)).trans (mul_le_mul_of_nonneg_right
      (Classical.choose_spec (exists_endpointHill_tail_inverseMinus w r hr hr1 n hn z hz q hs)).2.2
        (norm_nonneg _))

end NLS.KdV
