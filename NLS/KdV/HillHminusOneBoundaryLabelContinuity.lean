import NLS.KdV.HillHminusOneAllBoundaryLimits
import NLS.KdV.HillHminusOneTraceParity
import NLS.ComplexAnalysis.ParametricUpperLogarithmBoundary

/-! # Continuity of the actual primitive at moving real Hill labels

The trace is the same signed value along each intrinsic label. Its
root tends jointly to zero on approaching the moving label from above.
The shared logarithm lemma then proves continuity of the actual endpoint
value in every continuous real H^-1 potential family, including collisions.
-/

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
namespace NLS.KdV
open NLS.ComplexAnalysis

theorem continuous_hillHminusUpperBoundaryPrimitive_label_family
    {T : Type*} [TopologicalSpace T]
    (Q : T → PeriodOneHminusOne) (hQ : Continuous Q)
    (hr : ∀ t, IsRealPeriodOneHminusOne (Q t)) (j : ℕ) :
    Continuous (fun t => hillHminusUpperBoundaryPrimitive (Q t)
      (hillHminusRealLabels (Q t) (hr t) j)) := by
  let L : T → ℝ := fun t => hillHminusRealLabels (Q t) (hr t) j
  have hL : Continuous L := continuous_hillHminusRealLabels_family Q hQ hr j
  let E : T × ℝ → ℂ × PeriodOneHminusOne := fun p =>
    ((L p.1 : ℂ) + (p.2 : ℂ) * I, Q p.1)
  have hE : Continuous E :=
    ((Complex.continuous_ofReal.comp (hL.comp continuous_fst)).add
      ((Complex.continuous_ofReal.comp continuous_snd).mul_const I)).prodMk
        (hQ.comp continuous_fst)
  let F : T → ℝ → ℂ := fun t ε => hillHminusContinuedPrimitive (E (t, ε))
  let B : T → ℂ := fun t => hillHminusUpperBoundaryPrimitive (Q t) (L t)
  let m : ℂ := (-1 : ℂ) ^ ((j + 1) / 2)
  have hm : m ≠ 0 := pow_ne_zero _ (by norm_num)
  have hm2 : m ^ 2 = 1 := by
    dsimp only [m]
    rw [← pow_mul, Nat.mul_comm ((j + 1) / 2) 2, pow_mul]
    norm_num
  have hdom (t : T) (ε : ℝ) (hε : 0 < ε) : E (t, ε) ∈ hillHminusContinuationDomain := by
    apply mem_hillHminusContinuationDomain_of_im_ne_zero (Q t) (hr t)
    simpa only [ofReal_im, add_im, mul_im, ofReal_re, I_im, I_re,
      mul_one, mul_zero, zero_add, add_zero] using hε.ne'
  refine continuous_boundary_logarithm_of_constant_exponential F B m hm ?_ ?_ ?_ ?_ ?_
  · intro ε hε
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (analyticOnNhd_hillHminusContinuedPrimitive _ (hdom t ε hε)).continuousAt.comp
      (f := fun t => E (t, ε)) (hE.comp (continuous_id.prodMk continuous_const)).continuousAt
  · intro t ε hε
    exact ((analyticOnNhd_hillHminusContinuedPrimitive _ (hdom t ε hε)).continuousAt.comp
      (f := fun ε => E (t, ε))
      (hE.comp (continuous_const.prodMk continuous_id)).continuousAt).continuousWithinAt
  · intro t
    exact (tendsto_hillHminusUpperBoundaryPrimitive_all (Q t) (hr t) (L t)).comp
      (tendsto_real_upper_vertical (L t))
  · intro t
    have hz := hillHminusRealLabels_root (Q t) (hr t) j
    have he := hillHminusUpperBoundaryPrimitive_exp_at_zero (Q t) (hr t) (L t) hz
    change exp (B t) = _ at he
    rw [hillHminusRealLabels_trace_parity] at he
    simpa only [mul_div_cancel_left₀ _ (by norm_num : (2 : ℂ) ≠ 0)] using he
  · intro t0
    let l : Filter (T × ℝ) := 𝓝 t0 ×ˢ 𝓝[>] 0
    have hl : l ≤ 𝓝 (t0, (0 : ℝ)) := by
      rw [nhds_prod_eq]
      exact Filter.prod_mono le_rfl nhdsWithin_le_nhds
    have hD : Tendsto (fun p => hillHminusDiscriminant (E p).2 (E p).1) l (𝓝 (2 * m)) := by
      have hc : ContinuousAt (fun p => hillHminusDiscriminant (E p).2 (E p).1) (t0, (0 : ℝ)) :=
        (analyticOnNhd_hillHminusDiscriminant_joint _ (mem_univ _)).continuousAt.comp
        (f := E) hE.continuousAt
      have he : hillHminusDiscriminant (E (t0, 0)).2 (E (t0, 0)).1 = 2 * m := by
        simpa only [E, ofReal_zero, zero_mul, add_zero] using
          hillHminusRealLabels_trace_parity (Q t0) (hr t0) j
      simpa only [he] using hc.tendsto.mono_left hl
    have hpos : ∀ᶠ p : T × ℝ in l, 0 < p.2 :=
      Filter.tendsto_snd.eventually self_mem_nhdsWithin
    have hR : Tendsto (fun p => hillHminusContinuedRoot (E p)) l (𝓝 0) := by
      apply tendsto_zero_of_sq_tendsto_zero
      have hδ : Tendsto (fun p => hillHminusDiscriminant (E p).2 (E p).1 ^ 2 - 4) l (𝓝 0) := by
        have he : (2 * m) ^ 2 - 4 = 0 := by rw [mul_pow, hm2]; ring
        simpa only [he] using (hD.pow 2).sub_const 4
      apply hδ.congr'
      filter_upwards [hpos] with p hp
      exact (hillHminusContinuedRoot_sq _ (hdom p.1 p.2 hp)).symm
    have hM := (hD.add hR).div_const 2
    have he : (2 * m + 0) / 2 = m := by ring
    rw [he] at hM
    apply hM.congr'
    filter_upwards [hpos] with p hp
    exact (exp_hillHminusContinuedPrimitive _ (hdom p.1 p.2 hp)).symm

end NLS.KdV
