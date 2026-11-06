import NLS.KdV.HillL2AllBoundaryLimits
import NLS.KdV.HillRealTraceParity
import NLS.ComplexAnalysis.ParametricUpperLogarithmBoundary

/-! # Continuity of the actual primitive at moving real Hill labels

The trace is the same signed value along each intrinsic label. Its
root tends jointly to zero on approaching the moving label from above.
The shared logarithm lemma then proves continuity of the actual endpoint
value in every continuous real L2 potential family, including collisions.
-/

noncomputable section
open Set Metric Complex Filter Topology
namespace NLS.KdV
open NLS.ComplexAnalysis

theorem continuous_hillL2UpperBoundaryPrimitive_label_family
    {T : Type*} [TopologicalSpace T]
    (Q : T → WeightedCoeff SpectralWeight.one.toWeight 2) (hQ : Continuous Q)
    (hq : ∀ t, SpectralWeight.one.toCoeff (Q t) ∈ Coeff.paritySubspace 0)
    (hr : ∀ t, IsRealHillPotential (SpectralWeight.one.toCoeff (Q t))) (j : ℕ) :
    Continuous (fun t => hillL2UpperBoundaryPrimitive (SpectralWeight.one.toCoeff (Q t))
      (hillRealLabels (Q t) (hq t) (hr t) j)) := by
  let L : T → ℝ := fun t => hillRealLabels (Q t) (hq t) (hr t) j
  have hL : Continuous L := continuous_hillRealLabels_family Q hQ hq hr j
  let E : T × ℝ → ℂ × Coeff 2 := fun p =>
    ((L p.1 : ℂ) + (p.2 : ℂ) * I, SpectralWeight.one.toCoeff (Q p.1))
  have hE : Continuous E :=
    ((Complex.continuous_ofReal.comp (hL.comp continuous_fst)).add
      ((Complex.continuous_ofReal.comp continuous_snd).mul_const I)).prodMk
        ((SpectralWeight.one.toCoeff.continuous.comp hQ).comp continuous_fst)
  let F : T → ℝ → ℂ := fun t ε => hillL2ContinuedPrimitive (E (t, ε))
  let B : T → ℂ := fun t => hillL2UpperBoundaryPrimitive (SpectralWeight.one.toCoeff (Q t)) (L t)
  let m : ℂ := (-1 : ℂ) ^ ((j + 1) / 2)
  have hm : m ≠ 0 := pow_ne_zero _ (by norm_num)
  have hm2 : m ^ 2 = 1 := by
    dsimp only [m]
    rw [← pow_mul, Nat.mul_comm ((j + 1) / 2) 2, pow_mul]
    norm_num
  have hdom (t : T) (ε : ℝ) (hε : 0 < ε) : E (t, ε) ∈ hillL2ContinuationDomain := by
    apply mem_hillL2ContinuationDomain_of_im_ne_zero (Q t) (hq t) (hr t)
    simpa only [ofReal_im, add_im, mul_im, ofReal_re, I_im, I_re,
      mul_one, mul_zero, zero_add, add_zero] using hε.ne'
  refine continuous_boundary_logarithm_of_constant_exponential F B m hm ?_ ?_ ?_ ?_ ?_
  · intro ε hε
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (analyticOnNhd_hillL2ContinuedPrimitive _ (hdom t ε hε)).continuousAt.comp
      (f := fun t => E (t, ε)) (hE.comp (continuous_id.prodMk continuous_const)).continuousAt
  · intro t ε hε
    exact ((analyticOnNhd_hillL2ContinuedPrimitive _ (hdom t ε hε)).continuousAt.comp
      (f := fun ε => E (t, ε))
      (hE.comp (continuous_const.prodMk continuous_id)).continuousAt).continuousWithinAt
  · intro t
    exact (tendsto_hillL2UpperBoundaryPrimitive_all (Q t) (hq t) (hr t) (L t)).comp
      (tendsto_real_upper_vertical (L t))
  · intro t
    have hz := (hillRealLabels_spec (Q t) (hq t) (hr t)).root j
    have he := hillL2UpperBoundaryPrimitive_exp_at_zero (Q t) (hq t) (hr t) (L t) hz
    change exp (B t) = _ at he
    rw [hillRealLabels_trace_parity] at he
    simpa only [mul_div_cancel_left₀ _ (by norm_num : (2 : ℂ) ≠ 0)] using he
  · intro t0
    let l : Filter (T × ℝ) := 𝓝 t0 ×ˢ 𝓝[>] 0
    have hl : l ≤ 𝓝 (t0, (0 : ℝ)) := by
      rw [nhds_prod_eq]
      exact Filter.prod_mono le_rfl nhdsWithin_le_nhds
    have hD : Tendsto (fun p => hillL2Discriminant (E p).2 (E p).1) l (𝓝 (2 * m)) := by
      have hc : ContinuousAt (fun p => hillL2Discriminant (E p).2 (E p).1) (t0, (0 : ℝ)) :=
        (analyticOnNhd_hillL2Discriminant_joint _ (mem_univ _)).continuousAt.comp
        (f := E) hE.continuousAt
      have he : hillL2Discriminant (E (t0, 0)).2 (E (t0, 0)).1 = 2 * m := by
        simpa only [E, ofReal_zero, zero_mul, add_zero] using
          hillRealLabels_trace_parity (Q t0) (hq t0) (hr t0) j
      simpa only [he] using hc.tendsto.mono_left hl
    have hpos : ∀ᶠ p : T × ℝ in l, 0 < p.2 :=
      Filter.tendsto_snd.eventually self_mem_nhdsWithin
    have hR : Tendsto (fun p => hillL2ContinuedRoot (E p)) l (𝓝 0) := by
      apply tendsto_zero_of_sq_tendsto_zero
      have hδ : Tendsto (fun p => hillL2Discriminant (E p).2 (E p).1 ^ 2 - 4) l (𝓝 0) := by
        have he : (2 * m) ^ 2 - 4 = 0 := by rw [mul_pow, hm2]; ring
        simpa only [he] using (hD.pow 2).sub_const 4
      apply hδ.congr'
      filter_upwards [hpos] with p hp
      exact (hillL2ContinuedRoot_sq _ (hdom p.1 p.2 hp)).symm
    have hM := (hD.add hR).div_const 2
    have he : (2 * m + 0) / 2 = m := by ring
    rw [he] at hM
    apply hM.congr'
    filter_upwards [hpos] with p hp
    exact (exp_hillL2ContinuedPrimitive _ (hdom p.1 p.2 hp)).symm

end NLS.KdV
