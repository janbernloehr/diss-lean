import NLS.KdV.HillL2AllEndpointNormalization
import NLS.KdV.HillL2BoundaryGapProfile

/-! # Indexed actual boundary values on every closed real Hill gap

The constant interior phase extends to the endpoints by continuity.
Its exact endpoint normalization fixes it to the spectral index. This
gives the source arcosh formula on every closed gap, including low and
collapsed gaps, and the literal two-sided primitive jump.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ComplexConjugate
namespace NLS.KdV
open NLS.ComplexAnalysis

theorem hillL2UpperBoundaryPrimitive_gap_indexed
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1 ≤ n)
    (x : ℝ) (hx : x ∈ Icc (hillRealLabels q hq hr (2 * n - 1)) (hillRealLabels q hq hr (2 * n))) :
    hillL2UpperBoundaryPrimitive (SpectralWeight.one.toCoeff q) x =
      (hillRealGapProfile (SpectralWeight.one.toCoeff q) n x : ℂ) - I * (n : ℂ) * Real.pi := by
  let a := hillRealLabels q hq hr (2 * n - 1)
  let b := hillRealLabels q hq hr (2 * n)
  have hab : a ≤ b := monotone_hillRealLabels q hq hr (by omega)
  rcases lt_or_eq_of_le hab with hopen | hclosed
  · obtain ⟨k, hk⟩ := exists_hillL2UpperBoundaryPrimitive_gap_phase q hq hr n hn hopen
    have hG : ContinuousOn (fun y : ℝ => (hillRealGapProfile (SpectralWeight.one.toCoeff q) n y : ℂ) +
        I * (k : ℂ) * Real.pi) (Icc a b) :=
      (Complex.continuous_ofReal.comp_continuousOn (continuousOn_hillRealGapProfile q hq hr n hn)).add_const _
    have heq : EqOn (hillL2UpperBoundaryPrimitive (SpectralWeight.one.toCoeff q))
        (fun y => (hillRealGapProfile (SpectralWeight.one.toCoeff q) n y : ℂ) + I * (k : ℂ) * Real.pi)
        (Icc a b) := by
      exact (show EqOn _ _ (Ioo a b) from hk).of_subset_closure
        (continuous_hillL2UpperBoundaryPrimitive q hq hr).continuousOn hG
        Ioo_subset_Icc_self (by rw [closure_Ioo hopen.ne])
    have hshift : I * (k : ℂ) * Real.pi = -I * (n : ℂ) * Real.pi := by
      have he := heq ⟨le_rfl, hab⟩
      dsimp only [a] at he
      rw [(hillRealGapProfile_endpoints q hq hr n hn).1, ofReal_zero, zero_add] at he
      exact he.symm.trans (hillL2UpperBoundaryPrimitive_pair_indexed q hq hr n hn).1
    rw [heq hx, hshift]
    ring
  · have hx0 : x = a := le_antisymm (hx.2.trans hclosed.ge) hx.1
    rw [hx0, (hillRealGapProfile_endpoints q hq hr n hn).1, ofReal_zero, zero_sub]
    simpa only [neg_mul] using (hillL2UpperBoundaryPrimitive_pair_indexed q hq hr n hn).1

theorem tendsto_hillL2ContinuedPrimitive_gap_upper
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1 ≤ n)
    (x : ℝ) (hx : x ∈ Icc (hillRealLabels q hq hr (2 * n - 1)) (hillRealLabels q hq hr (2 * n))) :
    Tendsto (fun z => hillL2ContinuedPrimitive (z, SpectralWeight.one.toCoeff q))
      (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ))
      (𝓝 ((hillRealGapProfile (SpectralWeight.one.toCoeff q) n x : ℂ) - I * (n : ℂ) * Real.pi)) := by
  rw [← hillL2UpperBoundaryPrimitive_gap_indexed q hq hr n hn x hx]
  exact tendsto_hillL2UpperBoundaryPrimitive_all q hq hr x

theorem tendsto_hillL2ContinuedPrimitive_gap_lower
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1 ≤ n)
    (x : ℝ) (hx : x ∈ Icc (hillRealLabels q hq hr (2 * n - 1)) (hillRealLabels q hq hr (2 * n))) :
    Tendsto (fun z => hillL2ContinuedPrimitive (z, SpectralWeight.one.toCoeff q))
      (𝓝[{z : ℂ | z.im < 0}] (x : ℂ))
      (𝓝 (-(hillRealGapProfile (SpectralWeight.one.toCoeff q) n x : ℂ) - I * (n : ℂ) * Real.pi)) := by
  have hc : Tendsto (conj : ℂ → ℂ) (𝓝[{z : ℂ | z.im < 0}] (x : ℂ))
      (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [conj_ofReal] using (continuous_conj.tendsto (x : ℂ)).mono_left
        (nhdsWithin_le_nhds : 𝓝[{z : ℂ | z.im < 0}] (x : ℂ) ≤ 𝓝 (x : ℂ))
    · filter_upwards [self_mem_nhdsWithin] with z hz
      simpa only [conj_im, neg_pos] using hz
  have hu := (tendsto_hillL2ContinuedPrimitive_gap_upper q hq hr n hn x hx).comp hc
  have hl := (continuous_conj.continuousAt.tendsto.comp hu).neg
  have hv : -conj ((hillRealGapProfile (SpectralWeight.one.toCoeff q) n x : ℂ) -
      I * (n : ℂ) * Real.pi) =
      -(hillRealGapProfile (SpectralWeight.one.toCoeff q) n x : ℂ) - I * (n : ℂ) * Real.pi := by
    simp only [map_sub, map_mul, conj_ofReal, conj_I, map_natCast]
    ring
  rw [hv] at hl
  apply hl.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  have he := hillL2ContinuedPrimitive_conj _ hr z
    (mem_hillL2ContinuationDomain_of_im_ne_zero q hq hr z hz.ne)
  have hh := congrArg (fun w : ℂ => -conj w) he
  simpa only [Function.comp_def, map_neg, conj_conj, neg_neg] using hh

theorem tendsto_hillL2ContinuedPrimitive_gap_lower_vertical
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1 ≤ n)
    (x : ℝ) (hx : x ∈ Icc (hillRealLabels q hq hr (2 * n - 1)) (hillRealLabels q hq hr (2 * n))) :
    Tendsto (fun ε : ℝ => hillL2ContinuedPrimitive
      ((x : ℂ) - (ε : ℂ) * I, SpectralWeight.one.toCoeff q)) (𝓝[>] 0)
      (𝓝 (-(hillRealGapProfile (SpectralWeight.one.toCoeff q) n x : ℂ) - I * (n : ℂ) * Real.pi)) := by
  have hu := (tendsto_hillL2ContinuedPrimitive_gap_upper q hq hr n hn x hx).comp
    (tendsto_real_upper_vertical x)
  have hl := (continuous_conj.continuousAt.tendsto.comp hu).neg
  have hv : -conj ((hillRealGapProfile (SpectralWeight.one.toCoeff q) n x : ℂ) -
      I * (n : ℂ) * Real.pi) =
      -(hillRealGapProfile (SpectralWeight.one.toCoeff q) n x : ℂ) - I * (n : ℂ) * Real.pi := by
    simp only [map_sub, map_mul, conj_ofReal, conj_I, map_natCast]
    ring
  rw [hv] at hl
  apply hl.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have him : 0 < ((x : ℂ) + (ε : ℂ) * I).im := by simpa using hε
  have he := hillL2ContinuedPrimitive_conj _ hr ((x : ℂ) + (ε : ℂ) * I)
    (mem_hillL2ContinuationDomain_of_im_ne_zero q hq hr _ him.ne')
  simpa only [Function.comp_def, map_add, map_mul, conj_ofReal, conj_I, mul_neg, ← sub_eq_add_neg] using he.symm

theorem hillL2ContinuedPrimitive_closed_gap_vertical_jump
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1 ≤ n)
    (x : ℝ) (hx : x ∈ Icc (hillRealLabels q hq hr (2 * n - 1)) (hillRealLabels q hq hr (2 * n))) :
    Tendsto (fun ε : ℝ =>
      hillL2ContinuedPrimitive ((x : ℂ) + (ε : ℂ) * I, SpectralWeight.one.toCoeff q) -
        hillL2ContinuedPrimitive ((x : ℂ) - (ε : ℂ) * I, SpectralWeight.one.toCoeff q))
      (𝓝[>] 0) (𝓝 (2 * (hillRealGapProfile (SpectralWeight.one.toCoeff q) n x : ℂ))) := by
  have hu := (tendsto_hillL2ContinuedPrimitive_gap_upper q hq hr n hn x hx).comp
    (tendsto_real_upper_vertical x)
  have hl := tendsto_hillL2ContinuedPrimitive_gap_lower_vertical q hq hr n hn x hx
  dsimp only [Function.comp_def] at hu
  have he : ((hillRealGapProfile (SpectralWeight.one.toCoeff q) n x : ℂ) - I * (n : ℂ) * Real.pi) -
      (-(hillRealGapProfile (SpectralWeight.one.toCoeff q) n x : ℂ) - I * (n : ℂ) * Real.pi) =
        2 * (hillRealGapProfile (SpectralWeight.one.toCoeff q) n x : ℂ) := by ring
  simpa only [he] using hu.sub hl

end NLS.KdV
