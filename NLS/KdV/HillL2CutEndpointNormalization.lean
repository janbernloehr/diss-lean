import NLS.KdV.HillL2CutRealPhase
import NLS.KdV.HillL2CutPrimitiveEndpointValues
import NLS.KdV.HillRealTraceParity

/-! # Exact indexed limits of the actual high Hill cut primitive

The adjacent real-band phase intervals and the actual trace parity
select the finite endpoint limits. Both endpoints have value `-i*n*pi`
for every approach in the full local cut complement. The cutoff remains
the quantitative `8*||q||_2`; no continuity of chosen endpoint charts in
the potential or lower bound on an open gap is imposed.
-/

noncomputable section
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
namespace NLS.KdV

theorem HillRealHighGapPair.trace_parity
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hreal : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (n : ℕ) (hn : 2 ≤ n) (hcut : 8*‖q‖ ≤ (n : ℝ))
    (p : HillRealHighGapPair (SpectralWeight.one.toCoeff q) n) :
    hillL2Discriminant (SpectralWeight.one.toCoeff q) p.left = 2*(-1 : ℂ)^n ∧
    hillL2Discriminant (SpectralWeight.one.toCoeff q) p.right = 2*(-1 : ℂ)^n := by
  obtain ⟨p',hl,hr⟩ := hillRealLabels_high_pair q hq hreal n hn hcut
  have hu := p.endpoints_unique _ n (by omega) p'
  have ht := hillRealLabels_pair_trace q hq hreal n (by omega)
  simpa only [hl,hr,← hu.1,← hu.2] using ht

theorem HillL2NormalizedCutPrimitive.endpoint_normalization
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hreal : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (n : ℕ) (hn : 2 ≤ n) (hcut : 8*‖q‖ ≤ (n : ℝ))
    (p : HillRealHighGapPair (SpectralWeight.one.toCoeff q) n) (hopen : p.left ≠ p.right)
    (R F : ℂ → ℂ)
    (h : HillL2NormalizedCutPrimitive (SpectralWeight.one.toCoeff q) n p R F) :
    Tendsto F (𝓝[ball (freeHillValue n : ℂ) (7*(n : ℝ)/8) \ segment ℝ (p.left : ℂ) p.right] p.left)
      (𝓝 (-I*(n : ℂ)*Real.pi)) ∧
    Tendsto F (𝓝[ball (freeHillValue n : ℂ) (7*(n : ℝ)/8) \ segment ℝ (p.left : ℂ) p.right] p.right)
      (𝓝 (-I*(n : ℂ)*Real.pi)) := by
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  obtain ⟨A,B,hA,hB,heA,heB,_⟩ := h.endpoint_values q hq n hn1 hcut p hopen R F
  have hparity := p.trace_parity q hq hreal n hn hcut
  have hphase := h.real_band_phases q hq hreal n hn1 hcut p R F
  have hmem := p.real_band_domain q hq n hn1 hcut
  have hloc := p.localization q hq n hn1 hcut
  have hl := abs_le.mp hloc.1
  have hr := abs_le.mp hloc.2
  let U := ball (freeHillValue n : ℂ) (7*(n : ℝ)/8) \ segment ℝ (p.left : ℂ) p.right
  let L := Ioo (freeHillValue n-7*(n : ℝ)/8) p.left
  let V := Ioo p.right (freeHillValue n+7*(n : ℝ)/8)
  have hlenL : freeHillValue n-7*(n : ℝ)/8 < p.left := by linarith
  have hlenV : p.right < freeHillValue n+7*(n : ℝ)/8 := by linarith
  have : NeBot (𝓝[L] p.left) := right_nhdsWithin_Ioo_neBot hlenL
  have : NeBot (𝓝[V] p.right) := left_nhdsWithin_Ioo_neBot hlenV
  have hmapL : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[L] p.left) (𝓝[U] (p.left : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds,?_⟩
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact hmem.1 x hx
  have hmapV : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[V] p.right) (𝓝[U] (p.right : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds,?_⟩
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact hmem.2 x hx
  have hAL : A.im ∈ Icc (-Real.pi*n) (-Real.pi*((n : ℝ)-1)) := by
    apply isClosed_Icc.mem_of_tendsto ((continuous_im.tendsto A).comp (hA.comp hmapL))
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact ⟨(hphase.1 x hx).1.le,(hphase.1 x hx).2.le⟩
  have hBV : B.im ∈ Icc (-Real.pi*((n : ℝ)+1)) (-Real.pi*n) := by
    apply isClosed_Icc.mem_of_tendsto ((continuous_im.tendsto B).comp (hB.comp hmapV))
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact ⟨(hphase.2 x hx).1.le,(hphase.2 x hx).2.le⟩
  have hzim : (-I*(n : ℂ)*Real.pi).im = -Real.pi*n := by
    simp only [mul_im,mul_re,neg_re,I_re,neg_zero,neg_im,I_im,natCast_re,
      natCast_im,ofReal_re,ofReal_im,mul_zero,zero_mul,sub_zero,zero_add,neg_one_mul]
    ring
  have hAE : exp A = exp (-I*(n : ℂ)*Real.pi) := by
    rw [heA,hparity.1,exp_neg_I_nat_pi]
    ring
  have hBE : exp B = exp (-I*(n : ℂ)*Real.pi) := by
    rw [heB,hparity.2,exp_neg_I_nat_pi]
    ring
  have hAn : A = -I*(n : ℂ)*Real.pi :=
    eq_of_exp_eq_of_abs_im_sub_le_pi A _ hAE (by
      rw [hzim,abs_le]
      constructor <;> linarith [hAL.1,hAL.2])
  have hBn : B = -I*(n : ℂ)*Real.pi :=
    eq_of_exp_eq_of_abs_im_sub_le_pi B _ hBE (by
      rw [hzim,abs_le]
      constructor <;> linarith [hBV.1,hBV.2])
  exact ⟨hAn ▸ hA,hBn ▸ hB⟩

/-- The source's shifted nth primitive has zero limit at both ends of
an open high gap, from the entire local cut complement. -/
theorem HillL2NormalizedCutPrimitive.shifted_endpoint_normalization
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hreal : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (n : ℕ) (hn : 2 ≤ n) (hcut : 8*‖q‖ ≤ (n : ℝ))
    (p : HillRealHighGapPair (SpectralWeight.one.toCoeff q) n) (hopen : p.left ≠ p.right)
    (R F : ℂ → ℂ)
    (h : HillL2NormalizedCutPrimitive (SpectralWeight.one.toCoeff q) n p R F) :
    Tendsto (fun z => F z+I*(n : ℂ)*Real.pi)
      (𝓝[ball (freeHillValue n : ℂ) (7*(n : ℝ)/8) \ segment ℝ (p.left : ℂ) p.right] p.left) (𝓝 0) ∧
    Tendsto (fun z => F z+I*(n : ℂ)*Real.pi)
      (𝓝[ball (freeHillValue n : ℂ) (7*(n : ℝ)/8) \ segment ℝ (p.left : ℂ) p.right] p.right) (𝓝 0) := by
  have ht := h.endpoint_normalization q hq hreal n hn hcut p hopen R F
  have he : -I*(n : ℂ)*Real.pi+I*(n : ℂ)*Real.pi = 0 := by ring
  exact ⟨by simpa only [he] using ht.1.add_const (I*(n : ℂ)*Real.pi),
    by simpa only [he] using ht.2.add_const (I*(n : ℂ)*Real.pi)⟩

end NLS.KdV
