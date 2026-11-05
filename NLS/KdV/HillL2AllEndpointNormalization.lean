import NLS.KdV.HillL2BoundaryLabelContinuity
import NLS.KdV.HillCanonicalFreeLabels
import Mathlib.Analysis.Complex.SqrtDeriv

/-! # Exact source normalization at every real Hill endpoint

Continuity at moving characteristic labels retains the logarithm period
along the real scaling path from zero potential. The free square root
therefore fixes every endpoint value, including the lowest endpoint,
low gaps and collisions, with no spectral cutoff.
-/

noncomputable section
open Set Metric Complex Filter Topology
namespace NLS.KdV
open NLS.ComplexAnalysis

theorem hillL2UpperBoundaryPrimitive_zero_free (n : ℕ) :
    hillL2UpperBoundaryPrimitive 0 (freeHillValue n) = -I * (n : ℂ) * Real.pi := by
  have hval : freeHillValue n = ((n : ℝ) * Real.pi) ^ 2 := by
    simp only [freeHillValue, Int.cast_natCast]
    ring
  have hnonneg : 0 ≤ freeHillValue n := by rw [hval]; positivity
  have hsqrt : Complex.sqrt (freeHillValue n : ℂ) = (n : ℂ) * Real.pi := by
    rw [Complex.sqrt_of_nonneg (by exact_mod_cast hnonneg), ofReal_re, hval,
      Real.sqrt_sq (by positivity : 0 ≤ (n : ℝ) * Real.pi), ofReal_mul, ofReal_natCast]
  have ht : Tendsto (fun z : ℂ => -I * Complex.sqrt z)
      (𝓝[{z : ℂ | 0 < z.im}] (freeHillValue n : ℂ))
      (𝓝 (-I * (n : ℂ) * Real.pi)) := by
    have hc : ContinuousAt (fun z : ℂ => -I * Complex.sqrt z) (freeHillValue n : ℂ) :=
      (Complex.continuousAt_sqrt (Or.inl (by simpa only [ofReal_re] using hnonneg))).const_mul (-I)
    simpa only [hsqrt, mul_assoc] using hc.tendsto.mono_left nhdsWithin_le_nhds
  let := real_upper_nhds_neBot (freeHillValue n)
  simpa only [hillL2UpperBoundaryPrimitive, hillL2ContinuedPrimitive_base] using ht.limUnder_eq

theorem hillL2UpperBoundaryPrimitive_label_indexed
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (j : ℕ) :
    hillL2UpperBoundaryPrimitive (SpectralWeight.one.toCoeff q) (hillRealLabels q hq hr j) =
      -I * (((j + 1) / 2 : ℕ) : ℂ) * Real.pi := by
  let Q : Icc (0 : ℝ) 1 → WeightedCoeff SpectralWeight.one.toWeight 2 := fun t => (t.val : ℂ) • q
  have hQ : Continuous Q := (Complex.continuous_ofReal.comp continuous_subtype_val).smul continuous_const
  have hqp (t : Icc (0 : ℝ) 1) : SpectralWeight.one.toCoeff (Q t) ∈ Coeff.paritySubspace 0 := by
    rw [map_smul]
    exact (Coeff.paritySubspace 0).smul_mem _ hq
  have hQr (t : Icc (0 : ℝ) 1) : IsRealHillPotential (SpectralWeight.one.toCoeff (Q t)) := by
    rw [map_smul]
    exact hr.smul_real t.val
  let B : Icc (0 : ℝ) 1 → ℂ := fun t =>
    hillL2UpperBoundaryPrimitive (SpectralWeight.one.toCoeff (Q t))
      (hillRealLabels (Q t) (hqp t) (hQr t) j)
  have hB : Continuous B := continuous_hillL2UpperBoundaryPrimitive_label_family Q hQ hqp hQr j
  have he (t : Icc (0 : ℝ) 1) : exp (B t) = (-1 : ℂ) ^ ((j + 1) / 2) := by
    have hz := (hillRealLabels_spec (Q t) (hqp t) (hQr t)).root j
    have ht := hillL2UpperBoundaryPrimitive_exp_at_zero (Q t) (hqp t) (hQr t) _ hz
    rw [hillRealLabels_trace_parity] at ht
    simpa only [mul_div_cancel_left₀ _ (by norm_num : (2 : ℂ) ≠ 0)] using ht
  let t0 : Icc (0 : ℝ) 1 := ⟨0, by constructor <;> norm_num⟩
  let t1 : Icc (0 : ℝ) 1 := ⟨1, by constructor <;> norm_num⟩
  have hconstant := continuousLogarithms_eqOn B (fun _ => B t0) univ isPreconnected_univ
    hB.continuousOn continuousOn_const (fun t _ => (he t).trans (he t0).symm)
    t0 (mem_univ _) rfl
  have h01 : B t1 = B t0 := hconstant (mem_univ t1)
  have h0 : B t0 = -I * (((j + 1) / 2 : ℕ) : ℂ) * Real.pi := by
    simpa only [B, Q, t0, ofReal_zero, zero_smul, map_zero, hillRealLabels_zero] using
      hillL2UpperBoundaryPrimitive_zero_free ((j + 1) / 2)
  have h1 : B t1 = hillL2UpperBoundaryPrimitive (SpectralWeight.one.toCoeff q)
      (hillRealLabels q hq hr j) := by simp only [B, Q, t1, ofReal_one, one_smul]
  exact h1.symm.trans (h01.trans h0)

theorem hillL2UpperBoundaryPrimitive_pair_indexed
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1 ≤ n) :
    hillL2UpperBoundaryPrimitive (SpectralWeight.one.toCoeff q) (hillRealLabels q hq hr (2 * n - 1)) =
        -I * (n : ℂ) * Real.pi ∧
      hillL2UpperBoundaryPrimitive (SpectralWeight.one.toCoeff q) (hillRealLabels q hq hr (2 * n)) =
        -I * (n : ℂ) * Real.pi := by
  constructor
  · simpa only [show (2 * n - 1 + 1) / 2 = n by omega] using
      hillL2UpperBoundaryPrimitive_label_indexed q hq hr (2 * n - 1)
  · simpa only [show (2 * n + 1) / 2 = n by omega] using
      hillL2UpperBoundaryPrimitive_label_indexed q hq hr (2 * n)

end NLS.KdV
