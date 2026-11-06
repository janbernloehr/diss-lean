import NLS.Articles.KdVPseudomeasures.SourceLemma216
import NLS.Articles.KdVPseudomeasures.SpectralWeightedGaps
import NLS.KdV.PseudomeasureSharpTailGaps

/-! The exact Fourier-tail estimate for the actual lexicographic complex
gaps in Lemma 2.12, uniformly over the original spectral weight class. -/
noncomputable section
open NLS.KdV NLS.WeightedCoeff
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures

theorem source_weighted_gap_tail_point (w : SpectralWeight) (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤) (N₀ N : ℕ)
    (hN₀ : 2≤N₀) (hN : N₀≤N)
    (hlabel : SourceHillComplexLabeling r hr (sourceForgetWeight w r q) N₀
      (sourceHillComplexLabels r hr (sourceForgetWeight w r q)))
    (hsmall : ∀ n : ℕ, N₀≤n → 13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖≤1/2)
    (k : ℤ) (hk : N≤k.natAbs) :
    w.negativeSobolev r k*‖sourceWeightedCanonicalGapValues w r hr q k‖≤
      4*‖fourierTail (w.negativeSobolev r) N (sourceWeightedEndpointCoefficients w r q)‖+
        16*sourceCoefficientConstant r/(N:ℝ)^(1/2-r)*‖q‖^2 := by
  have hkn : N₀≤k.natAbs := hN.trans hk
  have hkn2 : 2≤k.natAbs := hN₀.trans hkn
  have hk0 : k≠0 := by intro h; simp only [h,Int.natAbs_zero] at hkn2; omega
  obtain ⟨p,hl,hrr⟩ := hlabel.high_pair k.natAbs hkn
  have hg := EndpointHillComplexPair.sharp_tail_gap_le w r hr.1 hr.2 N k.natAbs hkn2 hk
    (sourceWeightedEndpointCoefficients w r q)
    (by simpa only [norm_sourceWeightedEndpointCoefficients] using hsmall k.natAbs hkn)
  rw [← sourceEndpointCoefficients_forgetWeight w r q] at hg
  have hp := hg p
  rw [norm_sourceWeightedEndpointCoefficients] at hp
  have hW : w.negativeSobolev r k=w.negativeSobolev r (k.natAbs:ℤ) := by
    simp only [Int.natCast_natAbs,SpectralWeight.negativeSobolev_apply,SpectralWeight.apply_abs,
      Weight.sobolev_apply,Int.cast_abs,abs_abs]
  rw [sourceWeightedCanonicalGapValues,sourceComplexCanonicalGapValues,if_neg hk0,hl,hrr,hW]
  have hNp : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hnle : (N:ℝ)≤k.natAbs := by exact_mod_cast hk
  have hrate : (k.natAbs:ℝ)^(r-1/2)≤(N:ℝ)^(r-1/2) :=
    Real.rpow_le_rpow_of_nonpos hNp hnle (by have hh:=hr.2; linarith)
  have hC : 0≤sourceCoefficientConstant r := by linarith [sourceCoefficientConstant_one_le r hr.2]
  have hquadratic : 8*sourceCoefficientConstant r*(k.natAbs:ℝ)^(r-1/2)*‖q‖^2≤
      16*sourceCoefficientConstant r/(N:ℝ)^(1/2-r)*‖q‖^2 := by
    have he : (N:ℝ)^(r-1/2)=((N:ℝ)^(1/2-r))⁻¹ := by
      rw [← Real.rpow_neg hNp.le]
      congr 1
      ring
    calc
      _ ≤ 8*sourceCoefficientConstant r*(N:ℝ)^(r-1/2)*‖q‖^2 := by gcongr
      _ ≤ 16*sourceCoefficientConstant r*(N:ℝ)^(r-1/2)*‖q‖^2 := by
        have hnonneg : 0≤sourceCoefficientConstant r*(N:ℝ)^(r-1/2)*‖q‖^2 := by positivity
        nlinarith
      _ = _ := by rw [he]; ring
  exact hp.trans (by simpa only [sourceCoefficientConstant] using add_le_add_right hquadratic _)

/-- Full source Lemma 2.12, with one cutoff before all source weights and
potentials in a norm ball. Every larger tail cutoff retains the literal
constants 4 and 16*c_s, and the boundary |k|=N is included. -/
theorem sourceLemma2_12 (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ) :
    ∃ N₀ : ℕ, 2≤N₀ ∧ ∀ (w : SpectralWeight)
      (q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤), ‖q‖≤R →
      ∀ N : ℕ, N₀≤N →
        ‖fourierTail (w.negativeSobolev r) N (sourceWeightedCanonicalGaps w r hr q)‖≤
          4*‖fourierTail (w.negativeSobolev r) N (sourceWeightedEndpointCoefficients w r q)‖+
            16*sourceCoefficientConstant r/(N:ℝ)^(1/2-r)*‖q‖^2 := by
  obtain ⟨N₀,hN₀,hcut,hlabel⟩ := source_uniform_canonical_complex_labels_with_contraction r hr R
  refine ⟨N₀,hN₀,?_⟩
  intro w q hq N hN
  have hl := hlabel (sourceForgetWeight w r q) ((norm_sourceForgetWeight_le w r q).trans hq)
  have hs (n : ℕ) (hn : N₀≤n) : 13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖≤1/2 :=
    (mul_le_mul_of_nonneg_left hq (by positivity [endpointHillConstant_pos r hr.2])).trans (hcut n hn)
  have hC : 0≤sourceCoefficientConstant r := by linarith [sourceCoefficientConstant_one_le r hr.2]
  have hB : 0≤4*‖fourierTail (w.negativeSobolev r) N (sourceWeightedEndpointCoefficients w r q)‖+
      16*sourceCoefficientConstant r/(N:ℝ)^(1/2-r)*‖q‖^2 := by positivity
  change ‖weightEquiv (w.negativeSobolev r) ⊤ _‖≤_
  apply lp.norm_le_of_forall_le hB
  intro k
  rw [weightEquiv_apply,fourierTail_apply,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos ((w.negativeSobolev r).positive k)]
  split_ifs with hk
  · exact source_weighted_gap_tail_point w r hr q N₀ N hN₀ hN hl hs k hk
  · simpa only [norm_zero,mul_zero] using hB

end NLS.Articles.KdVPseudomeasures
