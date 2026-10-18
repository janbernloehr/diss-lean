import NLS.ZakharovShabat.NormalizedWeightedSourceTopology
import NLS.ZakharovShabat.SourceWeightedGapSequence
import NLS.ZakharovShabat.SourceCriticalGapQuotientUniform
import NLS.ZakharovShabat.SourceNormalizedActionSequenceMajorants

/-! # Complex Sobolev critical-offset majorants

The actual critical offset has a locally bounded weighted Hilbert majorant, using the exact squared-gap identity even at collapsed complex gaps.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Complex first-order Sobolev neighborhoods carry weighted majorants of both gaps and actual critical offsets. -/
theorem exists_local_normalizedSobolevCriticalOffset_majorants (φ : realTypeSourceLocus 2) :
    ∃ U : Set (CoeffPair 2), IsOpen U ∧ φ.val ∈ U ∧
      ∃ M : ℝ, 0 ≤ M ∧ ∀ ψ ∈ U, ∃ G A : Coeff 2,
        (∀ n : ℤ, (1+|(n:ℝ)|)*‖sourcePeriodicGapDisplacement (by simp) (by norm_num)
          (normalizedWeightedSource (SpectralWeight.sobolev 1 (by norm_num)) ψ) n‖ ≤ ‖G n‖) ∧
        (∀ n : ℤ, (1+|(n:ℝ)|)*‖sourceCriticalMidpointOffsetAtExponent (by simp) (by norm_num)
          (q := 2) (by norm_num) (normalizedWeightedSource (SpectralWeight.sobolev 1 (by norm_num)) ψ) n‖ ≤ ‖A n‖) ∧
        ‖G‖ ≤ M ∧ ‖A‖ ≤ M ∧
        (∀ n : ℤ, canonicalCriticalPoints (by simp) (by norm_num)
            (periodOnePotential (normalizedWeightedSource (SpectralWeight.sobolev 1 (by norm_num)) ψ))
            (periodOnePotential_mem _) n-
          canonicalPeriodicMidpoint (by simp) (by norm_num)
            (periodOnePotential (normalizedWeightedSource (SpectralWeight.sobolev 1 (by norm_num)) ψ))
            (periodOnePotential_mem _) n =
          sourceCriticalMidpointOffsetAtExponent (by simp) (by norm_num) (q := 2) (by norm_num)
            (normalizedWeightedSource (SpectralWeight.sobolev 1 (by norm_num)) ψ) n) := by
  let w := SpectralWeight.sobolev 1 (by norm_num)
  let L := normalizedWeightedSourceCLM (p := 2) w
  let S := (normalizedWeightedPeriodOne (p := 2) w).toContinuousLinearMap
  have hSL : ∀ b, weightedBaseToPair w (S b) = periodOnePotential (L b) :=
    fun b => weightedBaseToPair_normalizedWeightedPeriodOne w b
  obtain ⟨Vg,hVg,hφg,R,hR,hgap⟩ := exists_local_sourceWeightedGapSequence_bound (by simp) (by norm_num) w L S hSL φ.val
  obtain ⟨Vq,hVq,hφq,B,hB,hquot⟩ := exists_local_uniform_sourceCriticalGapQuotient (by simp) (by norm_num)
    (L φ.val) (normalizedWeightedSource_realType w φ.val φ.property)
  let U := Vg ∩ L ⁻¹' Vq
  have hU : IsOpen U := hVg.inter (hVq.preimage L.continuous)
  refine ⟨U,hU,⟨hφg,hφq⟩,R+B*R^2,by positivity,?_⟩
  intro ψ hψ
  let G := sourceWeightedGapSequence (by simp) (by norm_num) w L S hSL ψ
  let A : Coeff 2 := ((B*R:ℝ):ℂ) • Coeff.magnitude G
  have hGn : ‖G‖ ≤ R := hgap ψ hψ.1
  have hG (n : ℤ) : (1+|(n:ℝ)|)*‖sourcePeriodicGapDisplacement (by simp) (by norm_num) (L ψ) n‖ ≤ ‖G n‖ := by
    change _ ≤ ‖(w (2*n):ℂ)*sourcePeriodicGapDisplacement (by simp) (by norm_num) (L ψ) n‖
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (w.positive _).le]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    simp only [w,SpectralWeight.sobolev_apply,Weight.sobolev_apply,Real.rpow_one,
      Int.cast_mul,Int.cast_ofNat,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    linarith [abs_nonneg (n:ℝ)]
  have hA (n : ℤ) : (1+|(n:ℝ)|)*‖sourceCriticalMidpointOffsetAtExponent (by simp) (by norm_num)
      (q := 2) (by norm_num) (L ψ) n‖ ≤ ‖A n‖ := by
    have hg : ‖sourcePeriodicGapDisplacement (by simp) (by norm_num) (L ψ) n‖ ≤ R := by
      have hn := (hG n).trans ((lp.norm_apply_le_norm (by norm_num : (2:ℝ≥0∞) ≠ 0) G n).trans hGn)
      nlinarith [abs_nonneg (n:ℝ),norm_nonneg (sourcePeriodicGapDisplacement (by simp) (by norm_num) (L ψ) n)]
    have hq : ‖sourceCriticalGapQuotient (by simp) (by norm_num) (L ψ) n‖ ≤ B :=
      (lp.norm_apply_le_norm (by norm_num : (2:ℝ≥0∞) ≠ 0) _ n).trans (hquot _ hψ.2).1
    have hAc : ‖A n‖ = (B*R)*‖G n‖ := by
      simp only [A,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,norm_mul,Coeff.magnitude_apply,
        Complex.norm_real,Real.norm_of_nonneg (mul_nonneg hB hR),Real.norm_of_nonneg (norm_nonneg _)]
    rw [sourceCriticalMidpointOffsetAtExponent_apply,norm_mul,norm_pow,hAc]
    calc
      _ = ((1+|(n:ℝ)|)*‖sourcePeriodicGapDisplacement (by simp) (by norm_num) (L ψ) n‖)*
          (‖sourcePeriodicGapDisplacement (by simp) (by norm_num) (L ψ) n‖*
            ‖sourceCriticalGapQuotient (by simp) (by norm_num) (L ψ) n‖) := by ring
      _ ≤ ‖G n‖*(R*B) := mul_le_mul (hG n) (mul_le_mul hg hq (norm_nonneg _) hR)
        (by positivity) (norm_nonneg _)
      _ = _ := by ring
  have hAn : ‖A‖ ≤ B*R^2 := by
    rw [show ‖A‖ = ‖((B*R:ℝ):ℂ)‖*‖Coeff.magnitude G‖ from norm_smul _ _,
      Complex.norm_real,Real.norm_of_nonneg (mul_nonneg hB hR),Coeff.norm_magnitude]
    exact (mul_le_mul_of_nonneg_left hGn (mul_nonneg hB hR)).trans_eq (by ring)
  refine ⟨G,A,hG,hA,hGn.trans (le_add_of_nonneg_right (by positivity)),
    hAn.trans (le_add_of_nonneg_left hR),?_⟩
  intro n
  simpa only [sourceCriticalMidpointOffsetAtExponent_apply,L,w,normalizedWeightedSourceCLM_apply]
    using! (hquot _ hψ.2).2 n

end NLS.ZakharovShabat
