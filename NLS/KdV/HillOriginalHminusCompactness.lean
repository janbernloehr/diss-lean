import NLS.KdV.HillHminusOriginalSource
import NLS.KdV.HillMeanZeroIsospectralCompactness

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.KdV

/-- Bounded ORIGINAL L2 Fourier sequences converging in every raw mode
converge strongly after the literal even-index inclusion in H-minus-one. -/
theorem tendsto_hillOriginalHminusSource_of_bounded_coefficientwise
    (a : ℕ → WeightedCoeff SpectralWeight.one.toWeight 2)
    (b : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hb : Bornology.IsBounded (range a))
    (ht : ∀ k : ℤ, Tendsto (fun j => (a j).val k) atTop (𝓝 (b.val k))) :
    Tendsto (fun j => hillOriginalHminusSource (a j)) atTop
      (𝓝 (hillOriginalHminusSource b)) := by
  obtain ⟨B,hB⟩ := hb.exists_norm_le
  let C : ℝ := max B 0 + ‖b‖
  have hC : 0 ≤ C := add_nonneg (le_max_right _ _) (norm_nonneg _)
  let T := WeightedCoeff.weightIsometry (Weight.sobolev (-1)) 2
  let f : ℕ → Coeff 2 := fun j => T (hillOriginalHminusSource (a j) - hillOriginalHminusSource b)
  have hf (j : ℕ) (k : ℤ) : f j k =
      (Weight.sobolev (-1) k : ℂ) * ((a j).val (2*k)-b.val (2*k)) := by
    change (Weight.sobolev (-1) k : ℂ) *
      ((hillOriginalHminusSource (a j)).val k-(hillOriginalHminusSource b).val k) = _
    rw [hillOriginalHminusSource_apply,hillOriginalHminusSource_apply]
  have hz : Tendsto f atTop (𝓝 (0 : Coeff 2)) := by
    apply Coeff.tendsto_zero_of_dominated (by simp) f ((C : ℂ) • inverseBracketCoefficients)
    · apply Eventually.of_forall
      intro j k
      have ha : ‖(a j).val (2*k)‖ ≤ max B 0 := by
        have he := lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
          (SpectralWeight.one.toCoeff (a j)) (2*k)
        simpa only [SpectralWeight.toCoeff_apply] using
          he.trans ((SpectralWeight.norm_toCoeff_le _ _).trans ((hB _ ⟨j,rfl⟩).trans (le_max_left B 0)))
      have hbb : ‖b.val (2*k)‖ ≤ ‖b‖ := by
        simpa only [SpectralWeight.toCoeff_apply] using
          (lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
            (SpectralWeight.one.toCoeff b) (2*k)).trans (SpectralWeight.norm_toCoeff_le _ _)
      rw [hf]
      change ‖(Weight.sobolev (-1) k : ℂ) * ((a j).val (2*k)-b.val (2*k))‖ ≤
        ‖(C : ℂ) * inverseBracketCoefficients k‖
      simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hC,
        norm_inverseBracketCoefficients_apply,
        Weight.sobolev_apply,Real.rpow_neg_one,abs_of_pos (by positivity : (0 : ℝ) < (1+|(k : ℝ)|)⁻¹)]
      calc
        _ ≤ (1+|(k : ℝ)|)⁻¹ * (max B 0 + ‖b‖) :=
          mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add ha hbb)) (by positivity)
        _ = C * (1+|(k : ℝ)|)⁻¹ := mul_comm _ _
    · intro k
      simpa only [hf,sub_self,mul_zero] using ((ht (2*k)).sub_const (b.val (2*k))).const_mul
        (Weight.sobolev (-1) k : ℂ)
  have h := T.symm.continuous.continuousAt.tendsto.comp hz
  have hd : Tendsto (fun j => hillOriginalHminusSource (a j)-hillOriginalHminusSource b)
      atTop (𝓝 0) := by
    simpa only [Function.comp_def,f,LinearIsometryEquiv.symm_apply_apply,map_zero] using h
  exact (tendsto_sub_nhds_zero_iff).mp hd

/-- Every bounded ORIGINAL real L2 sequence has an H-minus-one strongly
convergent subsequence with a limit in the SAME original real L2 space. -/
theorem exists_hillRealSource_hminus_tendsto_subseq
    (a : ℕ → RealPeriodOneHillPotential)
    (hb : Bornology.IsBounded (range (fun j => (a j).val))) :
    ∃ b : RealPeriodOneHillPotential, ∃ σ : ℕ → ℕ, StrictMono σ ∧
      Tendsto (fun j => hillOriginalHminusSource (a (σ j)).val) atTop
        (𝓝 (hillOriginalHminusSource b.val)) := by
  obtain ⟨b,σ,hσ,ht⟩ := exists_hillRealSource_coefficientwise_subseq a hb
  refine ⟨b,σ,hσ,tendsto_hillOriginalHminusSource_of_bounded_coefficientwise _ _ ?_ ht⟩
  exact hb.subset (by rintro _ ⟨j,rfl⟩; exact ⟨σ j,rfl⟩)

end NLS.KdV
