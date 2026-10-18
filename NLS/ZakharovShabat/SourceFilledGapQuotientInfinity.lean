import NLS.ZakharovShabat.SourceFilledGapQuotient
import NLS.ZakharovShabat.StandardRootInfinity
import NLS.ZakharovShabat.SourceFullAbelianFiniteGapInversion

/-! # Finite-gap normalization of the filled quotient

The actual finite-gap primitive has leading coefficient -i at complex
infinity. Together with the standard-root asymptotic, this proves that
the analytically filled quotient tends to one.
-/

noncomputable section
open Set Metric Filter Topology Complex
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
variable (C : SourceFullAbelianUniformCauchyFamily hp hp1 W)

/-- The actual finite-gap primitive has leading coefficient minus i in every complex direction. -/
theorem primitive_div_tendsto_finiteGap (n : ℤ) (φ : realTypeSourceSubmodule p)
    (hφ : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius)
    (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    Tendsto (fun z : ℂ => sourceFullAbelianPrimitive hp hp1 W n (z,φ.val)/z)
      (Bornology.cobounded ℂ) (𝓝 (-I)) := by
  obtain ⟨R,hR,r,hr,_,A,hA,hA0,hval⟩ :=
    exists_sourceFullAbelian_finiteGap_inversion_remainder_all_indices C φ hφ hf
  have hi := tendsto_inv₀_cobounded (α := ℂ)
  have hAlim : Tendsto (fun z : ℂ => A z⁻¹) (Bornology.cobounded ℂ) (𝓝 0) := by
    simpa only [hA0,Function.comp_def] using (hA 0 (mem_ball_self hr)).continuousAt.tendsto.comp hi
  have hlim : Tendsto (fun z : ℂ => -I+(I*(Real.pi:ℂ)*n)*z⁻¹+A z⁻¹*z⁻¹)
      (Bornology.cobounded ℂ) (𝓝 (-I)) := by
    simpa only [mul_zero,add_zero] using
      ((tendsto_const_nhds (x := -I)).add (hi.const_mul (I*(Real.pi:ℂ)*n))).add (hAlim.mul hi)
  apply hlim.congr'
  filter_upwards [tendsto_norm_cobounded_atTop.eventually (eventually_gt_atTop R)] with z hz
  have hz0 : z ≠ 0 := norm_pos_iff.mp (hR.trans hz)
  rw [hval n z hz]
  field_simp

/-- Filling the selected gap preserves the normalized limit one at infinity. -/
theorem filledGapQuotient_tendsto_one_finiteGap (n : ℤ) (φ : realTypeSourceSubmodule p)
    (hφ : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius)
    (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    Tendsto (C.filledGapQuotient n φ.val) (Bornology.cobounded ℂ) (𝓝 1) := by
  have hroot : Tendsto (fun z : ℂ => sourceStandardRoot hp hp1 φ.val n z/z)
      (Bornology.cobounded ℂ) (𝓝 (-1)) := normalizedStandardRoot_div_tendsto _ _
  have hlim := (tendsto_const_nhds (x := -I)).mul
    ((C.primitive_div_tendsto_finiteGap n φ hφ hf).div hroot (by norm_num))
  norm_num at hlim
  apply hlim.congr'
  filter_upwards [tendsto_norm_cobounded_atTop.eventually
    (eventually_gt_atTop (max (‖C.discs.center n‖+C.discs.outer n) 0))] with z hz
  have hz0 : z ≠ 0 := norm_pos_iff.mp ((le_max_right _ _).trans_lt hz)
  have hb : z ∉ ball (C.discs.center n) (C.discs.outer n) := by
    intro hb
    have hdist := mem_ball.mp hb
    have hnorm : ‖z‖ ≤ dist z (C.discs.center n)+‖C.discs.center n‖ := by
      simpa only [dist_zero_right] using dist_triangle z (C.discs.center n) 0
    have hlarge := (le_max_left (‖C.discs.center n‖+C.discs.outer n) 0).trans_lt hz
    linarith
  simp only [filledGapQuotient,if_neg hb,div_div_div_cancel_right₀ hz0,neg_mul]

end NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily
