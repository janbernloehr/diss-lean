import NLS.Articles.KdVPseudomeasures.SourceSharpResonantRows

/-! The precise logarithmic/power transition in the source epsilon_s.
The constant is chosen before every weight, input and spectral parameter. -/
noncomputable section
open NLS.KdV NLS.ReciprocalSeries
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures

def sourcePredualEpsilon (r : ℝ) (n : ℕ) : ℝ :=
  if r=0 then Real.log (1+(n:ℝ))/(n:ℝ) else 1/(n:ℝ)^(1-r)

theorem sourcePredualEpsilon_nonneg (r : ℝ) (n : ℕ) (hn : 1≤n) :
    0≤sourcePredualEpsilon r n := by
  have hnR : (1:ℝ)≤n := by exact_mod_cast hn
  unfold sourcePredualEpsilon
  split_ifs
  · exact div_nonneg (Real.log_nonneg (by linarith)) (by positivity)
  · positivity

theorem source_scaled_reciprocal_bound (r : ℝ) (hr : 0≤r) (hr1 : r<1/2) :
    ∃ C : ℝ, 0<C ∧ ∀ n : ℕ, 2≤n →
      ((2:ℝ)^(2*r)*(n:ℝ)^(-r))*(∑' k : ℤ, quadraticPowerKernel (1-r) n k) ≤
        C*sourcePredualEpsilon r n := by
  by_cases hzero : r=0
  · subst r
    obtain ⟨C,hC,h⟩ := sourceLemmaA_1_harmonic
    refine ⟨C,hC,?_⟩
    intro n hn
    simpa [sourcePredualEpsilon,mul_div_assoc] using (h n (by omega)).2
  · have hrp : 0<r := lt_of_le_of_ne hr (Ne.symm hzero)
    obtain ⟨C,hC,h⟩ := sourceLemmaA_1_subcritical (1-r) (by linarith) (by linarith)
    refine ⟨(2:ℝ)^(2*r)*C,by positivity,?_⟩
    intro n hn
    have hnp : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
    calc
      _ ≤ ((2:ℝ)^(2*r)*(n:ℝ)^(-r))*(C/(n:ℝ)^(2*(1-r)-1)) :=
        mul_le_mul_of_nonneg_left (h n (by omega)).2 (by positivity)
      _ = ((2:ℝ)^(2*r)*C)*sourcePredualEpsilon r n := by
        rw [sourcePredualEpsilon,if_neg hzero]
        have hden : ((n:ℝ)^(2*(1-r)-1))⁻¹=(n:ℝ)^(-(2*(1-r)-1)) := (Real.rpow_neg hnp.le _).symm
        have hden₂ : ((n:ℝ)^(1-r))⁻¹=(n:ℝ)^(-(1-r)) := (Real.rpow_neg hnp.le _).symm
        have he : (n:ℝ)^(-r)*(n:ℝ)^(-(2*(1-r)-1))=(n:ℝ)^(-(1-r)) := by
          rw [← Real.rpow_add hnp]
          congr 1
          ring
        rw [div_eq_mul_inv,one_div,hden,hden₂]
        calc
          _ = ((2:ℝ)^(2*r)*C)*((n:ℝ)^(-r)*(n:ℝ)^(-(2*(1-r)-1))) := by ring
          _ = _ := by rw [he]

theorem sourceLemma2_10_plus (r : ℝ) (hr : 0≤r) (hr1 : r<1/2) :
    ∃ C : ℝ, 1≤C ∧ 13*endpointHillConstant r≤C ∧
      ∀ (w : SpectralWeight) (q f : WeightedCoeff (w.negativeSobolev r) ⊤),
      ∀ (n : ℕ) (hn : 2≤n) (z : ℂ) (hz : z ∈ wideHillStrip n),
        w.negativeSobolev r (2*(n:ℤ))*
          ‖(wideEndpointHillPerturbation w r hr hr1 n hn z hz q f).val (n:ℤ)‖ ≤
            C*sourcePredualEpsilon r n*‖q‖*w.negativeShiftedNorm r hr (n:ℤ) ⊤ f := by
  obtain ⟨C₀,_,h₀⟩ := source_scaled_reciprocal_bound r hr hr1
  let C := max 1 (max (13*endpointHillConstant r) C₀)
  have hC : C₀≤C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨C,le_max_left _ _,(le_max_left _ _).trans (le_max_right _ _),?_⟩
  intro w q f n hn z hz
  have hb : ((2:ℝ)^(2*r)*(n:ℝ)^(-r))*(∑' k : ℤ, quadraticPowerKernel (1-r) n k) ≤
      C*sourcePredualEpsilon r n := (h₀ n hn).trans
    (mul_le_mul_of_nonneg_right hC (sourcePredualEpsilon_nonneg r n (by omega)))
  have hF : 0≤w.negativeShiftedNorm r hr (n:ℤ) ⊤ f := norm_nonneg _
  calc
    _ ≤ (((2:ℝ)^(2*r)*(n:ℝ)^(-r))*‖q‖*w.negativeShiftedNorm r hr (n:ℤ) ⊤ f)*
        (∑' k : ℤ, quadraticPowerKernel (1-r) n k) :=
      source_resonant_row_sum_bound w r hr hr1 n hn z hz q f
    _ = (((2:ℝ)^(2*r)*(n:ℝ)^(-r))*(∑' k : ℤ, quadraticPowerKernel (1-r) n k))*
        ‖q‖*w.negativeShiftedNorm r hr (n:ℤ) ⊤ f := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hb (norm_nonneg q)) hF

end NLS.Articles.KdVPseudomeasures
