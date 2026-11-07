import NLS.Articles.KdVPseudomeasures.SourceThresholdNumerics
import NLS.KdV.PseudomeasureWideAnalyticCoefficients

/-! The literal ball and threshold estimates of Lemma 2.16. -/
noncomputable section
open NLS.KdV
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures

def sourceCoefficientConstant (r : ℝ) : ℝ := 13*endpointHillConstant r

theorem sourceCoefficientConstant_one_le (r : ℝ) (hr1 : r<1/2) :
    1≤sourceCoefficientConstant r := by
  unfold sourceCoefficientConstant endpointHillConstant
  have hd : 0<1-2*r := by linarith
  have h := div_nonneg (by norm_num : (0:ℝ)≤16) hd.le
  linarith

theorem source_wideDiagonal_error (r : ℝ) (hr : 0≤r) (hr1 : r<1/2)
    (n : ℕ) (hn : 2≤n) (z : ℂ) (hz : z ∈ wideHillStrip n)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
    (hs : 13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖≤1/2) :
    ‖endpointDiagonal r hr hr1 n (q,z)-q.val 0‖≤
      2*(sourceCoefficientConstant r*(n:ℝ)^(r-1/2)*‖q‖)*‖q‖ := by
  have h := wideEndpointHillCorrectedMode_coefficient_error SpectralWeight.one r hr hr1
    n hn z hz q hs n n (Or.inl rfl)
  rw [wideEndpointHillCorrectedMode_pos,sub_self] at h
  unfold endpointDiagonal
  rw [endpointEffectiveFamily_eq_wide r hr hr1 n hn (q,z) hz hs]
  simpa only [sourceCoefficientConstant,SpectralWeight.negativeSobolev_apply,SpectralWeight.one_apply,
    Weight.sobolev_apply,Int.cast_zero,abs_zero,add_zero,Real.one_rpow,div_one,one_mul] using h

theorem source_threshold35_small (r C m : ℝ) (hC : sourceCoefficientConstant r≤C) (hr1 : r<1/2)
    (hm : 1≤m) (n : ℕ) (hn : 2≤n)
    (h35 : 16*C*m/(n:ℝ)^(1/2-r)≤1/2)
    (Q : ℝ) (hQ : Q≤2*m) :
    sourceCoefficientConstant r*(n:ℝ)^(r-1/2)*Q≤1/16 := by
  have hscale := source_threshold35_bound r C m n (by omega) h35
  have hnR : 0≤(n:ℝ)^(r-1/2) := Real.rpow_nonneg (by positivity) _
  have hCpos : 0≤sourceCoefficientConstant r := by
    unfold sourceCoefficientConstant
    positivity [endpointHillConstant_pos r hr1]
  calc
    _ ≤ sourceCoefficientConstant r*(n:ℝ)^(r-1/2)*(2*m) :=
      mul_le_mul_of_nonneg_left hQ (mul_nonneg hCpos hnR)
    _ ≤ C*(n:ℝ)^(r-1/2)*(2*m) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC hnR) (by linarith)
    _ ≤ _ := by nlinarith

/-- The literal numerical bounds, with one constant before every ball,
weight, potential and spectral parameter. -/
def SourceLemma216Bounds (r : ℝ) (hr : 0≤r) (hr1 : r<1/2) (C : ℝ) : Prop :=
  ∀ (m : ℝ), 1≤m → ∀ (n : ℕ) (_hn : 2≤n),
      16*C*m/(n:ℝ)^(1/2-r)≤1/2 →
      ∀ (w : SpectralWeight) (q : WeightedCoeff (w.negativeSobolev r) ⊤),
      ‖q‖≤2*m → q.val 0=0 → ∀ (z : ℂ), z ∈ wideHillStrip n →
        (‖endpointDiagonal r hr hr1 n (endpointForgetWeight w r q,z)‖≤
          8*sourceCoefficientConstant r*m^2/(n:ℝ)^(1/2-r)) ∧
        (8*sourceCoefficientConstant r*m^2/(n:ℝ)^(1/2-r)≤m/4) ∧
        (w.negativeSobolev r (2*(n:ℤ))*
          ‖endpointUpperCoupling r hr hr1 n (endpointForgetWeight w r q,z)-q.val (2*(n:ℤ))‖≤
          Real.log (1+(n:ℝ))/(n:ℝ)^(1-r)*(8*C*m^2)) ∧
        (w.negativeSobolev r (2*(n:ℤ))*
          ‖endpointLowerCoupling r hr hr1 n (endpointForgetWeight w r q,z)-q.val (-(2*(n:ℤ)))‖≤
          Real.log (1+(n:ℝ))/(n:ℝ)^(1-r)*(8*C*m^2)) ∧
        (Real.log (1+(n:ℝ))/(n:ℝ)^(1-r)*(8*C*m^2)≤
          Real.log (1+(n:ℝ))/(n:ℝ)^((1:ℝ)/2)*(m/4))

/-- Uniform pointwise bounds on the entire printed strip. The only
numerical threshold is precisely (35), with c'_s chosen before m,w,q,n,z. -/
theorem sourceLemma2_16_bounds (r : ℝ) (hr : 0≤r) (hr1 : r<1/2) :
    ∃ C : ℝ, 1≤C ∧ sourceCoefficientConstant r≤C ∧
      SourceLemma216Bounds r hr hr1 C := by
  obtain ⟨C,hC,hCwide,hsharp⟩ := source_wideCoupling_errors_sharp r hr hr1
  refine ⟨C,hC,hCwide,?_⟩
  intro m hm n hn h35 w q hq hq0 z hz
  have hsmall : 13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖≤1/2 :=
    (source_threshold35_small r C m hCwide hr1 hm n hn h35 ‖q‖ hq).trans (by norm_num)
  have hq1 : ‖endpointForgetWeight w r q‖≤2*m := (norm_endpointForgetWeight_le w r q).trans hq
  have hsmall1 : 13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖endpointForgetWeight w r q‖≤1/2 :=
    (source_threshold35_small r C m hCwide hr1 hm n hn h35 _ hq1).trans (by norm_num)
  have hnR : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have he : (n:ℝ)^(r-1/2)=((n:ℝ)^(1/2-r))⁻¹ := by
    rw [← Real.rpow_neg hnR.le]
    congr 1
    ring
  have hcpos : 0≤sourceCoefficientConstant r := (sourceCoefficientConstant_one_le r hr1).trans' (by norm_num)
  have hsq : ‖q‖^2≤4*m^2 := by nlinarith [norm_nonneg q]
  have hsqu : ‖endpointForgetWeight w r q‖^2≤4*m^2 := by nlinarith [norm_nonneg (endpointForgetWeight w r q)]
  have hscale := source_threshold35_bound r C m n (by omega) h35
  have hcs : sourceCoefficientConstant r*(n:ℝ)^(r-1/2)*m≤1/32 :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCwide (by positivity)) (by linarith)).trans hscale
  have hbdiag : 8*sourceCoefficientConstant r*m^2/(n:ℝ)^(1/2-r)≤m/4 := by
    rw [div_eq_mul_inv,← he]
    nlinarith [mul_le_mul_of_nonneg_right hcs (by linarith : (0:ℝ)≤m)]
  have hbsharp := hsharp w q n hn z hz hsmall
  have hlognonneg : 0≤Real.log (1+(n:ℝ))/(n:ℝ)^(1-r) := by
    exact div_nonneg (Real.log_nonneg (by linarith)) (Real.rpow_nonneg hnR.le _)
  have hcprime : 0≤C := by linarith
  have herror : 2*C*sourcePredualEpsilon r n*‖q‖^2≤
      Real.log (1+(n:ℝ))/(n:ℝ)^(1-r)*(8*C*m^2) := by
    calc
      _ ≤ 2*C*(Real.log (1+(n:ℝ))/(n:ℝ)^(1-r))*‖q‖^2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (source_epsilon_log_bound r n hn) (by positivity)) (sq_nonneg _)
      _ ≤ 2*C*(Real.log (1+(n:ℝ))/(n:ℝ)^(1-r))*(4*m^2) :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = _ := by ring
  refine ⟨?_,hbdiag,hbsharp.1.trans herror,hbsharp.2.trans herror,?_⟩
  · have hd := source_wideDiagonal_error r hr hr1 n hn z hz (endpointForgetWeight w r q) hsmall1
    rw [endpointForgetWeight_apply,hq0,sub_zero] at hd
    calc
      _ ≤ 2*(sourceCoefficientConstant r*(n:ℝ)^(r-1/2)*‖endpointForgetWeight w r q‖)*‖endpointForgetWeight w r q‖ := hd
      _ = (2*sourceCoefficientConstant r*(n:ℝ)^(r-1/2))*‖endpointForgetWeight w r q‖^2 := by ring
      _ ≤ (2*sourceCoefficientConstant r*(n:ℝ)^(r-1/2))*(4*m^2) :=
        mul_le_mul_of_nonneg_left hsqu (by positivity)
      _ = _ := by rw [he]; ring
  · have hpowers : (n:ℝ)^(1-r)=(n:ℝ)^((1:ℝ)/2)*(n:ℝ)^(1/2-r) := by
      rw [← Real.rpow_add hnR]
      congr 1
      ring
    have h32 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hscale (by linarith : (0:ℝ)≤m))
      (by norm_num : (0:ℝ)≤8)
    have hb : 8*C*m^2/(n:ℝ)^(1/2-r)≤m/4 := by
      rw [div_eq_mul_inv,← he]
      nlinarith
    have hmul := mul_le_mul_of_nonneg_left hb
      (show 0≤Real.log (1+(n:ℝ))/(n:ℝ)^((1:ℝ)/2) from
        div_nonneg (Real.log_nonneg (by linarith)) (Real.rpow_nonneg hnR.le _))
    calc
      _ = (Real.log (1+(n:ℝ))/(n:ℝ)^((1:ℝ)/2))*(8*C*m^2/(n:ℝ)^(1/2-r)) := by
        rw [hpowers]
        ring
      _ ≤ _ := hmul

/-- Analyticity holds jointly on a neighborhood of every point in the
closed source ball and printed strip, under the very same threshold. -/
theorem sourceLemma2_16_analytic (r : ℝ) (hr : 0≤r) (hr1 : r<1/2)
    (C m : ℝ) (hC : sourceCoefficientConstant r≤C) (hm : 1≤m)
    (n : ℕ) (hn : 2≤n) (h35 : 16*C*m/(n:ℝ)^(1/2-r)≤1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) (hq : ‖q‖≤2*m)
    (z : ℂ) (hz : z ∈ wideHillStrip n) :
    AnalyticAt ℂ (endpointDiagonal r hr hr1 n) (q,z) ∧
    AnalyticAt ℂ (endpointUpperCoupling r hr hr1 n) (q,z) ∧
    AnalyticAt ℂ (endpointLowerCoupling r hr hr1 n) (q,z) :=
  analyticAt_endpointCoefficients_wide r hr hr1 n hn (q,z) hz
    ((source_threshold35_small r C m hC hr1 hm n hn h35 ‖q‖ hq).trans (by norm_num))

/-- Full Lemma 2.16: one c'_s gives the printed estimates and joint
analyticity under exactly (35), for every weight and source norm ball. -/
theorem sourceLemma2_16 (r : ℝ) (hr : 0≤r) (hr1 : r<1/2) :
    ∃ C : ℝ, 1≤C ∧ sourceCoefficientConstant r≤C ∧
      SourceLemma216Bounds r hr hr1 C ∧
      ∀ (m : ℝ), 1≤m → ∀ (n : ℕ), 2≤n →
        16*C*m/(n:ℝ)^(1/2-r)≤1/2 →
        ∀ (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤), ‖q‖≤2*m →
        ∀ (z : ℂ), z ∈ wideHillStrip n →
          AnalyticAt ℂ (endpointDiagonal r hr hr1 n) (q,z) ∧
          AnalyticAt ℂ (endpointUpperCoupling r hr hr1 n) (q,z) ∧
          AnalyticAt ℂ (endpointLowerCoupling r hr hr1 n) (q,z) := by
  obtain ⟨C,hC,hwide,h⟩ := sourceLemma2_16_bounds r hr hr1
  exact ⟨C,hC,hwide,h,fun m hm n hn h35 q hq z hz =>
    sourceLemma2_16_analytic r hr hr1 C m hwide hm n hn h35 q hq z hz⟩

end NLS.Articles.KdVPseudomeasures
