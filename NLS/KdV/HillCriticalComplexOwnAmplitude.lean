import NLS.KdV.HillNativeWeightedOwnFactors
import NLS.KdV.HillCommonComplexOwnAmplitudes

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem exists_hillComplexOwnCartesianAmplitudes_native_critical_pointwise_bound
    (B : ℝ) (hB : 0≤B) :
    ∃ C : ℝ, 0<C ∧ ∃ N : ℕ, 1≤N ∧ ∀ w : SpectralWeight,
      ∀ q : WeightedCoeff w.doubleIndex.toWeight 2, ‖q‖≤B → ∀ n : ℕ, N≤n →
      (n : ℝ)*(w (2*(n : ℤ)))^2*
          ‖hillComplexOwnCartesianAmplitude h0q h0r n (hillPeriodOneCoefficientMap w q)‖^2 ≤
        C*((w (2*(n : ℤ)))^2*‖q.val n‖^2+(w (2*(n : ℤ)))^2*‖q.val (-(n : ℤ))‖^2+
          256*‖q‖^4/(n : ℝ)^2) ∧
      (n : ℝ)*(w (2*(n : ℤ)))^2*
          ‖hillComplexOwnCartesianDualAmplitude h0q h0r n (hillPeriodOneCoefficientMap w q)‖^2 ≤
        C*((w (2*(n : ℤ)))^2*‖q.val n‖^2+(w (2*(n : ℤ)))^2*‖q.val (-(n : ℤ))‖^2+
          256*‖q‖^4/(n : ℝ)^2) := by
  obtain ⟨Cp,hCp,hpref⟩ := exists_hillComplexActionGapPrefactor_common_analytic_bound h0q h0r
  obtain ⟨Np,hNp,hp⟩ := hpref (B+1)
  obtain ⟨Cf,hCf,Nf,hNf,hfactor⟩ := exists_hillComplexOwnGapFactors_native_weighted_bound h0q h0r B hB
  refine ⟨3*Cp*Cf^2,by positivity,max Np Nf,hNp.trans (le_max_left _ _),?_⟩
  intro w q hq n hn
  have hnP : Np≤n := (le_max_left _ _).trans hn
  have hnF : Nf≤n := (le_max_right _ _).trans hn
  have hn1 : 1≤n := hNp.trans hnP
  have hnpos : (0 : ℝ)<n := by exact_mod_cast (show 0<n by omega)
  let p := hillPeriodOneCoefficientMap w q
  let a := hillComplexActionGapPrefactor h0q h0r n p
  let W := w (2*(n : ℤ))
  let P := W*‖q.val n‖
  let M := W*‖q.val (-(n : ℤ))‖
  let e := 16*‖q‖^2/(n : ℝ)
  have hW : 0≤W := (w.positive _).le
  have hpball : p∈ball (0 : Coeff 2) (B+1) := by
    rw [mem_ball,dist_zero_right]
    exact (norm_hillPeriodOneCoefficientMap_le w q).trans hq |>.trans_lt (by linarith)
  have ha : (n : ℝ)*‖a‖^2≤Cp := by
    change (n : ℝ)*‖hillComplexActionGapPrefactor h0q h0r n p‖^2≤Cp
    nlinarith only [(le_div_iff₀ hnpos).mp (((hp n hnP).2 p hpball).2)]
  obtain ⟨hFp,hFm⟩ := hfactor w q hq n hnF
  have hpoint (F : ℂ) (hF : W*‖F‖≤Cf*(P+M+e)) :
      (n : ℝ)*W^2*‖a*F‖^2 ≤ 3*Cp*Cf^2*(P^2+M^2+e^2) := by
    have hsum : (P+M+e)^2≤3*(P^2+M^2+e^2) := by
      nlinarith [sq_nonneg (P-M),sq_nonneg (P-e),sq_nonneg (M-e)]
    have hF0 : 0≤W*‖F‖ := mul_nonneg hW (norm_nonneg _)
    have hright : 0≤Cf*(P+M+e) := hF0.trans hF
    have hFsq : (W*‖F‖)^2≤Cf^2*(P+M+e)^2 := by
      simpa only [mul_pow] using (sq_le_sq₀ hF0 hright).mpr hF
    calc
      _ = ((n : ℝ)*‖a‖^2)*(W*‖F‖)^2 := by rw [norm_mul];ring
      _ ≤ Cp*(Cf^2*(P+M+e)^2) := mul_le_mul ha hFsq (sq_nonneg _) hCp.le
      _ ≤ Cp*(Cf^2*(3*(P^2+M^2+e^2))) := by gcongr
      _ = _ := by ring
  have hbudget : P^2+M^2+e^2 =
      W^2*‖q.val n‖^2+W^2*‖q.val (-(n : ℤ))‖^2+256*‖q‖^4/(n : ℝ)^2 := by
    dsimp only [P,M,e]
    simp only [div_pow,mul_pow]
    ring
  constructor
  · have hh := hpoint (hillComplexOwnGapFactor h0q h0r n p) hFp
    rw [hbudget] at hh
    exact hh
  · have hh := hpoint (hillComplexOwnGapDualFactor h0q h0r n p) hFm
    rw [hbudget] at hh
    exact hh

end NLS.KdV
