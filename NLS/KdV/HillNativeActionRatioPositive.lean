import NLS.KdV.HillNativeActionRatioFree
import NLS.ComplexAnalysis.UniformPositiveAnalyticFamily

/-! # One positive square-root branch for every native action ratio -/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV
variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem exists_hillNativeActionGapRatio_all_positive :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧ ∀ k : ℕ+,
      AnalyticOnNhd ℂ (hillNativeActionGapRatio h0q h0r k) (ball (0 : Coeff 2) η) ∧
      ∀ u ∈ ball (0 : Coeff 2) η,
        ‖hillNativeActionGapRatio h0q h0r k u‖ ≤ C/(k : ℝ) ∧
        0 < (hillNativeActionGapRatio h0q h0r k u).re := by
  obtain ⟨R,C,hR,hC,hdata⟩ := exists_hillNativeActionGapRatio_all_analytic_bound h0q h0r
  let f := fun (k : ℕ+) (u : Coeff 2) => (k : ℂ)*hillNativeActionGapRatio h0q h0r k u
  let a : ℂ := (2*(Real.pi : ℂ))⁻¹
  have ha : 0 < a.re := by
    dsimp only [a]
    rw [show (2*(Real.pi : ℂ))⁻¹ = ((2*Real.pi)⁻¹ : ℝ) by push_cast; rfl,ofReal_re]
    positivity
  have hf (k : ℕ+) : AnalyticOnNhd ℂ (f k) (ball (0 : Coeff 2) R) :=
    analyticOnNhd_const.mul (hdata k).1
  have hb (k : ℕ+) (u : Coeff 2) (hu : u ∈ ball 0 R) : ‖f k u‖ ≤ C := by
    have hk : (0 : ℝ) < k := by positivity
    change ‖(k : ℂ)*hillNativeActionGapRatio h0q h0r k u‖ ≤ _
    rw [norm_mul,show ‖(k : ℂ)‖ = (k : ℝ) by simp]
    apply (mul_le_mul_of_nonneg_left ((hdata k).2 u hu) hk.le).trans_eq
    field_simp
  obtain ⟨η,hη,hηR,hpositive⟩ := exists_uniform_ball_positive_re f R C a hR hC ha hf hb
    (hillNativeActionGapRatio_normalized_zero h0q h0r)
  have hsub : ball (0 : Coeff 2) η ⊆ ball 0 R := ball_subset_ball hηR
  refine ⟨η,C,hη,hC,?_⟩
  intro k
  refine ⟨(hdata k).1.mono hsub,?_⟩
  intro u hu
  refine ⟨(hdata k).2 u (hsub hu),?_⟩
  have hp := (hpositive k u hu).2
  change 0 < ((k : ℂ)*hillNativeActionGapRatio h0q h0r k u).re at hp
  simp only [mul_re,natCast_re,natCast_im,zero_mul,sub_zero] at hp
  have hk : (0 : ℝ) < k := by positivity
  nlinarith

end NLS.KdV
