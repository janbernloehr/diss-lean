import NLS.ZakharovShabat.SourceGapInterpolationOuterCircles
import NLS.ZakharovShabat.CentralCircleThresholds

/-! Restoring one energy factor makes a sub-sine quadratic numerator
subquadratic relative to the actual full interpolation product.
The exact sine ratio and every physical energy translation are retained. -/
noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat

theorem restored_quadratic_product_quotient_subquadratic
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (ρ : ℤ → ℂ)
    (hρ : Memℓp (fun k => ρ k-(Real.pi:ℂ)*k) p)
    (P : ℂ → ℂ) (b c : ℂ)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      ∀ z ∈ sphere (0:ℂ) (centralCircleRadius k), ‖(2*z*P (z^2-c))/(-2*sin z)‖ ≤ ε) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop,
      ∀ z ∈ sphere (0:ℂ) (centralCircleRadius k),
        ‖((b-(z^2-c))*(2*z*P (z^2-c)))/entireSingleSpectralProduct ρ z‖ ≤
          ε*(centralCircleRadius k)^2 := by
  intro ε hε
  obtain ⟨K,hK⟩ := hsmall (ε/4) (by positivity)
  obtain ⟨L,hL⟩ := eventually_centralCircle_entireSingleSpectralProduct_div_free_close
    hp ρ hρ (by norm_num : (0:ℝ) < 1/2)
  filter_upwards [eventually_ge_atTop (max K L),
    tendsto_centralCircleRadius_atTop.eventually_ge_atTop (max 1 ‖b+c‖)] with k hk hlarge z hz
  have hnorm : ‖z‖ = centralCircleRadius k := by simpa only [mem_sphere,dist_zero_right] using hz
  have hRone : 1 ≤ centralCircleRadius k := (le_max_left _ _).trans hlarge
  have hRbig : ‖b+c‖ ≤ centralCircleRadius k := (le_max_right _ _).trans hlarge
  have hRsq : centralCircleRadius k ≤ (centralCircleRadius k)^2 := by nlinarith
  have hfactor : ‖b-(z^2-c)‖ ≤ 2*(centralCircleRadius k)^2 := by
    have he : b-(z^2-c) = (b+c)-z^2 := by ring
    rw [he]
    calc
      ‖b+c-z^2‖ ≤ ‖b+c‖+‖z^2‖ := norm_sub_le _ _
      _ = ‖b+c‖+(centralCircleRadius k)^2 := by rw [norm_pow,hnorm]
      _ ≤ 2*(centralCircleRadius k)^2 := by linarith
  have hgs := hL k ((le_max_right _ _).trans hk) z hz
  have hfree : -2*sin z ≠ (0:ℂ) := by
    intro he
    rw [he,div_zero,zero_sub,norm_neg,norm_one] at hgs
    norm_num at hgs
  have hden : (1:ℝ)/2 ≤ ‖entireSingleSpectralProduct ρ z/(-2*sin z)‖ := by
    have ht := norm_add_le (entireSingleSpectralProduct ρ z/(-2*sin z))
      (1-entireSingleSpectralProduct ρ z/(-2*sin z))
    rw [add_sub_cancel,norm_one,norm_sub_rev] at ht
    linarith
  have he : ((b-(z^2-c))*(2*z*P (z^2-c)))/entireSingleSpectralProduct ρ z =
      ((b-(z^2-c))*((2*z*P (z^2-c))/(-2*sin z)))/
        (entireSingleSpectralProduct ρ z/(-2*sin z)) := by
    rw [← mul_div_assoc,div_div_div_cancel_right₀ hfree]
  rw [he,norm_div,norm_mul]
  apply (div_le_iff₀ (by linarith : 0 < ‖entireSingleSpectralProduct ρ z/(-2*sin z)‖)).mpr
  calc
    ‖b-(z^2-c)‖*‖(2*z*P (z^2-c))/(-2*sin z)‖ ≤
        (2*(centralCircleRadius k)^2)*(ε/4) :=
      mul_le_mul hfactor (hK k ((le_max_left _ _).trans hk) z hz) (norm_nonneg _) (by positivity)
    _ = (ε*(centralCircleRadius k)^2)*(1/2) := by ring
    _ ≤ (ε*(centralCircleRadius k)^2)*‖entireSingleSpectralProduct ρ z/(-2*sin z)‖ :=
      mul_le_mul_of_nonneg_left hden (mul_nonneg hε.le (sq_nonneg _))

end NLS.ZakharovShabat
