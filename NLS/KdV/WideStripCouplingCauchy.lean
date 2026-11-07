import NLS.KdV.FreeHillWideGeometry
import NLS.ComplexAnalysis.QuadraticGapActionRatioBounds

/-! A full-strip bound gives the source 1/88 spectral variation on the
small disc surrounding the actual diagonal root. -/
noncomputable section
open Set Metric
namespace NLS.KdV

theorem couplingCauchyDisc_subset_wide (n : ℕ) (hn : 1≤n) (α : ℂ) (ρ : ℝ)
    (hα : ‖α-(freeHillValue n:ℂ)‖≤Real.sqrt (n:ℝ)/256)
    (hρ : ρ≤Real.sqrt (n:ℝ)/32) :
    closedBall α (4*(n:ℝ)+2*ρ)⊆wideHillStrip n := by
  intro z hz
  have hnR : (1:ℝ)≤n := by exact_mod_cast hn
  have hsqrt : Real.sqrt (n:ℝ)≤n := Real.sqrt_le_iff.mpr ⟨by positivity,by nlinarith⟩
  have hd : ‖z-α‖≤4*(n:ℝ)+2*ρ := by simpa only [mem_closedBall,dist_eq_norm] using hz
  have ht := norm_sub_le_norm_sub_add_norm_sub z α (freeHillValue n:ℂ)
  have hre := Complex.abs_re_le_norm (z-(freeHillValue n:ℂ))
  simp only [Complex.sub_re,Complex.ofReal_re] at hre
  change |z.re-freeHillValue n|≤12*(n:ℝ)
  linarith

theorem wideStrip_smallDisc_variation (n : ℕ) (hn : 1≤n) (α : ℂ) (ρ : ℝ)
    (hρ0 : 0≤ρ) (hα : ‖α-(freeHillValue n:ℂ)‖≤Real.sqrt (n:ℝ)/256)
    (hρ : ρ≤Real.sqrt (n:ℝ)/32) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (wideHillStrip n))
    (hb : ∀ z ∈ wideHillStrip n, ‖f z‖≤Real.sqrt (n:ℝ)/32) :
    ∀ z ∈ closedBall α (2*ρ), ‖f z-f α‖≤ρ/44 := by
  have hnp : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hnR : (1:ℝ)≤n := by exact_mod_cast hn
  have hsqrt : Real.sqrt (n:ℝ)≤n := Real.sqrt_le_iff.mpr ⟨by positivity,by nlinarith⟩
  have hsub := couplingCauchyDisc_subset_wide n hn α ρ hα hρ
  have hsmall : closedBall α (2*ρ)⊆wideHillStrip n :=
    (closedBall_subset_closedBall (by linarith : 2*ρ≤4*(n:ℝ)+2*ρ)).trans hsub
  have hd (z : ℂ) (hz : z ∈ closedBall α (2*ρ)) : ‖deriv f z‖≤1/88 := by
    have hh := NLS.ComplexAnalysis.norm_deriv_le_of_analytic_closedDisc_bound f α (2*ρ)
      (4*(n:ℝ)+2*ρ) (Real.sqrt (n:ℝ)/32) (by linarith) (hf.mono hsub)
      (fun z hz => hb z (hsub hz)) z hz
    have he : (4*(n:ℝ)+2*ρ)-2*ρ=4*(n:ℝ) := by ring
    rw [he] at hh
    have hbound : (Real.sqrt (n:ℝ)/32)/(4*(n:ℝ))≤1/88 :=
      (div_le_iff₀ (by positivity : (0:ℝ)<4*(n:ℝ))).mpr (by linarith)
    exact hh.trans hbound
  intro z hz
  have hm := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun x hx => (hf x (hsmall hx)).differentiableAt) hd
    (convex_closedBall α (2*ρ)) (mem_closedBall_self (by positivity)) hz
  have hdist : ‖z-α‖≤2*ρ := by simpa only [mem_closedBall,dist_eq_norm] using hz
  nlinarith

end NLS.KdV
