import NLS.KdV.HillIntrinsicPeriodReflection
import Mathlib.Analysis.Calculus.Deriv.Star

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV

variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

theorem complex_entire_eq_zero_of_hill_periods_and_product_decay
    (N : ℂ → ℂ) (hN : AnalyticOnNhd ℂ N univ)
    (hperiods : ∀ k : ℕ, 1 ≤ k → hillIntrinsicGapPeriod q hq hr k N = 0)
    (hdecay : ∀ roots ∈ hillGapRootBox q hq hr, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ k : ℕ in atTop, ∀ E ∈ sphere (0 : ℂ) ((centralCircleRadius k)^2),
        ‖N E/hillAbelianNumeratorProduct roots 0 E‖ ≤ ε) : N = 0 := by
  have hprojection (a : ℂ) (ha : ‖a‖ = 1) : (fun E => a*N E+conj (a*N (conj E))) = 0 := by
    let A : ℂ → ℂ := fun E => a*N E
    let B : ℂ → ℂ := fun E => conj (A (conj E))
    have hA : AnalyticOnNhd ℂ A univ := analyticOnNhd_const.mul hN
    have hB : AnalyticOnNhd ℂ B univ := by
      apply analyticOnNhd_univ_iff_differentiable.mpr
      intro E
      simpa only [Function.comp_def,conj_conj] using (hA (conj E) (mem_univ _)).differentiableAt.conj_conj
    apply entire_eq_zero_of_hill_periods_and_product_decay q hq hr (fun E => A E+B E) (hA.add hB)
    · intro x
      dsimp only [B]
      rw [conj_ofReal,add_im,conj_im]
      ring
    · intro k hk
      have hpA : hillIntrinsicGapPeriod q hq hr k A = 0 := by
        rw [hillIntrinsicGapPeriod_const_mul q hq hr k N a,hperiods k hk,mul_zero]
      have hpB : hillIntrinsicGapPeriod q hq hr k B = 0 := by
        rw [hillIntrinsicGapPeriod_reflection q hq hr k hk A,hpA,map_zero]
      rw [hillIntrinsicGapPeriod_add q hq hr k hk A B hA hB,hpA,hpB,add_zero]
    · intro roots hroots ε hε
      filter_upwards [hdecay roots hroots (ε/2) (by positivity)] with k hk
      intro E hE
      have hcE : conj E ∈ sphere (0 : ℂ) ((centralCircleRadius k)^2) := by
        simpa only [mem_sphere,dist_zero_right,norm_conj] using hE
      have hfirst : ‖A E/hillAbelianNumeratorProduct roots 0 E‖ ≤ ε/2 := by
        simpa only [A,mul_div_assoc,norm_mul,ha,one_mul] using hk E hE
      have hsecond : ‖B E/hillAbelianNumeratorProduct roots 0 E‖ ≤ ε/2 := by
        have he : B E/hillAbelianNumeratorProduct roots 0 E =
            conj (A (conj E)/hillAbelianNumeratorProduct roots 0 (conj E)) := by
          simp only [B,map_div₀,hillAbelianNumeratorProduct_conj q hq hr roots hroots 0 E,conj_conj]
        rw [he,norm_conj]
        simpa only [A,mul_div_assoc,norm_mul,ha,one_mul] using hk (conj E) hcE
      rw [add_div]
      exact (norm_add_le _ _).trans (by linarith)
  have hone := hprojection 1 norm_one
  have hi := hprojection Complex.I norm_I
  funext E
  have h1 := congrFun hone E
  have h2 := congrFun hi E
  simp only [one_mul,Pi.zero_apply] at h1
  simp only [map_mul,conj_I,Pi.zero_apply] at h2
  calc
    N E = (N E+conj (N (conj E)))/2-Complex.I*(Complex.I*N E+(-Complex.I)*conj (N (conj E)))/2 := by
      ring_nf
      rw [I_sq]
      ring
    _ = 0 := by rw [h1,h2];ring

end NLS.KdV
