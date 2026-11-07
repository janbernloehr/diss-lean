import NLS.ComplexAnalysis.CauchyFiniteHoles
import NLS.ComplexAnalysis.EntireCircleDecay

/-! An even entire function with subquadratic growth on expanding
circles is constant. Twice-filled divided differences reduce the
claim to the verified maximum-modulus circle-decay theorem. -/
noncomputable section
open Set Metric Complex Filter Topology
namespace NLS.ComplexAnalysis

theorem deriv_zero_at_zero_of_even (Q : ℂ → ℂ) (hQ : AnalyticAt ℂ Q 0)
    (heven : ∀ z : ℂ, Q (-z) = Q z) : deriv Q 0 = 0 := by
  have hd := hQ.differentiableAt.hasDerivAt
  have hn := hd.comp_of_eq (h := fun z : ℂ => -z) 0 (hasDerivAt_id (0:ℂ)).neg (by simp)
  have he : (fun z : ℂ => Q (-z)) = Q := funext heven
  dsimp only [Function.comp_def] at hn
  rw [he] at hn
  have h := hn.unique hd
  have hz : (2:ℂ)*deriv Q 0 = 0 := by linear_combination -h
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

theorem entire_even_eq_const_of_subquadratic_circles (Q : ℂ → ℂ)
    (hQ : AnalyticOnNhd ℂ Q univ) (heven : ∀ z : ℂ, Q (-z) = Q z)
    (R : ℕ → ℝ) (hR : Tendsto R atTop atTop)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop,
      ∀ z ∈ sphere (0:ℂ) (R k), ‖Q z‖ ≤ ε*(R k)^2) : ∀ z : ℂ, Q z = Q 0 := by
  let H := dslope (dslope Q 0) 0
  have hH : AnalyticOnNhd ℂ H univ :=
    analyticOnNhd_dslope_of_analytic _ univ 0
      (analyticOnNhd_dslope_of_analytic Q univ 0 hQ (mem_univ _)) (mem_univ _)
  have hd := deriv_zero_at_zero_of_even Q (hQ 0 (mem_univ _)) heven
  have hfactor (z : ℂ) : z^2*H z = Q z-Q 0 := by
    have h₁ : z*dslope Q 0 z = Q z-Q 0 := by
      simpa only [sub_zero,smul_eq_mul] using sub_smul_dslope Q 0 z
    have h₂ : z*H z = dslope Q 0 z := by
      simpa only [H,sub_zero,smul_eq_mul,dslope_same,hd] using sub_smul_dslope (dslope Q 0) 0 z
    calc
      z^2*H z = z*(z*H z) := by ring
      _ = Q z-Q 0 := by rw [h₂,h₁]
  have hzeroH : H = 0 := by
    apply entire_eq_zero_of_small_on_expanding_circles (fun z => (hH z (mem_univ _)).differentiableAt) R hR
    intro ε hε
    filter_upwards [hsmall (ε/2) (by positivity),
      hR.eventually_ge_atTop (max 1 (2*‖Q 0‖/ε))] with k hk hlarge z hz
    have hRone : 1 ≤ R k := (le_max_left _ _).trans hlarge
    have hRpos : 0 < R k := by linarith
    have hlow : 2*‖Q 0‖/ε ≤ R k := (le_max_right _ _).trans hlarge
    have hlow' : 2*‖Q 0‖ ≤ (R k)*ε := (div_le_iff₀ hε).mp hlow
    have hRsq : R k ≤ (R k)^2 := by nlinarith
    have hscaled := mul_le_mul_of_nonneg_left hRsq hε.le
    have hconst : ‖Q 0‖ ≤ (ε/2)*(R k)^2 := by linarith
    have hnorm : ‖z‖ = R k := by simpa only [mem_sphere,dist_zero_right] using hz
    have hbound : (R k)^2*‖H z‖ ≤ (R k)^2*ε := by
      calc
        (R k)^2*‖H z‖ = ‖Q z-Q 0‖ := by rw [← hnorm,← norm_pow,← norm_mul,hfactor]
        _ ≤ ‖Q z‖+‖Q 0‖ := norm_sub_le _ _
        _ ≤ (ε/2)*(R k)^2+(ε/2)*(R k)^2 := add_le_add (hk z hz) hconst
        _ = (R k)^2*ε := by ring
    exact le_of_mul_le_mul_left hbound (sq_pos_of_pos hRpos)
  intro z
  have h := hfactor z
  rw [hzeroH,Pi.zero_apply,mul_zero] at h
  exact sub_eq_zero.mp h.symm

end NLS.ComplexAnalysis
