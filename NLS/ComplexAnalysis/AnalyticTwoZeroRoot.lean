import NLS.ComplexAnalysis.AnalyticDiscSquareRoot
import NLS.ZakharovShabat.SourceStandardRootAnalytic

/-! # Analytic roots of a deflated two-zero function on a slit disc

The endpoint root uses the normalized quadratic formula already proved
in the spectral library. An analytic unit on the whole disc supplies the
remaining root factor. This constructs a branch on the complement of
the actual straight segment, including when the endpoints coincide.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
namespace NLS.ComplexAnalysis

def endpointRoot (a b z : ℂ) : ℂ :=
  NLS.ZakharovShabat.normalizedStandardRoot ((a+b)/2) ((b-a)^2) z

theorem midpoint_mem_complex_segment (a b : ℂ) : (a+b)/2 ∈ segment ℝ a b := by
  convert midpoint_mem_segment (𝕜 := ℝ) a b using 1
  rw [midpoint_eq_smul_add,invOf_eq_inv]
  simp only [Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_ofNat]
  ring

theorem endpointRoot_sq (a b z : ℂ) (hz : z ∉ segment ℝ a b) :
    endpointRoot a b z^2 = (z-a)*(z-b) := by
  have hmid : (a+b)/2 ≠ z := fun he => hz (he ▸ midpoint_mem_complex_segment a b)
  rw [endpointRoot,NLS.ZakharovShabat.normalizedStandardRoot_sq _ _ _ hmid]
  ring

theorem analyticOnNhd_endpointRoot (a b : ℂ) :
    AnalyticOnNhd ℂ (endpointRoot a b) (segment ℝ a b)ᶜ := by
  intro z hz
  exact NLS.ZakharovShabat.normalizedStandardRoot_analyticAt_of_slit _ _ z
    (fun he => hz (he ▸ midpoint_mem_complex_segment a b))
    (gap_radicand_mem_slitPlane a b z hz)

theorem exists_analytic_squareRoot_on_two_zero_cut
    (f Q : ℂ → ℂ) (a b c : ℂ) (R : ℝ) (hR : 0 < R)
    (hQ : AnalyticOnNhd ℂ Q (ball c R))
    (hne : ∀ z ∈ ball c R, Q z ≠ 0)
    (hfactor : ∀ z ∈ ball c R, f z = (z-a)*(z-b)*Q z) :
    ∃ B : ℂ → ℂ, AnalyticOnNhd ℂ B (ball c R \ segment ℝ a b) ∧
      ∀ z ∈ ball c R \ segment ℝ a b, B z ≠ 0 ∧ B z^2 = f z := by
  obtain ⟨h,hh,hsq⟩ := exists_analytic_squareRoot_on_ball Q c R hR hQ hne
  let B : ℂ → ℂ := fun z => endpointRoot a b z*h z
  have hB : AnalyticOnNhd ℂ B (ball c R \ segment ℝ a b) := by
    intro z hz
    exact (analyticOnNhd_endpointRoot a b z hz.2).mul (hh z hz.1)
  refine ⟨B,hB,?_⟩
  intro z hz
  have hbsq : B z^2 = f z := by
    dsimp only [B]
    rw [mul_pow,endpointRoot_sq a b z hz.2,(hsq z hz.1).2,hfactor z hz.1]
  have hza : z ≠ a := fun he => hz.2 (he ▸ left_mem_segment ℝ a b)
  have hzb : z ≠ b := fun he => hz.2 (he ▸ right_mem_segment ℝ a b)
  have hfne : f z ≠ 0 := by
    rw [hfactor z hz.1]
    exact mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hza) (sub_ne_zero.mpr hzb)) (hne z hz.1)
  refine ⟨?_,hbsq⟩
  intro he
  exact hfne (by rw [← hbsq,he]; simp)

end NLS.ComplexAnalysis
