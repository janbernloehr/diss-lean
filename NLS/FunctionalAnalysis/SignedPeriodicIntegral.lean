import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! A common sign cancels in physical bilinear integrals, including the
derivative products. The normalized doubled interval is exactly the unit interval. -/
noncomputable section
open Set MeasureTheory
namespace NLS.FunctionalAnalysis

/-- Closed-interval agreement determines the totalized derivative almost
everywhere in its interior; no regularity outside that interval is needed. -/
theorem ae_deriv_eq_of_eqOn_Icc {f g : ℝ → ℂ} {a b : ℝ}
    (hfg : EqOn f g (Icc a b)) :
    deriv f =ᵐ[volume.restrict (Ioc a b)] deriv g := by
  have hne : ∀ᵐ x : ℝ ∂volume, x ≠ b := by simp [ae_iff]
  filter_upwards [ae_restrict_mem measurableSet_Ioc,ae_restrict_of_ae hne] with x hx hxb
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [Ioo_mem_nhds hx.1 (lt_of_le_of_ne hx.2 hxb)] with y hy
  exact hfg ⟨hy.1.le,hy.2.le⟩

/-- Differentiation retains a constant complex translation multiplier,
without an extra pointwise differentiability assumption. -/
theorem deriv_translate_one_of_multiplier (f : ℝ → ℂ) (e : ℂ)
    (hf : ∀ x, f (x+1) = e*f x) (x : ℝ) :
    deriv f (x+1) = e*deriv f x := by
  have he : (fun y : ℝ => f (y+1)) = fun y => e*f y := funext hf
  calc
    _ = deriv (fun y : ℝ => f (y+1)) x := (deriv_comp_add_const f 1 x).symm
    _ = _ := by rw [he,deriv_const_mul_field]

/-- The exact half-period normalization for any integrable product
whose two factors have the same sign multiplier. -/
theorem half_integral_mul_of_common_sign (f g : ℝ → ℂ) (e : ℂ)
    (he : e^2 = 1) (hf : ∀ x, f (x+1) = e*f x) (hg : ∀ x, g (x+1) = e*g x)
    (hi : IntervalIntegrable (fun x => f x*g x) volume 0 2) :
    (2:ℂ)⁻¹*(∫ x in (0:ℝ)..2, f x*g x) = ∫ x in (0:ℝ)..1, f x*g x := by
  let F := fun x => f x*g x
  have hper (x : ℝ) : F (x+1) = F x := by
    dsimp only [F]
    rw [hf,hg]
    calc
      _ = e^2*(f x*g x) := by ring
      _ = _ := by rw [he,one_mul]
  have hshift : (∫ x in (1:ℝ)..2, F x) = ∫ x in (0:ℝ)..1, F x := by
    have h := intervalIntegral.integral_comp_add_right (a := (0:ℝ)) (b := 1) F 1
    simp only [zero_add,one_add_one_eq_two,hper] at h
    exact h.symm
  have hleft : IntervalIntegrable F volume 0 1 := hi.mono_set (by
    simp only [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1),uIcc_of_le (by norm_num : (0:ℝ) ≤ 2)]
    exact Icc_subset_Icc_right (by norm_num))
  have hright : IntervalIntegrable F volume 1 2 := hi.mono_set (by
    simp only [uIcc_of_le (by norm_num : (1:ℝ) ≤ 2),uIcc_of_le (by norm_num : (0:ℝ) ≤ 2)]
    exact Icc_subset_Icc_left (by norm_num))
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hleft hright
  rw [hshift] at hsplit
  change (2:ℂ)⁻¹*(∫ x in (0:ℝ)..2, F x) = _
  rw [← hsplit]
  ring

end NLS.FunctionalAnalysis
