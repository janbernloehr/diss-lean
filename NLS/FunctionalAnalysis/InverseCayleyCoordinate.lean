import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-! # The real coordinate of the inverse Cayley transform -/
noncomputable section
set_option autoImplicit false
open Complex MeasureTheory
namespace NLS.FunctionalAnalysis

/-- Rational inverse Cayley coordinate, with the field convention zero at one. -/
def inverseCayleyCoordinate (ζ : ℂ) : ℂ := I*(1+ζ)/(1-ζ)

/-- The real coordinate used for transporting the actual Cayley scalar measures. -/
def inverseCayleyReal (ζ : ℂ) : ℝ := (inverseCayleyCoordinate ζ).re

theorem measurable_inverseCayleyReal : Measurable inverseCayleyReal := by
  unfold inverseCayleyReal inverseCayleyCoordinate
  exact continuous_re.measurable.comp ((measurable_const.mul (measurable_const.add measurable_id)).div
    (measurable_const.sub measurable_id))

/-- On the unit circle the inverse coordinate is real, including its convention at one. -/
theorem inverseCayleyCoordinate_im_eq_zero (ζ : ℂ) (hζ : ζ ∈ unitary ℂ) :
    (inverseCayleyCoordinate ζ).im = 0 := by
  have hn : normSq ζ = 1 := by
    have h := Unitary.mem_iff_star_mul_self.mp hζ
    change (starRingEnd ℂ) ζ*ζ = 1 at h
    rw [← normSq_eq_conj_mul_self] at h
    exact_mod_cast h
  have hs : ζ.re*ζ.re+ζ.im*ζ.im = 1 := by simpa [normSq_apply] using hn
  simp only [inverseCayleyCoordinate,div_im,mul_re,mul_im,I_re,I_im,zero_mul,one_mul,
    add_re,one_re,add_im,one_im,zero_add,sub_re,sub_im]
  have hz : (1+ζ.re)*(1-ζ.re)-(-ζ.im)*(-ζ.im) = 0 := by nlinarith
  rw [zero_sub,← sub_div,hz,zero_div]

/-- The real coordinate is the full inverse coordinate on the actual unit circle. -/
theorem ofReal_inverseCayleyReal (ζ : ℂ) (hζ : ζ ∈ unitary ℂ) :
    (inverseCayleyReal ζ : ℂ) = inverseCayleyCoordinate ζ := by
  apply Complex.ext
  · rfl
  · simp [inverseCayleyCoordinate_im_eq_zero ζ hζ]

/-- The inverse coordinate recovers the original unit-circle parameter away from one. -/
theorem cayley_inverseCayleyReal (ζ : ℂ) (hζ : ζ ∈ unitary ℂ) (hne : ζ ≠ 1) :
    ((inverseCayleyReal ζ : ℂ)-I)/((inverseCayleyReal ζ : ℂ)+I) = ζ := by
  rw [ofReal_inverseCayleyReal ζ hζ]
  have hd : 1-ζ ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hnum : I*(1+ζ)+I*(1-ζ) ≠ 0 := by
    rw [show I*(1+ζ)+I*(1-ζ) = 2*I by ring]
    simp
  unfold inverseCayleyCoordinate
  field_simp
  ring

end NLS.FunctionalAnalysis
