import NLS.FunctionalAnalysis.InverseCayleyCoordinate
import Mathlib.Topology.ContinuousMap.Algebra

/-! # Continuous resolvent functions on the actual Cayley spectrum -/
noncomputable section
set_option autoImplicit false
open Complex
namespace NLS.FunctionalAnalysis

/-- The denominator obtained when the original resolvent is written in Cayley coordinates. -/
def cayleyResolventDenominator (z ζ : ℂ) : ℂ := z*(1-ζ)-I*(1+ζ)

theorem cayleyResolventDenominator_factor (z ζ : ℂ) (hne : ζ ≠ 1) :
    cayleyResolventDenominator z ζ = (1-ζ)*(z-inverseCayleyCoordinate ζ) := by
  have hd : 1-ζ ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  unfold cayleyResolventDenominator inverseCayleyCoordinate
  field_simp

/-- At a nonreal spectral parameter the denominator never vanishes on the unit circle. -/
theorem cayleyResolventDenominator_ne_zero (z : ℂ) (hz : z.im ≠ 0)
    (ζ : ℂ) (hζ : ζ ∈ unitary ℂ) : cayleyResolventDenominator z ζ ≠ 0 := by
  by_cases hone : ζ = 1
  · simp [hone,cayleyResolventDenominator]
  · rw [cayleyResolventDenominator_factor z ζ hone]
    apply mul_ne_zero (sub_ne_zero.mpr (Ne.symm hone))
    intro he
    have heq := sub_eq_zero.mp he
    exact hz (heq ▸ inverseCayleyCoordinate_im_eq_zero ζ hζ)

/-- Continuous resolvent test function, including its exact zero value at one. -/
def cayleyResolventFunction (s : Set ℂ) (hs : s ⊆ unitary ℂ)
    (z : ℂ) (hz : z.im ≠ 0) : C(s, ℂ) :=
  ⟨fun ζ => (1-(ζ : ℂ))/cayleyResolventDenominator z ζ,
    (continuous_const.sub continuous_subtype_val).div
      ((continuous_const.mul (continuous_const.sub continuous_subtype_val)).sub
        (continuous_const.mul (continuous_const.add continuous_subtype_val)))
      (fun ζ => cayleyResolventDenominator_ne_zero z hz ζ (hs ζ.property))⟩

@[simp] theorem cayleyResolventFunction_apply (s : Set ℂ) (hs : s ⊆ unitary ℂ)
    (z : ℂ) (hz : z.im ≠ 0) (ζ : s) :
    cayleyResolventFunction s hs z hz ζ = (1-(ζ : ℂ))/cayleyResolventDenominator z ζ := rfl

/-- Away from the null exceptional point the test function is the original real resolvent kernel. -/
theorem cayleyResolventFunction_eq_inverse (s : Set ℂ) (hs : s ⊆ unitary ℂ)
    (z : ℂ) (hz : z.im ≠ 0) (ζ : s) (hne : (ζ : ℂ) ≠ 1) :
    cayleyResolventFunction s hs z hz ζ = (z-(inverseCayleyReal ζ : ℂ))⁻¹ := by
  rw [cayleyResolventFunction_apply,ofReal_inverseCayleyReal ζ (hs ζ.property),
    cayleyResolventDenominator_factor z ζ hne]
  have hd : 1-(ζ : ℂ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  field_simp

end NLS.FunctionalAnalysis
