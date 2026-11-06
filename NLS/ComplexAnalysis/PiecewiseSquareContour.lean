import NLS.ComplexAnalysis.PiecewiseC1Loop
import Mathlib.Analysis.Calculus.Deriv.Pow

/-! # Squaring actual piecewise smooth contours

The image contour retains its oriented path parameters. Its integral has
the literal complex Jacobian 2*z, including at corners of the original
piecewise C¹ loop. No primitive-value definition of an integral is used.
-/
noncomputable section
open Set Complex
namespace NLS.ComplexAnalysis

/-- The actual squared path, including its prescribed endpoints. -/
def squarePath {a b : ℂ} (γ : Path a b) : Path (a^2) (b^2) :=
  γ.map (continuous_id.pow 2)

@[simp] theorem squarePath_extend {a b : ℂ} (γ : Path a b) (t : ℝ) :
    (squarePath γ).extend t = (γ.extend t)^2 := rfl

theorem contDiffOn_squarePath {a b : ℂ} (γ : Path a b)
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1)) :
    ContDiffOn ℝ 1 (squarePath γ).extend (Icc 0 1) := hγ.pow 2

/-- Change of variables in the actual path integral. -/
theorem curveIntegral_squarePath {a b : ℂ} (γ : Path a b)
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1)) (f : ℂ → ℂ) :
    (∫ᶜ w in squarePath γ, holomorphicOneForm f w) =
      ∫ᶜ z in γ, holomorphicOneForm (fun z => 2*z*f (z^2)) z := by
  rw [curveIntegral_eq_intervalIntegral_deriv,curveIntegral_eq_intervalIntegral_deriv]
  apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
  intro t ht
  have hd : DifferentiableAt ℝ γ.extend t :=
    (hγ.contDiffAt (Icc_mem_nhds ht.1 ht.2)).differentiableAt (by norm_num)
  have he : deriv (squarePath γ).extend t = 2*γ.extend t*deriv γ.extend t := by
    simpa only [squarePath_extend,Nat.cast_ofNat,pow_one,Nat.reduceSub] using!
      (hd.hasDerivAt.pow 2).deriv
  dsimp only
  rw [holomorphicOneForm_apply,holomorphicOneForm_apply,he,squarePath_extend]
  ring

namespace PiecewiseC1Loop

/-- Image under z -> z², with the same oriented pieces. -/
def square (Γ : PiecewiseC1Loop) : PiecewiseC1Loop where
  count := Γ.count
  vertex i := (Γ.vertex i)^2
  edge i := squarePath (Γ.edge i)
  smooth i := contDiffOn_squarePath (Γ.edge i) (Γ.smooth i)
  closed := congrArg (fun z : ℂ => z^2) Γ.closed

theorem integral_square (Γ : PiecewiseC1Loop) (f : ℂ → ℂ) :
    Γ.square.integral f = Γ.integral (fun z => 2*z*f (z^2)) := by
  change (∑ i : Fin Γ.count, ∫ᶜ w in squarePath (Γ.edge i), holomorphicOneForm f w) = _
  simp only [curveIntegral_squarePath _ (Γ.smooth _)]
  rfl

theorem inside_square (Γ : PiecewiseC1Loop) {D E : Set ℂ}
    (hΓ : Γ.Inside D) (hmap : ∀ z ∈ D, z^2 ∈ E) : Γ.square.Inside E := by
  intro i u
  exact hmap (Γ.edge i u) (hΓ i u)

end PiecewiseC1Loop
end NLS.ComplexAnalysis
