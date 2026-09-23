import NLS.ComplexAnalysis.LocalHolomorphicLoopStability
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Holomorphic integrals along continuous families of smooth loops

Local stability makes a holomorphic one-form's integral locally constant
as a smooth loop varies continuously. Connectedness of the homotopy
parameter then identifies the endpoint integrals, even if the homotopy
is only continuous as a map on the whole square. Basepoints may move.
-/

noncomputable section
open Set Metric Complex Filter
open scoped unitInterval
namespace NLS.ComplexAnalysis

/-- The closed loop at an intermediate time of a homotopy whose slices
have matching endpoints. -/
def homotopyLoop
    {a b : ℂ} {γ₁ : Path a a} {γ₂ : Path b b}
    (H : (γ₁ : C(I, ℂ)).Homotopy γ₂)
    (hloop : ∀ s : I, H (s, 1) = H (s, 0))
    (s : I) : Path (H (s,0)) (H (s,0)) where
  toFun := H.toContinuousMap.curry s
  source' := rfl
  target' := hloop s

/-- Evaluation of an intermediate loop agrees with the homotopy. -/
@[simp] theorem homotopyLoop_apply
    {a b : ℂ} {γ₁ : Path a a} {γ₂ : Path b b}
    (H : (γ₁ : C(I, ℂ)).Homotopy γ₂)
    (hloop : ∀ s : I, H (s, 1) = H (s, 0))
    (s u : I) : homotopyLoop H hloop s u = H (s,u) := rfl

/-- A holomorphic one-form has the same integral on the endpoint loops
of a continuous homotopy with twice-smooth, gap-avoiding slices. The
basepoint may vary with the homotopy parameter. -/
theorem curveIntegral_eq_of_continuous_smooth_loop_homotopy
    (f : ℂ → ℂ) (Ω : Set ℂ)
    (hΩopen : IsOpen Ω)
    (hf : ∀ z ∈ Ω, DifferentiableAt ℂ f z)
    {a b : ℂ} {γ₁ : Path a a} {γ₂ : Path b b}
    (H : (γ₁ : C(I, ℂ)).Homotopy γ₂)
    (hloop : ∀ s : I, H (s, 1) = H (s, 0))
    (hsmooth : ∀ s : I,
      ContDiffOn ℝ 2 (homotopyLoop H hloop s).extend (Icc 0 1))
    (hinside : ∀ s u : I, H (s,u) ∈ Ω) :
    (∫ᶜ z in γ₁, holomorphicOneForm f z) =
      ∫ᶜ z in γ₂, holomorphicOneForm f z := by
  let J : I → ℂ := fun s =>
    ∫ᶜ z in homotopyLoop H hloop s, holomorphicOneForm f z
  have hHuc : UniformContinuous (fun x : I × I => H x) :=
    CompactSpace.uniformContinuous_of_continuous H.continuous
  have hJ : IsLocallyConstant J := by
    apply (IsLocallyConstant.iff_eventually_eq J).2
    intro s
    obtain ⟨ε, hε, hstable⟩ :=
      exists_curveIntegral_eq_of_uniform_perturbation
        f Ω hΩopen hf (homotopyLoop H hloop s) (hsmooth s)
        (fun u => by simpa only [homotopyLoop_apply] using hinside s u)
    obtain ⟨δ, hδ, huniform⟩ := Metric.uniformContinuous_iff.mp hHuc ε hε
    filter_upwards [Metric.ball_mem_nhds s hδ] with t ht
    have hclose (u : I) :
        dist (homotopyLoop H hloop t u) (homotopyLoop H hloop s u) ≤ ε := by
      rw [homotopyLoop_apply, homotopyLoop_apply]
      apply le_of_lt
      apply huniform
      simpa only [dist_prod_same_right, mem_ball] using ht
    exact hstable (homotopyLoop H hloop t) (hsmooth t) hclose
  have hconst : J 0 = J 1 :=
    hJ.apply_eq_of_isPreconnected isPreconnected_univ (mem_univ 0) (mem_univ 1)
  have h0 : homotopyLoop H hloop 0 =
      γ₁.cast (by simp) (by simp) := by
    apply Path.ext
    funext u
    simp [homotopyLoop_apply]
  have h1 : homotopyLoop H hloop 1 =
      γ₂.cast (by simp) (by simp) := by
    apply Path.ext
    funext u
    simp [homotopyLoop_apply]
  simpa [J, h0, h1] using hconst

end NLS.ComplexAnalysis
