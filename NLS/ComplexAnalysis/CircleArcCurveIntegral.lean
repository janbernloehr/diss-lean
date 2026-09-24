import NLS.ComplexAnalysis.CircleCurveIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Circle arcs as bundled paths

A circle arc with arbitrary starting and ending angles is bundled as a
path on the unit interval. Its complex one-form integral equals the
usual angle integral, including decreasing-angle orientation.
-/

noncomputable section
open Set Complex MeasureTheory Filter Function intervalIntegral
open scoped unitInterval
namespace NLS.ComplexAnalysis

/-- A nonzero direction, and also the zero direction by convention,
locates its endpoint on the circle of its norm. -/
theorem circleMap_norm_arg (c z : ℂ) :
    circleMap c ‖z‖ (arg z) = c+z := by
  simp only [circleMap, norm_mul_exp_arg_mul_I]

/-- The circular arc traversed linearly in angle from `α` to `β`. -/
def circleAngleArcPath (c : ℂ) (R α β : ℝ) :
    Path (circleMap c R α) (circleMap c R β) :=
  Path.ofLine
    (f := fun t : ℝ => circleMap c R (α+(β-α)*t))
    (by fun_prop)
    (by simp)
    (by simp)

/-- Every fixed-angle circle arc is twice smooth on its parameter
interval, including its endpoints. -/
theorem circleAngleArcPath_contDiffOn
    (c : ℂ) (R α β : ℝ) :
    ContDiffOn ℝ 2 (circleAngleArcPath c R α β).extend
      (Icc (0:ℝ) 1) := by
  have hsmooth : ContDiff ℝ 2
      (fun t : ℝ => circleMap c R (α+(β-α)*t)) := by
    exact (contDiff_circleMap c R).comp (by fun_prop)
  apply hsmooth.contDiffOn.congr
  intro t ht
  rw [(circleAngleArcPath c R α β).extend_apply ht]
  rfl

/-- The bundled circle arc integral is the corresponding angle
integral for either orientation. -/
theorem curveIntegral_circleAngleArcPath
    (f : ℂ → ℂ) (c : ℂ) (R α β : ℝ) :
    (∫ᶜ z in circleAngleArcPath c R α β, holomorphicOneForm f z) =
      ∫ θ in α..β,
        deriv (circleMap c R) θ * f (circleMap c R θ) := by
  let q : ℝ := β-α
  let g : ℝ → ℂ := fun θ =>
    deriv (circleMap c R) θ * f (circleMap c R θ)
  have hpath (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) :
      (circleAngleArcPath c R α β).extend t =
        circleMap c R (α+q*t) := by
    rw [(circleAngleArcPath c R α β).extend_apply
      (show t ∈ (Icc 0 1 : Set ℝ) from ⟨ht.1.le,ht.2.le⟩)]
    rfl
  have hderiv (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) :
      deriv (circleAngleArcPath c R α β).extend t =
        q • deriv (circleMap c R) (α+q*t) := by
    have hEq : (circleAngleArcPath c R α β).extend =ᶠ[nhds t]
        (fun x : ℝ => circleMap c R (α+q*x)) :=
      Filter.eventually_of_mem (isOpen_Ioo.mem_nhds ht) (fun x hx => hpath x hx)
    rw [hEq.deriv_eq]
    have h := (hasDerivAt_circleMap c R (α+q*t)).scomp t
      ((hasDerivAt_const_mul q).const_add α)
    simpa [Function.comp_def, deriv_circleMap, smul_eq_mul,
      mul_comm] using h.deriv
  calc
    (∫ᶜ z in circleAngleArcPath c R α β, holomorphicOneForm f z) =
        ∫ t in (0:ℝ)..1, q • g (α+q*t) := by
      rw [curveIntegral_eq_intervalIntegral_deriv]
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
      intro t ht
      simp only [holomorphicOneForm_apply]
      rw [hpath t ht, hderiv t ht]
      dsimp [g]
      simp [mul_comm, mul_left_comm]
    _ = q • ∫ t in (0:ℝ)..1, g (q*t+α) := by
      rw [intervalIntegral.integral_smul]
      simp_rw [add_comm α]
    _ = ∫ u in (0:ℝ)..q, g (u+α) := by
      simpa only [mul_zero,mul_one] using
        (intervalIntegral.smul_integral_comp_mul_left
          (f := fun u => g (u+α)) (a := 0) (b := 1) q)
    _ = ∫ θ in α..q+α, g θ := by
      simpa only [zero_add] using
        (intervalIntegral.integral_comp_add_right
          (f := g) (a := 0) (b := q) α)
    _ = ∫ θ in α..β,
          deriv (circleMap c R) θ * f (circleMap c R θ) := by
      have hendpoint : q+α = β := by dsimp [q]; ring
      rw [hendpoint]

/-- Continuity of a scalar integrand along the circle gives
continuity of its angle-parametrized one-form integrand. -/
theorem continuous_circleAngleIntegrand
    (f : ℂ → ℂ) (c : ℂ) (R : ℝ)
    (hf : ∀ θ : ℝ, ContinuousAt f (circleMap c R θ)) :
    Continuous (fun θ : ℝ =>
      deriv (circleMap c R) θ * f (circleMap c R θ)) := by
  apply continuous_iff_continuousAt.mpr
  intro θ
  have hcmap : ContinuousAt (circleMap c R) θ :=
    (by fun_prop : Continuous (circleMap c R)).continuousAt
  have hfcomp : ContinuousAt (fun t : ℝ => f (circleMap c R t)) θ :=
    (hf θ).comp hcmap
  have hderiv : ContinuousAt (fun t : ℝ => deriv (circleMap c R) t) θ := by
    simp only [deriv_circleMap]
    fun_prop
  exact hderiv.mul hfcomp

/-- Four successive clockwise circle arcs covering one full turn
have the negative of the standard counterclockwise circle integral.
The intermediate angles may be chosen to match another four-piece
contour, such as the gap stadium. -/
theorem four_circleAngleArc_curveIntegral_eq_neg_circleIntegral
    (f : ℂ → ℂ) (c : ℂ) (R α β γ δ : ℝ)
    (hf : ∀ θ : ℝ, ContinuousAt f (circleMap c R θ)) :
    ((((∫ᶜ z in circleAngleArcPath c R α β, holomorphicOneForm f z) +
       (∫ᶜ z in circleAngleArcPath c R β γ, holomorphicOneForm f z)) +
       (∫ᶜ z in circleAngleArcPath c R γ δ, holomorphicOneForm f z)) +
       (∫ᶜ z in circleAngleArcPath c R δ (α-2*Real.pi),
         holomorphicOneForm f z)) =
      -(∮ z in C(c, R), f z) := by
  let g : ℝ → ℂ := fun θ =>
    deriv (circleMap c R) θ * f (circleMap c R θ)
  have hgcont : Continuous g := continuous_circleAngleIntegrand f c R hf
  have hgint (a b : ℝ) : IntervalIntegrable g volume a b :=
    hgcont.intervalIntegrable a b
  have hgperiod : Periodic g (2*Real.pi) := by
    intro θ
    dsimp [g]
    rw [deriv_circleMap, deriv_circleMap,
      (periodic_circleMap 0 R) θ, (periodic_circleMap c R) θ]
  have hshift : (∫ θ in (α-2*Real.pi)..α, g θ) =
      ∫ θ in (0:ℝ)..2*Real.pi, g θ := by
    have h := hgperiod.intervalIntegral_add_eq (α-2*Real.pi) 0
    have ha : (α-2*Real.pi)+(2*Real.pi) = α := by ring
    simpa only [ha, zero_add] using h
  rw [curveIntegral_circleAngleArcPath,
    curveIntegral_circleAngleArcPath,
    curveIntegral_circleAngleArcPath,
    curveIntegral_circleAngleArcPath]
  change (((∫ θ in α..β, g θ) + (∫ θ in β..γ, g θ)) +
    (∫ θ in γ..δ, g θ)) + (∫ θ in δ..α-2*Real.pi, g θ) =
    -(∮ z in C(c, R), f z)
  have hsum₁ : (∫ θ in α..β, g θ) + (∫ θ in β..γ, g θ) =
      ∫ θ in α..γ, g θ :=
    integral_add_adjacent_intervals (hgint α β) (hgint β γ)
  have hsum₂ : (∫ θ in α..γ, g θ) + (∫ θ in γ..δ, g θ) =
      ∫ θ in α..δ, g θ :=
    integral_add_adjacent_intervals (hgint α γ) (hgint γ δ)
  have hsum₃ : (∫ θ in α..δ, g θ) +
      (∫ θ in δ..α-2*Real.pi, g θ) =
      ∫ θ in α..α-2*Real.pi, g θ :=
    integral_add_adjacent_intervals (hgint α δ)
      (hgint δ (α-2*Real.pi))
  rw [hsum₁, hsum₂, hsum₃, integral_symm, hshift]
  simp [circleIntegral, g, smul_eq_mul]

end NLS.ComplexAnalysis
