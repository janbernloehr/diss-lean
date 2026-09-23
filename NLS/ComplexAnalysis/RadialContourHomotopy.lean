import NLS.ComplexAnalysis.CircleCurveIntegral
import Mathlib.Topology.Homotopy.Affine

/-!
# Smooth polar contours and radial homotopy

A positive periodic radius defines a closed polar path. Its affine
homotopy with a concentric circle remains outside every smaller disc
whose radius is below both endpoint radii. The homotopy is smooth when
the radius is twice continuously differentiable.
-/

noncomputable section
open Set Metric Complex
open scoped unitInterval

namespace NLS.ComplexAnalysis

/-- A polar graph, counterclockwise as its angle increases. -/
def radialPath (c : ℂ) (ρ : ℝ → ℝ)
    (hρcont : Continuous ρ)
    (hperiod : ρ (2 * Real.pi) = ρ 0) :
    Path (circleMap c (ρ 0) 0) (circleMap c (ρ 0) 0) :=
  Path.ofLine
    (f := fun t : ℝ => circleMap c (ρ ((2 * Real.pi) * t)) ((2 * Real.pi) * t))
    (by
      have h : Continuous (fun t : ℝ => circleMap c (ρ ((2 * Real.pi) * t)) ((2 * Real.pi) * t)) := by
        simp only [circleMap]
        fun_prop
      exact h.continuousOn)
    (by simp)
    (by
      simpa [hperiod] using (periodic_circleMap c (ρ 0)) 0)

private theorem radialHomotopy_raw_contDiff (c : ℂ) (R : ℝ)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ 2 ρ) :
    ContDiff ℝ 2 (fun xy : ℝ × ℝ =>
      (1-xy.1) • circleMap c R ((2*Real.pi)*xy.2) +
        xy.1 • circleMap c (ρ ((2*Real.pi)*xy.2)) ((2*Real.pi)*xy.2)) := by
  have hθ : ContDiff ℝ 2 (fun xy : ℝ × ℝ => (2*Real.pi)*xy.2) := by fun_prop
  have hθc : ContDiff ℝ 2 (fun xy : ℝ × ℝ => (((2*Real.pi)*xy.2 : ℝ) : ℂ)) := by
    simpa only [Function.comp_def, Complex.ofRealCLM_apply] using
      (Complex.ofRealCLM.contDiff.comp hθ)
  have hρxy : ContDiff ℝ 2 (fun xy : ℝ × ℝ => ρ ((2*Real.pi)*xy.2)) :=
    hρ.comp hθ
  have hρc : ContDiff ℝ 2
      (fun xy : ℝ × ℝ => (ρ ((2*Real.pi)*xy.2) : ℂ)) := by
    simpa only [Function.comp_def, Complex.ofRealCLM_apply] using
      (Complex.ofRealCLM.contDiff.comp hρxy)
  simp only [circleMap]
  fun_prop (discharger := assumption)

/-- The affine deformation from a circle to a polar graph. -/
def radialHomotopy (c : ℂ) (R : ℝ) (ρ : ℝ → ℝ)
    (hρcont : Continuous ρ) (hperiod : ρ (2*Real.pi) = ρ 0) :
    (circlePath c R : C(unitInterval, ℂ)).Homotopy
      (radialPath c ρ hρcont hperiod : C(unitInterval, ℂ)) :=
  ContinuousMap.Homotopy.affine _ _

private theorem lineMap_circleMap (c : ℂ) (R r θ s : ℝ) :
    AffineMap.lineMap (circleMap c R θ) (circleMap c r θ) s =
      circleMap c ((1-s)*R+s*r) θ := by
  simp [AffineMap.lineMap_apply, circleMap, vsub_eq_sub, vadd_eq_add]
  ring

theorem radialHomotopy_apply (c : ℂ) (R : ℝ) (ρ : ℝ → ℝ)
    (hρcont : Continuous ρ) (hperiod : ρ (2*Real.pi) = ρ 0)
    (s u : unitInterval) :
    radialHomotopy c R ρ hρcont hperiod (s, u) =
      circleMap c ((1-(s:ℝ))*R+(s:ℝ)*ρ ((2*Real.pi)*(u:ℝ)))
        ((2*Real.pi)*(u:ℝ)) := by
  rw [radialHomotopy, ContinuousMap.Homotopy.affine_apply]
  change AffineMap.lineMap
    (circleMap c R ((2*Real.pi)*(u:ℝ)))
    (circleMap c (ρ ((2*Real.pi)*(u:ℝ))) ((2*Real.pi)*(u:ℝ))) (s:ℝ) = _
  exact lineMap_circleMap c R _ _ _

theorem radialHomotopy_loop (c : ℂ) (R : ℝ) (ρ : ℝ → ℝ)
    (hρcont : Continuous ρ) (hperiod : ρ (2*Real.pi) = ρ 0)
    (s : unitInterval) :
    radialHomotopy c R ρ hρcont hperiod (s, 1) =
      radialHomotopy c R ρ hρcont hperiod (s, 0) := by
  rw [radialHomotopy_apply, radialHomotopy_apply]
  simp only [show ((1 : unitInterval) : ℝ) = 1 by rfl,
    show ((0 : unitInterval) : ℝ) = 0 by rfl, mul_one, mul_zero]
  rw [hperiod]
  simpa using (periodic_circleMap c ((1-(s:ℝ))*R+(s:ℝ)*ρ 0) 0)

theorem radialHomotopy_contDiffOn (c : ℂ) (R : ℝ) (ρ : ℝ → ℝ)
    (hρcont : Continuous ρ) (hperiod : ρ (2*Real.pi) = ρ 0)
    (hρ : ContDiff ℝ 2 ρ) :
    ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ => Set.IccExtend zero_le_one
        ((radialHomotopy c R ρ hρcont hperiod).extend xy.1) xy.2)
      (Icc 0 1) := by
  apply (radialHomotopy_raw_contDiff c R ρ hρ).contDiffOn.congr
  intro xy hxy
  have hs : xy.1 ∈ (Icc 0 1 : Set ℝ) := ⟨hxy.1.1, hxy.2.1⟩
  have hu : xy.2 ∈ (Icc 0 1 : Set ℝ) := ⟨hxy.1.2, hxy.2.2⟩
  rw [Set.IccExtend_of_mem zero_le_one _ hu]
  rw [(radialHomotopy c R ρ hρcont hperiod).extend_apply_of_mem_I hs]
  rw [radialHomotopy, ContinuousMap.Homotopy.affine_apply]
  change AffineMap.lineMap
    (circleMap c R ((2*Real.pi)*xy.2))
    (circleMap c (ρ ((2*Real.pi)*xy.2)) ((2*Real.pi)*xy.2)) xy.1 =
      (1-xy.1) • circleMap c R ((2*Real.pi)*xy.2) +
        xy.1 • circleMap c (ρ ((2*Real.pi)*xy.2)) ((2*Real.pi)*xy.2)
  simp [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
  ring

/-- Every intermediate polar loop stays outside a smaller closed disc
when both endpoint radii are uniformly larger. -/
theorem radialHomotopy_disjoint_closedBall (c : ℂ) (R r₀ : ℝ)
    (ρ : ℝ → ℝ) (hρcont : Continuous ρ)
    (hperiod : ρ (2*Real.pi) = ρ 0)
    (hr₀ : 0 ≤ r₀) (hrR : r₀ < R)
    (hρlo : ∀ θ ∈ Icc (0:ℝ) (2*Real.pi), r₀ < ρ θ)
    (s u : unitInterval) :
    radialHomotopy c R ρ hρcont hperiod (s, u) ∉ closedBall c r₀ := by
  let θ : ℝ := (2*Real.pi)*(u:ℝ)
  have hs₀ : 0 ≤ (s:ℝ) := s.property.1
  have hs₁ : (s:ℝ) ≤ 1 := s.property.2
  have hu₀ : 0 ≤ (u:ℝ) := u.property.1
  have hu₁ : (u:ℝ) ≤ 1 := u.property.2
  have hq : 0 < 2*Real.pi := by positivity
  have hθ : θ ∈ Icc (0:ℝ) (2*Real.pi) := by
    dsimp [θ]
    constructor
    · exact mul_nonneg hq.le hu₀
    · nlinarith [mul_nonneg hq.le (sub_nonneg.mpr hu₁)]
  have hρu : r₀ < ρ θ := hρlo θ hθ
  have hrad : r₀ < (1-(s:ℝ))*R+(s:ℝ)*ρ θ := by
    by_cases hs : (s:ℝ) = 0
    · simp [hs, hrR]
    · have hsp : 0 < (s:ℝ) := lt_of_le_of_ne hs₀ (Ne.symm hs)
      have hleft := mul_le_mul_of_nonneg_left hrR.le (sub_nonneg.mpr hs₁)
      have hright := mul_lt_mul_of_pos_left hρu hsp
      nlinarith
  have hradpos : 0 < (1-(s:ℝ))*R+(s:ℝ)*ρ θ := lt_of_le_of_lt hr₀ hrad
  rw [radialHomotopy_apply]
  intro hmem
  have hdist : dist
      (circleMap c ((1-(s:ℝ))*R+(s:ℝ)*ρ θ) θ) c =
        (1-(s:ℝ))*R+(s:ℝ)*ρ θ := by
    rw [dist_eq_norm, circleMap_sub_center, norm_circleMap_zero,
      abs_of_pos hradpos]
  have := (mem_closedBall.mp hmem)
  rw [hdist] at this
  exact (not_le.mpr hrad) this

/-- The affine polar homotopy stays inside a common outer closed disc. -/
theorem radialHomotopy_mem_closedBall (c : ℂ) (R Rmax : ℝ)
    (ρ : ℝ → ℝ) (hρcont : Continuous ρ)
    (hperiod : ρ (2*Real.pi) = ρ 0)
    (hR0 : 0 ≤ R) (hRmax : R ≤ Rmax)
    (hρbounds : ∀ θ ∈ Icc (0:ℝ) (2*Real.pi),
      0 ≤ ρ θ ∧ ρ θ ≤ Rmax)
    (s u : unitInterval) :
    radialHomotopy c R ρ hρcont hperiod (s,u) ∈ closedBall c Rmax := by
  let θ : ℝ := (2*Real.pi)*(u:ℝ)
  have hs0 : 0 ≤ (s:ℝ) := s.property.1
  have hs1 : (s:ℝ) ≤ 1 := s.property.2
  have hu0 : 0 ≤ (u:ℝ) := u.property.1
  have hu1 : (u:ℝ) ≤ 1 := u.property.2
  have hq : 0 < 2*Real.pi := by positivity
  have hθ : θ ∈ Icc (0:ℝ) (2*Real.pi) := by
    dsimp [θ]
    constructor
    · exact mul_nonneg hq.le hu0
    · nlinarith [mul_nonneg hq.le (sub_nonneg.mpr hu1)]
  obtain ⟨hρ0,hρmax⟩ := hρbounds θ hθ
  let rad : ℝ := (1-(s:ℝ))*R+(s:ℝ)*ρ θ
  have hrad0 : 0 ≤ rad := by
    dsimp [rad]
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr hs1) hR0)
      (mul_nonneg hs0 hρ0)
  have hradmax : rad ≤ Rmax := by
    have hleft := mul_le_mul_of_nonneg_left hRmax (sub_nonneg.mpr hs1)
    have hright := mul_le_mul_of_nonneg_left hρmax hs0
    dsimp [rad]
    nlinarith
  rw [radialHomotopy_apply]
  exact (closedBall_subset_closedBall hradmax)
    (circleMap_mem_closedBall c hrad0 θ)

end NLS.ComplexAnalysis
