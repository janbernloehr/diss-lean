import NLS.ComplexAnalysis.BanachTaylorBounds
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Continuous derivatives of Banach-space holomorphic maps

The complex Schwarz bound and the convex mean-value inequality give a
local Lipschitz estimate for the Fréchet derivative. In particular,
complex differentiability on an open Banach-space domain implies `C¹`.
-/

noncomputable section
open Set Metric Topology
open scoped ContDiff NNReal
namespace NLS.ComplexAnalysis

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- A bounded holomorphic map has a locally Lipschitz Fréchet derivative.
The fourfold outer radius leaves room for a translated difference
quotient and a mean-value bound. -/
theorem norm_fderiv_sub_le_of_holomorphic_ball_bound
    (f : E → F) (c : E) (R M : ℝ) (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball c (4*R)))
    (hb : ∀ z ∈ ball c (4*R), ‖f z‖ ≤ M)
    {x y : E} (hx : x ∈ ball c R) (hy : y ∈ ball c R) :
    ‖fderiv ℂ f y - fderiv ℂ f x‖ ≤ (4*M/R^2)*‖y-x‖ := by
  have houter : 3*R+R = 4*R := by ring
  have hf' : DifferentiableOn ℂ f (ball c (3*R+R)) := by
    simpa only [houter] using hf
  have hb' : ∀ z ∈ ball c (3*R+R), ‖f z‖ ≤ M := by
    simpa only [houter] using hb
  have hder (w : E) (hw : w ∈ ball c (3*R)) :
      ‖fderiv ℂ f w‖ ≤ 2*M/R :=
    norm_fderiv_le_of_ball_bound f c w (3*R) R M hR hf' hb' hw
  have hinside (w : E) (hw : w ∈ ball c R)
      (z : E) (hz : z ∈ ball 0 R) : w+z ∈ ball c (3*R) := by
    rw [mem_ball,dist_eq_norm]
    have hw' : ‖w-c‖ < R := by simpa only [mem_ball,dist_eq_norm] using hw
    have hz' : ‖z‖ < R := by simpa only [mem_ball,dist_zero_right] using hz
    calc
      ‖w+z-c‖ = ‖(w-c)+z‖ := by congr 1; abel
      _ ≤ ‖w-c‖+‖z‖ := norm_add_le _ _
      _ < 3*R := by linarith
  have hsmall : ball c (3*R) ⊆ ball c (4*R) :=
    ball_subset_ball (by linarith)
  have hAt (w : E) (hw : w ∈ ball c (3*R)) : DifferentiableAt ℂ f w :=
    (hf w (hsmall hw)).differentiableAt
      (isOpen_ball.mem_nhds (hsmall hw))
  have hmv (z : E) (hz : z ∈ ball 0 R) :
      ‖f (y+z)-f (x+z)‖ ≤ (2*M/R)*‖y-x‖ := by
    have h := (convex_ball c (3*R)).norm_image_sub_le_of_norm_fderiv_le
      hAt hder (hinside x hx z hz) (hinside y hy z hz)
    simpa only [add_sub_add_right_eq_sub] using h
  let g : E → F := fun z => f (y+z)-f (x+z)
  have hgDiff : DifferentiableOn ℂ g (ball 0 R) := by
    intro z hz
    have hyz := hAt (y+z) (hinside y hy z hz)
    have hxz := hAt (x+z) (hinside x hx z hz)
    exact (((differentiableAt_comp_add_left y).2 hyz).sub
      ((differentiableAt_comp_add_left x).2 hxz)).differentiableWithinAt
  have hmap : MapsTo g (ball 0 R)
      (closedBall (g 0) (2*(2*M/R)*‖y-x‖)) := by
    intro z hz
    rw [mem_closedBall,dist_eq_norm]
    calc
      ‖g z-g 0‖ ≤ ‖f (y+z)-f (x+z)‖+‖f y-f x‖ := by
        simpa only [g,add_zero] using
          (norm_sub_le (f (y+z)-f (x+z)) (f y-f x))
      _ ≤ (2*M/R)*‖y-x‖+(2*M/R)*‖y-x‖ :=
        add_le_add (hmv z hz) (by simpa using hmv 0 (mem_ball_self hR))
      _ = 2*(2*M/R)*‖y-x‖ := by ring
  have hg0 : fderiv ℂ g 0 = fderiv ℂ f y-fderiv ℂ f x := by
    have hfy : DifferentiableAt ℂ (fun z => f (y+z)) 0 :=
      (differentiableAt_comp_add_left y).2 (by
        simpa only [add_zero] using hAt y
          ((ball_subset_ball (by linarith : R ≤ 3*R)) hy))
    have hfx : DifferentiableAt ℂ (fun z => f (x+z)) 0 :=
      (differentiableAt_comp_add_left x).2 (by
        simpa only [add_zero] using hAt x
          ((ball_subset_ball (by linarith : R ≤ 3*R)) hx))
    change fderiv ℂ ((fun z => f (y+z))-(fun z => f (x+z))) 0 = _
    rw [fderiv_sub hfy hfx]
    simp only [fderiv_comp_add_left, add_zero]
  have hschwarz := Complex.norm_fderiv_le_div_of_mapsTo_ball
    hgDiff hmap hR
  rw [hg0] at hschwarz
  calc
    ‖fderiv ℂ f y-fderiv ℂ f x‖ ≤
        (2*(2*M/R)*‖y-x‖)/R := hschwarz
    _ = (4*M/R^2)*‖y-x‖ := by field_simp; ring

/-- A complex-differentiable Banach-valued map on an open Banach-space
domain has a continuous Fréchet derivative. -/
theorem contDiffOn_one_of_differentiableOn
    (f : E → F) {S : Set E} (hS : IsOpen S)
    (hf : DifferentiableOn ℂ f S) : ContDiffOn ℂ 1 f S := by
  have hderCont : ContinuousOn (fderiv ℂ f) S := by
    intro c hc
    obtain ⟨R₀,hR₀,hSball⟩ := Metric.isOpen_iff.mp hS c hc
    have hfc : ContinuousAt f c :=
      ((hf c hc).differentiableAt (hS.mem_nhds hc)).continuousAt
    obtain ⟨R₁,hR₁,hFball⟩ := Metric.mem_nhds_iff.mp
      (hfc (ball_mem_nhds (f c) (by norm_num : (0 : ℝ) < 1)))
    let R : ℝ := min R₀ R₁ / 4
    have hR : 0 < R := by dsimp [R]; positivity
    have hR4 : 4*R = min R₀ R₁ := by dsimp [R]; ring
    have hball : ball c (4*R) ⊆ S := by
      apply (ball_subset_ball ?_).trans hSball
      rw [hR4]
      exact min_le_left _ _
    let M : ℝ := ‖f c‖+1
    have hM : 0 ≤ M := by dsimp [M]; positivity
    have hbound : ∀ z ∈ ball c (4*R), ‖f z‖ ≤ M := by
      intro z hz
      have hzF : ‖f z-f c‖ < 1 := by
        have hzB : z ∈ ball c R₁ :=
          (ball_subset_ball (by rw [hR4]; exact min_le_right _ _)) hz
        simpa only [Set.mem_preimage,mem_ball,dist_eq_norm] using hFball hzB
      have h := norm_le_norm_sub_add (f z) (f c)
      dsimp [M]
      linarith
    let K : ℝ≥0 := ⟨4*M/R^2,by positivity⟩
    have hLip : LipschitzOnWith K (fderiv ℂ f) (ball c R) := by
      rw [lipschitzOnWith_iff_norm_sub_le]
      intro x hx y hy
      have h := norm_fderiv_sub_le_of_holomorphic_ball_bound
        f c R M hR (hf.mono hball) hbound hx hy
      change ‖fderiv ℂ f x-fderiv ℂ f y‖ ≤
        (4*M/R^2)*‖x-y‖
      simpa only [norm_sub_rev] using h
    exact ((hLip.continuousOn c (mem_ball_self hR)).continuousAt
      (isOpen_ball.mem_nhds (mem_ball_self hR))).continuousWithinAt
  have hC1 := (contDiffOn_succ_iff_fderiv_of_isOpen
    (n := (0 : ℕ∞ω)) hS).2
      ⟨hf,by simp,contDiffOn_zero.mpr hderCont⟩
  simpa only [zero_add] using hC1

end NLS.ComplexAnalysis
