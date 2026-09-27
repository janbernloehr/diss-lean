import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Taylor series of Banach-valued holomorphic maps along affine lines

A complex Fréchet-holomorphic map on an open Banach domain restricts
to a holomorphic function on every sufficiently short complex affine
line. The Banach-valued Cauchy theorem then gives a convergent Taylor
series that reaches the endpoint of the line.
-/

noncomputable section
set_option maxHeartbeats 400000
open Set Metric Complex Filter Topology
open scoped ENNReal NNReal
namespace NLS.ComplexAnalysis
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The first complex-line derivative is the Fréchet derivative
applied to the line's source direction. -/
theorem fderiv_affineLine_zero (f : E → F) (c h : E)
    (hf : DifferentiableAt ℂ f c) :
    (fderiv ℂ (fun z : ℂ => f (c+z • h)) 0) 1 = (fderiv ℂ f c) h := by
  let L : ℂ →L[ℂ] E := (ContinuousLinearMap.id ℂ ℂ).smulRight h
  have hline : HasFDerivAt (fun z : ℂ => c+z • h) L 0 := by
    have hfun : (fun z : ℂ => c+z • h) = (fun z => c+L z) := by
      funext z
      simp [L]
    rw [hfun]
    exact L.hasFDerivAt.const_add c
  have hcomp : HasFDerivAt (fun z : ℂ => f (c+z • h))
      ((fderiv ℂ f c).comp L) 0 := by
    have hf0 : HasFDerivAt f (fderiv ℂ f c) (c+(0:ℂ) • h) := by
      simpa using hf.hasFDerivAt
    exact hf0.comp 0 hline
  have heq := congrArg (fun T : ℂ →L[ℂ] F => T 1) hcomp.fderiv
  simpa [L] using heq

variable [CompleteSpace F]

/-- The restriction of a holomorphic Banach-space map to a short
complex affine line has a Cauchy power series converging at `1`. -/
theorem exists_local_affineLine_cauchyTaylor (f : E → F) {S : Set E}
    (hSopen : IsOpen S) (hf : DifferentiableOn ℂ f S)
    (c : E) (hc : c ∈ S) :
    ∃ R : ℝ, 0 < R ∧ ball c R ⊆ S ∧
      ∀ h : E, ‖h‖ < R/3 →
        let g : ℂ → F := fun z => f (c+z • h)
        ∃ P : FormalMultilinearSeries ℂ ℂ F,
          HasFPowerSeriesOnBall g P 0 (2 : ℝ≥0) ∧
          P 1 (fun _ : Fin 1 => 1) = (fderiv ℂ f c) h ∧
          HasSum (fun n : ℕ => P n (fun _ : Fin n => 1)) (f (c+h)) := by
  obtain ⟨R,hR,hball⟩ := Metric.isOpen_iff.mp hSopen c hc
  refine ⟨R,hR,hball,?_⟩
  intro h hh
  let g : ℂ → F := fun z => f (c+z • h)
  have hmem (z : ℂ) (hz : z ∈ closedBall 0 2) : c+z • h ∈ S := by
    apply hball
    rw [mem_ball,dist_eq_norm,add_sub_cancel_left,norm_smul]
    have hz2 : ‖z‖ ≤ 2 := by simpa only [mem_closedBall,dist_zero_right] using hz
    calc
      ‖z‖*‖h‖ ≤ 2*‖h‖ := mul_le_mul_of_nonneg_right hz2 (norm_nonneg _)
      _ < R := by linarith
  have hg : DifferentiableOn ℂ g (closedBall 0 2) := by
    intro z hz
    have hfc : DifferentiableAt ℂ f (c+z • h) :=
      (hf _ (hmem z hz)).differentiableAt (hSopen.mem_nhds (hmem z hz))
    have hline : DifferentiableAt ℂ (fun w : ℂ => c+w • h) z := by fun_prop
    exact (hfc.comp z hline).differentiableWithinAt
  let R₂ : ℝ≥0 := 2
  have hg₂ : DifferentiableOn ℂ g (closedBall 0 R₂) := by
    simpa only [R₂, NNReal.coe_ofNat] using hg
  have hp : HasFPowerSeriesOnBall g (cauchyPowerSeries g 0 R₂) 0 R₂ :=
    hg₂.hasFPowerSeriesOnBall (by norm_num : (0 : ℝ≥0) < R₂)
  let P : FormalMultilinearSeries ℂ ℂ F := cauchyPowerSeries g 0 R₂
  refine ⟨P,?_,?_,?_⟩
  · simpa only [P,R₂] using hp
  · have hfc : DifferentiableAt ℂ f c :=
      (hf c hc).differentiableAt (hSopen.mem_nhds hc)
    have hcoef := congrArg (fun T : ℂ →L[ℂ] F => T 1)
      hp.hasFPowerSeriesAt.fderiv_eq
    have hfirst : P 1 (fun _ : Fin 1 => 1) = (fderiv ℂ g 0) 1 := by
      simpa only [P,continuousMultilinearCurryFin1_apply,Fin.snoc_zero] using hcoef.symm
    calc
      P 1 (fun _ : Fin 1 => 1) = (fderiv ℂ g 0) 1 := hfirst
      _ = (fderiv ℂ f c) h := fderiv_affineLine_zero f c h hfc
  · have h1 : (1 : ℂ) ∈ Metric.eball 0 (R₂ : ℝ≥0∞) := by
      norm_num [R₂]
    have hs : HasSum (fun n : ℕ => P n (fun _ : Fin n => 1)) (g 1) := by
      simpa only [zero_add,P] using (hp.hasSum (y := 1) h1)
    have heq : g 1 = f (c+h) := by simp [g]
    rw [← heq]
    exact hs

end NLS.ComplexAnalysis
