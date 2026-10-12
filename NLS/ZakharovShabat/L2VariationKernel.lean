import NLS.ZakharovShabat.L2KernelPairing
import NLS.ZakharovShabat.ClassicalForcedKernel

/-! # Variation of constants for arbitrary physical L2 potentials

The two homogeneous columns have determinant one. Their adjugate
transports the rough potential forcing to constant coordinates.
The identity extends from continuous inputs in the uniform curve norm.
-/
noncomputable section
open Set Complex MeasureTheory
open NLS.LinearVolterra
namespace NLS.ZakharovShabat

/-- The explicit fundamental-matrix kernel for a potential perturbation. -/
def l2PotentialKernelCurve (u h : IntervalPairL2) (z : ℂ) (v : ℂ × ℂ) : Curve (ℂ × ℂ) :=
  l2KernelPairing h (l2SolutionCurve u z (0,1)) (l2SolutionCurve u z v) • l2SolutionCurve u z (1,0)-
  l2KernelPairing h (l2SolutionCurve u z (1,0)) (l2SolutionCurve u z v) • l2SolutionCurve u z (0,1)

theorem continuous_l2PotentialKernelCurve (z : ℂ) (v : ℂ × ℂ) :
    Continuous (fun p : IntervalPairL2 × IntervalPairL2 => l2PotentialKernelCurve p.1 p.2 z v) := by
  have hc (x : ℂ × ℂ) : Continuous (fun p : IntervalPairL2 × IntervalPairL2 => l2SolutionCurve p.1 z x) := by
    have hp : Continuous (fun p : IntervalPairL2 × IntervalPairL2 => (z,p.1)) :=
      continuous_const.prodMk continuous_fst
    have h := (continuous_l2SolutionCurve_joint x).comp hp
    exact h
  have hk (x : ℂ × ℂ) : Continuous (fun p : IntervalPairL2 × IntervalPairL2 =>
      l2KernelPairing p.2 (l2SolutionCurve p.1 z x) (l2SolutionCurve p.1 z v)) := by
    have hp : Continuous (fun p : IntervalPairL2 × IntervalPairL2 =>
        (p.2,(l2SolutionCurve p.1 z x,l2SolutionCurve p.1 z v))) :=
      continuous_snd.prodMk ((hc x).prodMk (hc v))
    have h := continuous_l2KernelPairing.comp hp
    exact h
  apply ContinuousMap.continuous_of_continuous_uncurry
  have he (x : ℂ × ℂ) : Continuous (fun p : (IntervalPairL2 × IntervalPairL2) × Icc (0 : ℝ) 1 =>
      l2SolutionCurve p.1.1 z x p.2) :=
    continuous_eval.comp (((hc x).comp continuous_fst).prodMk continuous_snd)
  have hi (x : ℂ × ℂ) : Continuous (fun p : (IntervalPairL2 × IntervalPairL2) × Icc (0 : ℝ) 1 =>
      l2KernelPairing p.1.2 (l2SolutionCurve p.1.1 z x) (l2SolutionCurve p.1.1 z v) p.2) :=
    continuous_eval.comp (((hk x).comp continuous_fst).prodMk continuous_snd)
  exact ((hi (0,1)).smul (he (1,0))).sub ((hi (1,0)).smul (he (0,1)))

/-- Continuous inputs recover the original adjugate kernel exactly. -/
theorem l2PotentialKernelCurve_of_continuous (Φ H : Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ) :
    l2PotentialKernelCurve (continuousPotentialL2Class Φ) (continuousPotentialL2Class H) z v =
      classicalPotentialVariationCurve Φ H z v := by
  let g := classicalPotentialVariationSource Φ H z v
  apply ContinuousMap.ext
  intro t
  have hi := (continuous_classicalForcedKernelIntegrand Φ g z).intervalIntegrable (μ := volume) 0 t.val
  have hcoord : classicalForcedKernelPrimitive Φ g z t =
      (l2KernelPairing (continuousPotentialL2Class H) (classicalSolutionCurve Φ z (0,1))
         (classicalSolutionCurve Φ z v) t,
       -l2KernelPairing (continuousPotentialL2Class H) (classicalSolutionCurve Φ z (1,0))
         (classicalSolutionCurve Φ z v) t) := by
    apply Prod.ext
    · dsimp only [Prod.fst,Prod.snd]
      change (∫ s in (0 : ℝ)..t.val, classicalForcedKernelIntegrand Φ g z s).1 = _
      have he := (ContinuousLinearMap.fst ℂ ℂ ℂ).intervalIntegral_comp_comm hi
      simp only [ContinuousLinearMap.coe_fst'] at he
      rw [← he,l2KernelPairing_of_continuous]
      apply intervalIntegral.integral_congr
      intro s hs
      have hs0 : s ∈ Icc (0 : ℝ) t.val := by simpa only [uIcc_of_le t.property.1] using hs
      have hs' : s ∈ Icc (0 : ℝ) 1 := ⟨hs0.1,hs0.2.trans t.property.2⟩
      simp only [classicalForcedKernelIntegrand,g,NLS.LinearVolterra.extend,projIcc_of_mem _ hs',
        classicalPotentialVariationSource_apply,classicalSolutionCurve_apply]
      ring
    · dsimp only [Prod.fst,Prod.snd]
      change (∫ s in (0 : ℝ)..t.val, classicalForcedKernelIntegrand Φ g z s).2 = _
      have he := (ContinuousLinearMap.snd ℂ ℂ ℂ).intervalIntegral_comp_comm hi
      simp only [ContinuousLinearMap.coe_snd'] at he
      rw [← he,l2KernelPairing_of_continuous,← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_congr
      intro s hs
      have hs0 : s ∈ Icc (0 : ℝ) t.val := by simpa only [uIcc_of_le t.property.1] using hs
      have hs' : s ∈ Icc (0 : ℝ) 1 := ⟨hs0.1,hs0.2.trans t.property.2⟩
      simp only [classicalForcedKernelIntegrand,g,NLS.LinearVolterra.extend,projIcc_of_mem _ hs',
        classicalPotentialVariationSource_apply,classicalSolutionCurve_apply]
      ring
  change _ = forcedSolutionCurve (classicalCoefficientCurveCLM (z,Φ)) g 0 t
  rw [← forcedSolution_coe,← classicalForcedKernelSolution_eq_forcedSolution Φ g z t,
    classicalForcedKernelSolution,hcoord]
  simp only [l2PotentialKernelCurve,l2SolutionCurve_of_continuous]
  change (l2KernelPairing (continuousPotentialL2Class H) (classicalSolutionCurve Φ z (0,1))
      (classicalSolutionCurve Φ z v) t) • classicalSolutionCurve Φ z (1,0) t-
    (l2KernelPairing (continuousPotentialL2Class H) (classicalSolutionCurve Φ z (1,0))
      (classicalSolutionCurve Φ z v) t) • classicalSolutionCurve Φ z (0,1) t = _
  rw [classicalSolutionCurve_apply,classicalSolutionCurve_apply,neg_smul,sub_eq_add_neg]

/-- The explicit kernel is the actual derivative at every rough physical L2 input. -/
theorem l2PotentialKernelCurve_eq_variation (u h : IntervalPairL2) (z : ℂ) (v : ℂ × ℂ) :
    l2PotentialKernelCurve u h z v = l2VariationCurve (z,u) (0,h) v := by
  have hc : Continuous (fun p : IntervalPairL2 × IntervalPairL2 => l2VariationCurve (z,p.1) (0,p.2) v) := by
    have hp : Continuous (fun p : IntervalPairL2 × IntervalPairL2 => ((z,p.1),((0 : ℂ),p.2))) :=
      (continuous_const.prodMk continuous_fst).prodMk (continuous_const.prodMk continuous_snd)
    have hh := (continuous_l2VariationCurve v).comp hp
    exact hh
  have he := (denseRange_continuousPotentialL2Class.prodMap denseRange_continuousPotentialL2Class).equalizer
    (continuous_l2PotentialKernelCurve z v) hc (by
      funext p
      exact (l2PotentialKernelCurve_of_continuous p.1 p.2 z v).trans
        (l2PotentialVariation_of_continuous p.1 p.2 z v).symm)
  exact congrFun he (u,h)

theorem fderiv_l2SolutionCurve_potential_eq_kernel (u h : IntervalPairL2) (z : ℂ) (v : ℂ × ℂ) :
    (fderiv ℂ (fun w : IntervalPairL2 => l2SolutionCurve w z v) u) h =
      l2PotentialKernelCurve u h z v := by
  rw [fderiv_l2SolutionCurve_potential,l2PotentialKernelCurve_eq_variation]

end NLS.ZakharovShabat
