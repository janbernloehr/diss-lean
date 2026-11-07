import NLS.ZakharovShabat.DiscriminantNonlocalSignCounterexample
import NLS.ZakharovShabat.L2WholeLineDiscriminantXiIntegral
import NLS.ZakharovShabat.L2GradientComparison
import NLS.ZakharovShabat.SourcePhysicalL2Equiv

/-! # The printed plus-sign obstruction on the original periodic L2 space

Every unit-interval continuous profile determines an original periodic L2
source. Its actual whole-line gradient agrees with the classical Fréchet
gradient in the interior. The counterexample therefore refutes even the
almost-everywhere reading in the original source space, not merely a
pointwise formula for an auxiliary smooth ODE.
-/
noncomputable section
open Set Complex MeasureTheory Filter Topology NLS.LinearVolterra
namespace NLS.ZakharovShabat

def l2WholeLinePrintedDiscriminantXi (u : IntervalPairL2) (z : ℂ) (x : ℝ) : ℂ :=
  (l2Monodromy u z) 0 0-(l2Monodromy u z) 1 1+
    2*I*∫ t in (0:ℝ)..x,
      (I*(l2WholeLinePotential u t).1)*(l2WholeLineDiscriminantGradient u z t).1+
      (-I*(l2WholeLinePotential u t).2)*(l2WholeLineDiscriminantGradient u z t).2

theorem l2WholeLineDiscriminantGradient_of_continuous (Φ : Curve (ℂ × ℂ)) (z : ℂ)
    (t : Icc (0:ℝ) 1) :
    l2WholeLineDiscriminantGradient (continuousPotentialL2Class Φ) z t =
      classicalDiscriminantGradient Φ z t := by
  rw [l2WholeLineDiscriminantGradient_on_unit,l2DiscriminantGradient_of_continuous]

theorem l2WholeLinePrintedDiscriminantXi_of_continuous (Φ : Curve (ℂ × ℂ)) (z : ℂ)
    (t : Icc (0:ℝ) 1) :
    l2WholeLinePrintedDiscriminantXi (continuousPotentialL2Class Φ) z t =
      classicalPrintedDiscriminantXi Φ z t := by
  unfold l2WholeLinePrintedDiscriminantXi classicalPrintedDiscriminantXi
  rw [l2Monodromy_of_continuous]
  congr 2
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le t.property.1]
  have hp := (l2WholeLinePotential_ae_unit (continuousPotentialL2Class Φ)).trans
    (continuousPotentialL2Class_representative Φ)
  have hp' := ae_restrict_of_ae_restrict_of_subset
    (Ioc_subset_Ioc_right t.property.2) hp
  filter_upwards [hp',ae_restrict_mem measurableSet_Ioc] with x hx hmem
  have hxt : x ∈ Icc (0:ℝ) 1 := ⟨hmem.1.le,hmem.2.trans t.property.2⟩
  have hg := l2WholeLineDiscriminantGradient_of_continuous Φ z ⟨x,hxt⟩
  rw [hx,hg]
  rfl

theorem printed_nonlocal_spatial_equation_false_original_L2 :
    ¬ (∀ᵐ x ∂volume.restrict (Ioc (0:ℝ) 1),
      HasDerivAt (l2WholeLineDiscriminantGradient (continuousPotentialL2Class classicalRationalPotential) 0)
        (l2WholeLinePrintedDiscriminantXi (continuousPotentialL2Class classicalRationalPotential) 0 x*
          (l2WholeLinePotential (continuousPotentialL2Class classicalRationalPotential) x).2,
         -l2WholeLinePrintedDiscriminantXi (continuousPotentialL2Class classicalRationalPotential) 0 x*
          (l2WholeLinePotential (continuousPotentialL2Class classicalRationalPotential) x).1) x) := by
  intro h
  apply printed_nonlocal_spatial_equation_false_ae
  have hp := (l2WholeLinePotential_ae_unit (continuousPotentialL2Class classicalRationalPotential)).trans
    (continuousPotentialL2Class_representative classicalRationalPotential)
  filter_upwards [h,hp,ae_restrict_mem measurableSet_Ioc,
    (show ∀ᵐ x ∂volume.restrict (Ioc (0:ℝ) 1), x ≠ 1 by
      exact ae_restrict_of_ae (by simp [ae_iff]))] with x hx hpx hmem hx1
  have hxi : x ∈ Ioo (0:ℝ) 1 := ⟨hmem.1,lt_of_le_of_ne hmem.2 hx1⟩
  have he : classicalDiscriminantGradient classicalRationalPotential 0 =ᶠ[𝓝 x]
      l2WholeLineDiscriminantGradient (continuousPotentialL2Class classicalRationalPotential) 0 := by
    filter_upwards [Ioo_mem_nhds hxi.1 hxi.2] with y hy
    exact (l2WholeLineDiscriminantGradient_of_continuous classicalRationalPotential 0
      ⟨y,hy.1.le,hy.2.le⟩).symm
  have hc := hx.congr_of_eventuallyEq he
  have hpXi := l2WholeLinePrintedDiscriminantXi_of_continuous classicalRationalPotential 0
    ⟨x,hmem.1.le,hmem.2⟩
  rw [hpXi,hpx] at hc
  exact hc

/-- A literal original complex H0 Fourier source is a counterexample.
There is no finite-dimensional, smooth, or prescribed-gradient assumption. -/
theorem exists_original_source_printed_nonlocal_sign_false :
    ∃ φ : CoeffPair 2,
      ¬ (∀ᵐ x ∂volume.restrict (Ioc (0:ℝ) 1),
        HasDerivAt (l2WholeLineDiscriminantGradient (sourcePhysicalL2 φ) 0)
          (l2WholeLinePrintedDiscriminantXi (sourcePhysicalL2 φ) 0 x*(l2WholeLinePotential (sourcePhysicalL2 φ) x).2,
           -l2WholeLinePrintedDiscriminantXi (sourcePhysicalL2 φ) 0 x*(l2WholeLinePotential (sourcePhysicalL2 φ) x).1) x) := by
  refine ⟨sourcePhysicalL2Equiv.symm (continuousPotentialL2Class classicalRationalPotential),?_⟩
  simpa only [sourcePhysicalL2_equiv_symm] using printed_nonlocal_spatial_equation_false_original_L2

end NLS.ZakharovShabat
