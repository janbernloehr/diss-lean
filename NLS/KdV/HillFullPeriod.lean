import NLS.KdV.HillClassicalIdentification
import NLS.FunctionalAnalysis.AbsoluteContinuityTranslation
import Mathlib.MeasureTheory.Group.Measure

/-! # Full-period endpoint comparison for the physical Hill operator

The two actual unit-interval scalar flows propagate a periodic H2
eigenvector through the full period. Its initial state is nonzero whenever
the domain vector is nonzero. No spectral labels or multiplicities are
assumed in this comparison.
-/

noncomputable section
open Set Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.FunctionalAnalysis
namespace NLS.KdV

def hillPhysicalState (f : HillSobolevDomain) (x : ℝ) : ℂ × ℂ :=
  (hillRepresentative f (x : AddCircle (2 : ℝ)), hillDerivativeRepresentative f (x : AddCircle (2 : ℝ)))

def hillSecondPotentialCurve (Q : C(AddCircle (2 : ℝ), ℂ)) : Curve ℂ :=
  ⟨fun t => Q (((t : ℝ)+1 : ℝ) : AddCircle (2 : ℝ)), by fun_prop⟩

private theorem ae_second_unit_of_ae_two {P : ℝ → Prop}
    (h : ∀ᵐ x : ℝ ∂volume.restrict (Ioc 0 2), P x) :
    ∀ᵐ x : ℝ, x ∈ Icc (0 : ℝ) 1 → P (x+1) := by
  rw [ae_restrict_iff' measurableSet_Ioc] at h
  have ht := (measurePreserving_add_right (volume : Measure ℝ) 1).quasiMeasurePreserving.ae h
  filter_upwards [ht] with x hx
  intro hxi
  exact hx ⟨by linarith [hxi.1], by linarith [hxi.2]⟩

theorem physicalHillEigenvector_secondFlow (Q : C(AddCircle (2 : ℝ), ℂ))
    (lambda : ℂ) (f : HillSobolevDomain)
    (he : physicalHillOperator (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ Q) f =
      lambda • ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ (hillRepresentative f)) :
    EqOn (fun x => hillPhysicalState f (x+1))
      (classicalHillFlow (hillSecondPotentialCurve Q) lambda (hillPhysicalState f 1)) (Icc 0 1) := by
  let F := fun x : ℝ => hillRepresentative f (x : AddCircle (2 : ℝ))
  let G := fun x : ℝ => hillDerivativeRepresentative f (x : AddCircle (2 : ℝ))
  have hF : AbsolutelyContinuousOnInterval (fun x => F (x+1)) 0 1 := by
    apply absolutelyContinuousOnInterval_comp_add_right (f := F) 0 1 1
    norm_num only [zero_add, one_add_one_eq_two]
    apply (hillRepresentative_H1 f).1.mono
    norm_num [uIcc_of_le]
    exact Icc_subset_Icc (by norm_num) le_rfl
  have hG : AbsolutelyContinuousOnInterval (fun x => G (x+1)) 0 1 := by
    apply absolutelyContinuousOnInterval_comp_add_right (f := G) 0 1 1
    norm_num only [zero_add, one_add_one_eq_two]
    apply (hillDerivativeRepresentative_H1 f).1.mono
    norm_num [uIcc_of_le]
    exact Icc_subset_Icc (by norm_num) le_rfl
  have hFG := ae_second_unit_of_ae_two (hillRepresentative_deriv_ae f)
  have hEq := ae_second_unit_of_ae_two (physicalHillOperator_eigen_ae _ lambda f he)
  have hQ := ae_second_unit_of_ae_two (Fourier.circle_ae_pullback
    (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) AddCircle.haarAddCircle Q))
  have hFG' : ∀ᵐ x : ℝ, x ∈ Icc (0 : ℝ) 1 → deriv (fun y => F (y+1)) x = G (x+1) := by
    simpa only [deriv_comp_add_const] using hFG
  have hEq' : ∀ᵐ x : ℝ, x ∈ Icc (0 : ℝ) 1 → deriv (fun y => G (y+1)) x =
      (LinearVolterra.extend (hillSecondPotentialCurve Q) x-lambda)*F (x+1) := by
    filter_upwards [hEq, hQ] with x hxEq hxQ
    intro hxi
    have hpot : LinearVolterra.extend (hillSecondPotentialCurve Q) x = Q ((x+1 : ℝ) : AddCircle (2 : ℝ)) := by
      rw [LinearVolterra.extend, projIcc_of_mem _ hxi]
      rfl
    have heq := hxEq hxi
    have hq := hxQ hxi
    change Fourier.circlePullback (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ Q) (x+1) =
      Q ((x+1 : ℝ) : AddCircle (2 : ℝ)) at hq
    rw [hq] at heq
    rw [hpot, deriv_comp_add_const]
    dsimp [F, G]
    simp only [AddCircle.coe_add] at heq ⊢
    linear_combination -heq
  simpa only [F, G, hillPhysicalState, zero_add] using
    classicalHillFlow_unique_of_ac (hillSecondPotentialCurve Q) lambda _ _ hF hG hFG' hEq'

theorem hillPhysicalState_two (f : HillSobolevDomain) : hillPhysicalState f 2 = hillPhysicalState f 0 := by
  have hc : ((2 : ℝ) : AddCircle (2 : ℝ)) = 0 := by
    simpa only [zero_add, AddCircle.coe_zero] using AddCircle.coe_add_period (2 : ℝ) 0
  simp only [hillPhysicalState, hc, AddCircle.coe_zero]

/-- An actual periodic H2 eigenvector returns to the same state after
the composition of the two normalized scalar flows. -/
theorem physicalHillEigenvector_fullPeriod (Q : C(AddCircle (2 : ℝ), ℂ))
    (lambda : ℂ) (f : HillSobolevDomain)
    (he : physicalHillOperator (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ Q) f =
      lambda • ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ (hillRepresentative f)) :
    classicalHillFlow (hillSecondPotentialCurve Q) lambda
      (classicalHillFlow (hillUnitPotentialCurve Q) lambda (hillPhysicalState f 0) 1) 1 =
        hillPhysicalState f 0 := by
  have h1 := physicalHillEigenvector_eq_classicalFlow Q lambda f he (show (1 : ℝ) ∈ Icc 0 1 by norm_num)
  have h2 := physicalHillEigenvector_secondFlow Q lambda f he (show (1 : ℝ) ∈ Icc 0 1 by norm_num)
  change hillPhysicalState f 1 = classicalHillFlow (hillUnitPotentialCurve Q) lambda (hillPhysicalState f 0) 1 at h1
  change hillPhysicalState f (1+1) = classicalHillFlow (hillSecondPotentialCurve Q) lambda (hillPhysicalState f 1) 1 at h2
  rw [show (1 : ℝ)+1=2 by norm_num, hillPhysicalState_two, h1] at h2
  exact h2.symm

end NLS.KdV
