import NLS.KdV.ClassicalHillFlow
import NLS.KdV.HillPhysical

/-!
# The periodic H2 Hill operator agrees with the classical scalar flow

For a continuous physical potential, a domain eigenvector and its actual
continuous derivative representative have the constructed scalar Hill
state on the unit interval. This supplies the weak/classical comparison;
the periodic two-interval endpoint and global labeling arguments are not
asserted here.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open NLS.LinearVolterra
namespace NLS.KdV

/-- Restrict the actual physical circle potential to the scalar IVP interval. -/
def hillUnitPotentialCurve (Q : C(AddCircle (2 : ℝ), ℂ)) : Curve ℂ :=
  ⟨fun t => Q ((t : ℝ) : AddCircle (2 : ℝ)), by fun_prop⟩

private theorem ae_unit_of_ae_two {P : ℝ → Prop}
    (h : ∀ᵐ x : ℝ ∂volume.restrict (Ioc 0 2), P x) :
    ∀ᵐ x : ℝ, x ∈ Icc (0 : ℝ) 1 → P x := by
  rw [ae_restrict_iff' measurableSet_Ioc] at h
  filter_upwards [h, (show ∀ᵐ x : ℝ, x ≠ (0 : ℝ) by simp [ae_iff, measure_singleton])] with x hx hx0
  intro hxi
  exact hx ⟨lt_of_le_of_ne hxi.1 (Ne.symm hx0), by linarith [hxi.2]⟩

/-- The actual weak periodic eigenvector has the scalar IVP state with
its actual initial position and derivative. -/
theorem physicalHillEigenvector_eq_classicalFlow (Q : C(AddCircle (2 : ℝ), ℂ))
    (lambda : ℂ) (f : HillSobolevDomain)
    (he : physicalHillOperator (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ Q) f =
      lambda • ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ (hillRepresentative f)) :
    EqOn (fun x : ℝ => (hillRepresentative f (x : AddCircle (2 : ℝ)),
      hillDerivativeRepresentative f (x : AddCircle (2 : ℝ))))
      (classicalHillFlow (hillUnitPotentialCurve Q) lambda
        (hillRepresentative f (0 : AddCircle (2 : ℝ)), hillDerivativeRepresentative f (0 : AddCircle (2 : ℝ))))
      (Icc 0 1) := by
  have hF : AbsolutelyContinuousOnInterval
      (fun x : ℝ => hillRepresentative f (x : AddCircle (2 : ℝ))) 0 1 := by
    apply (hillRepresentative_H1 f).1.mono
    simp only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1), uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)]
    exact Icc_subset_Icc le_rfl (by norm_num)
  have hG : AbsolutelyContinuousOnInterval
      (fun x : ℝ => hillDerivativeRepresentative f (x : AddCircle (2 : ℝ))) 0 1 := by
    apply (hillDerivativeRepresentative_H1 f).1.mono
    simp only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1), uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)]
    exact Icc_subset_Icc le_rfl (by norm_num)
  have hFG := ae_unit_of_ae_two (hillRepresentative_deriv_ae f)
  have hEq := ae_unit_of_ae_two (physicalHillOperator_eigen_ae _ lambda f he)
  have hQ := ae_unit_of_ae_two (Fourier.circle_ae_pullback
    (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) AddCircle.haarAddCircle Q))
  apply classicalHillFlow_unique_of_ac (hillUnitPotentialCurve Q) lambda _ _ hF hG hFG
  filter_upwards [hEq, hQ] with x hxEq hxQ
  intro hxi
  have hpot : LinearVolterra.extend (hillUnitPotentialCurve Q) x = Q (x : AddCircle (2 : ℝ)) := by
    rw [LinearVolterra.extend, projIcc_of_mem _ hxi]
    rfl
  have heq := hxEq hxi
  have hq := hxQ hxi
  change Fourier.circlePullback (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ Q) x =
    Q (x : AddCircle (2 : ℝ)) at hq
  rw [hq] at heq
  rw [hpot]
  linear_combination -heq

end NLS.KdV
