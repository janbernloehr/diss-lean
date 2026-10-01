import NLS.FunctionalAnalysis.VariableGronwall
import NLS.ZakharovShabat.ClassicalSolutionGrowth

/-! # Actual classical growth controlled by integrated potential energy

The physical supremum norm is not bounded on a Hilbert source ball.
Variable-coefficient Gronwall instead bounds the actual fundamental
columns using the two component square integrals on the unit interval.
-/

noncomputable section
open Set Complex MeasureTheory NLS.LinearVolterra
namespace NLS.ZakharovShabat

/-- The sum of the two physical component energies on one period. -/
def classicalPotentialEnergy (Φ : Curve (ℂ × ℂ)) : ℝ :=
  ∫ s in (0 : ℝ)..1, ‖(extend Φ s).1‖^2 + ‖(extend Φ s).2‖^2

theorem classicalPotentialEnergy_nonneg (Φ : Curve (ℂ × ℂ)) :
    0 ≤ classicalPotentialEnergy Φ :=
  intervalIntegral.integral_nonneg (by norm_num) fun s _ => by positivity

private theorem norm_pair_le_one_add_energy (v : ℂ × ℂ) :
    ‖v‖ ≤ 1 + (‖v.1‖^2 + ‖v.2‖^2) := by
  apply norm_prod_le_iff.mpr
  constructor
  · nlinarith [sq_nonneg (‖v.1‖ - 1/2), sq_nonneg ‖v.2‖]
  · nlinarith [sq_nonneg (‖v.2‖ - 1/2), sq_nonneg ‖v.1‖]

/-- The integral of the actual ODE coefficient is controlled by physical
energy, uniformly for every time in the unit interval. -/
theorem integral_classicalGrowthCoefficient_le_energy
    (Φ : Curve (ℂ × ℂ)) (z : ℂ) (t : Icc (0 : ℝ) 1) :
    (∫ s in (0 : ℝ)..t.val, ‖z‖ + ‖extend Φ s‖) ≤
      ‖z‖ + 1 + classicalPotentialEnergy Φ := by
  have hc : Continuous (fun s : ℝ => ‖z‖ + ‖extend Φ s‖) :=
    continuous_const.add (continuous_extend Φ).norm
  have he : Continuous (fun s : ℝ => ‖(extend Φ s).1‖^2 + ‖(extend Φ s).2‖^2) :=
    ((continuous_extend Φ).fst.norm.pow 2).add ((continuous_extend Φ).snd.norm.pow 2)
  calc
    _ ≤ ∫ s in (0 : ℝ)..1, ‖z‖ + ‖extend Φ s‖ :=
      intervalIntegral.integral_mono_interval le_rfl t.property.1 t.property.2
        (Filter.Eventually.of_forall fun s => by positivity) (hc.intervalIntegrable 0 1)
    _ ≤ ∫ s in (0 : ℝ)..1, (‖z‖ + 1) + (‖(extend Φ s).1‖^2 + ‖(extend Φ s).2‖^2) := by
      apply intervalIntegral.integral_mono_on (by norm_num) (hc.intervalIntegrable 0 1)
        ((continuous_const.add he).intervalIntegrable 0 1)
      intro s _
      change ‖z‖ + ‖extend Φ s‖ ≤ ‖z‖ + 1 + (‖(extend Φ s).1‖^2 + ‖(extend Φ s).2‖^2)
      have h := norm_pair_le_one_add_energy (extend Φ s)
      linarith
    _ = _ := by
      rw [intervalIntegral.integral_add (continuous_const.intervalIntegrable 0 1)
        (he.intervalIntegrable 0 1)]
      simp [classicalPotentialEnergy]

/-- The actual solution is bounded using integrated physical energy,
without a bound on the supremum of the potential. -/
theorem norm_classicalSolution_le_exp_energy
    (Φ : Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ) (t : Icc (0 : ℝ) 1) :
    ‖classicalSolution Φ z v t‖ ≤
      ‖v‖ * Real.exp (‖z‖ + 1 + classicalPotentialEnergy Φ) := by
  have h := NLS.FunctionalAnalysis.norm_le_exp_integral_of_norm_deriv_le
    (f := classicalSolution Φ z v)
    (f' := fun s => classicalODECoefficient (extend Φ s) z (classicalSolution Φ z v s))
    (α := fun s => ‖z‖ + ‖extend Φ s‖) (a := 0) (b := 1)
    (continuous_classicalSolution Φ z v).continuousOn (by
      intro s hs
      have hs' : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1,hs.2.le⟩
      simpa only [NLS.LinearVolterra.extend,projIcc_of_mem _ hs'] using
        (hasDerivAt_classicalSolution Φ z v ⟨s,hs'⟩).hasDerivWithinAt)
    (continuous_const.add (continuous_extend Φ).norm)
    (fun _ _ => norm_classicalODECoefficient_apply_le _ _ _) t.val t.property
  rw [classicalSolution_zero] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (integral_classicalGrowthCoefficient_le_energy Φ z t)) (norm_nonneg _))

/-- The actual monodromy trace has an energy bound at every complex
spectral parameter and every continuous complex potential. -/
theorem norm_classicalDiscriminant_le_exp_energy (Φ : Curve (ℂ × ℂ)) (z : ℂ) :
    ‖classicalDiscriminant Φ z‖ ≤ 2 * Real.exp (‖z‖ + 1 + classicalPotentialEnergy Φ) := by
  let t : Icc (0 : ℝ) 1 := ⟨1,by constructor <;> norm_num⟩
  have h₁ := norm_classicalSolution_le_exp_energy Φ z (1,0) t
  have h₂ := norm_classicalSolution_le_exp_energy Φ z (0,1) t
  have ht : ‖classicalDiscriminant Φ z‖ ≤
      ‖classicalSolution Φ z (1,0) 1‖ + ‖classicalSolution Φ z (0,1) 1‖ := by
    simp only [classicalDiscriminant,classicalMonodromy,classicalFundamentalMatrix,Matrix.trace_fin_two_of]
    exact (norm_add_le _ _).trans (add_le_add (norm_fst_le _) (norm_snd_le _))
  exact ht.trans (by simpa [t,two_mul] using add_le_add h₁ h₂)

end NLS.ZakharovShabat
