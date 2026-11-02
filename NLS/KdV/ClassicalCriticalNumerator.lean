import NLS.KdV.ClassicalCriticalPointBranch
import NLS.ComplexAnalysis.ParametricDividedDifference

/-! # Entire actual spectral numerators near the free potential

Divide the actual discriminant derivative by its constructed moving simple
critical point. The pole is filled by a jointly analytic divided difference.
These are a basis for the period equation, not yet its normalized infinite
solution. At the free potential they are exactly the proved normalized basis.
-/
noncomputable section
open Set Filter Topology Complex
namespace NLS.KdV

def classicalHillLocalCriticalPoint (n : ℕ+) : NLS.LinearVolterra.Curve ℂ → ℂ :=
  Classical.choose (exists_classicalHill_critical_point_branch n)

def classicalHillLocalCriticalDomain (n : ℕ+) : Set (NLS.LinearVolterra.Curve ℂ) :=
  Classical.choose (Classical.choose_spec (exists_classicalHill_critical_point_branch n))

theorem classicalHillLocalCritical_spec (n : ℕ+) :
    IsOpen (classicalHillLocalCriticalDomain n) ∧ 0 ∈ classicalHillLocalCriticalDomain n ∧
      classicalHillLocalCriticalPoint n 0 = freeHillEnergy n ∧
      AnalyticOnNhd ℂ (classicalHillLocalCriticalPoint n) (classicalHillLocalCriticalDomain n) ∧
      ∀ q ∈ classicalHillLocalCriticalDomain n,
        deriv (classicalHillDiscriminant q) (classicalHillLocalCriticalPoint n q) = 0 ∧
        deriv (deriv (classicalHillDiscriminant q)) (classicalHillLocalCriticalPoint n q) ≠ 0 :=
  Classical.choose_spec (Classical.choose_spec (exists_classicalHill_critical_point_branch n))

/-- The filled numerator `2nπ Δ'(λ,q)/(λ-λ_n^bullet(q))`. -/
def classicalHillCriticalNumerator (n : ℕ+) (t : ℂ × NLS.LinearVolterra.Curve ℂ) : ℂ :=
  (2*(n : ℂ)*Real.pi)*ComplexAnalysis.parametricMovingDividedDifference
    classicalHillDiscriminantDerivative (classicalHillLocalCriticalPoint n) t

theorem analyticOnNhd_classicalHillCriticalNumerator (n : ℕ+) :
    AnalyticOnNhd ℂ (classicalHillCriticalNumerator n) (univ ×ˢ classicalHillLocalCriticalDomain n) := by
  obtain ⟨hV, _, _, hμ, _⟩ := classicalHillLocalCritical_spec n
  exact analyticOnNhd_const.mul
    (ComplexAnalysis.analyticOnNhd_parametricMovingDividedDifference _ _ hV
      (analyticOnNhd_classicalHillDiscriminantDerivative.mono (subset_univ _)) hμ)

theorem classicalHillCriticalNumerator_factor (n : ℕ+) (z : ℂ)
    (q : NLS.LinearVolterra.Curve ℂ) (hq : q ∈ classicalHillLocalCriticalDomain n) :
    (z-classicalHillLocalCriticalPoint n q)*classicalHillCriticalNumerator n (z,q) =
      (2*(n : ℂ)*Real.pi)*deriv (classicalHillDiscriminant q) z := by
  obtain ⟨_, _, _, hμ, hcritical⟩ := classicalHillLocalCritical_spec n
  have he := ComplexAnalysis.parametricMovingDividedDifference_mul
    classicalHillDiscriminantDerivative (classicalHillLocalCriticalPoint n)
    (analyticOnNhd_classicalHillDiscriminantDerivative.mono (subset_univ _)) hμ z q hq
  change (z-classicalHillLocalCriticalPoint n q)*
    ComplexAnalysis.parametricMovingDividedDifference _ _ (z,q) =
    deriv (classicalHillDiscriminant q) z-deriv (classicalHillDiscriminant q)
      (classicalHillLocalCriticalPoint n q) at he
  rw [(hcritical q hq).1, sub_zero] at he
  dsimp only [classicalHillCriticalNumerator]
  linear_combination (2*(n : ℂ)*Real.pi)*he

theorem classicalHillCriticalNumerator_center (n : ℕ+)
    (q : NLS.LinearVolterra.Curve ℂ) (hq : q ∈ classicalHillLocalCriticalDomain n) :
    classicalHillCriticalNumerator n (classicalHillLocalCriticalPoint n q,q) =
      (2*(n : ℂ)*Real.pi)*deriv (deriv (classicalHillDiscriminant q))
        (classicalHillLocalCriticalPoint n q) := by
  rw [classicalHillCriticalNumerator,
    ComplexAnalysis.parametricMovingDividedDifference_center _ _
      (analyticOnNhd_classicalHillDiscriminantDerivative.mono (subset_univ _)) q hq]
  rfl

theorem classicalHillCriticalNumerator_center_ne_zero (n : ℕ+)
    (q : NLS.LinearVolterra.Curve ℂ) (hq : q ∈ classicalHillLocalCriticalDomain n) :
    classicalHillCriticalNumerator n (classicalHillLocalCriticalPoint n q,q) ≠ 0 := by
  rw [classicalHillCriticalNumerator_center n q hq]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
    (by exact_mod_cast n.ne_zero)) (by exact_mod_cast Real.pi_ne_zero))
    ((classicalHillLocalCritical_spec n).2.2.2.2 q hq).2

theorem classicalHillCriticalNumerator_free (n : ℕ+) (z : ℂ) :
    classicalHillCriticalNumerator n (z,0) = classicalHillFreePsi n z := by
  obtain ⟨_, h0, hμ0, hμ, _⟩ := classicalHillLocalCritical_spec n
  rw [classicalHillCriticalNumerator, ComplexAnalysis.parametricMovingDividedDifference_eq_dslope
    _ _ (analyticOnNhd_classicalHillDiscriminantDerivative.mono (subset_univ _)) hμ z 0 h0, hμ0]
  rfl

/-- For every nearby potential each constructed numerator is genuinely
entire in energy, including its moving omitted point. -/
theorem analyticOnNhd_classicalHillCriticalNumerator_energy (n : ℕ+)
    (q : NLS.LinearVolterra.Curve ℂ) (hq : q ∈ classicalHillLocalCriticalDomain n) :
    AnalyticOnNhd ℂ (fun z => classicalHillCriticalNumerator n (z,q)) univ := by
  intro z _
  exact (analyticOnNhd_classicalHillCriticalNumerator n (z,q) ⟨mem_univ _,hq⟩).comp
    (f := fun z : ℂ => (z,q)) (analyticAt_id.prod analyticAt_const)

end NLS.KdV
