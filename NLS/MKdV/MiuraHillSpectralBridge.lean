import NLS.MKdV.MiuraHillHamiltonianTrace
import NLS.KdV.ClassicalHillPrimitiveReflection

/-! # The physical Miura IVP and the shared scalar Hill discriminant

The identification uses uniqueness of the actual position/derivative state
equation. It therefore includes zero energy and does not assume equality of
spectral objects as a hypothesis. The continuous Hill potential may agree
with the physical Miura potential only almost everywhere.
-/
noncomputable section
open Set Complex Filter Topology MeasureTheory NLS.LinearVolterra
open NLS.FunctionalAnalysis NLS.KdV NLS.ZakharovShabat
open scoped ContDiff
namespace NLS.MKdV

theorem physicalMiuraState_eq_classicalHillFlow
    (U : Curve ℂ) (u : ℝ → ℂ) (hU : ∀ t, U t = u t)
    (hu : AbsolutelyContinuousOnInterval u 0 1) (q : Curve ℂ)
    (hq : ∀ᵐ x : ℝ, x ∈ Icc (0 : ℝ) 1 → extend q x = miuraPotential u x)
    (μ : ℂ) (v : ℂ × ℂ) :
    EqOn (fun x => (physicalMiuraSolution U μ v x,deriv (physicalMiuraSolution U μ v) x))
      (classicalHillFlow q μ v) (Icc 0 1) := by
  obtain ⟨hF,hG,hE⟩ := physicalMiuraSolution_spec U u hU hu μ v
  have he := classicalHillFlow_unique_of_ac q μ
    (physicalMiuraSolution U μ v) (deriv (physicalMiuraSolution U μ v)) hF hG
    (Filter.Eventually.of_forall (fun _ _ => rfl)) (by
      filter_upwards [hE,hq,
        (show ∀ᵐ x : ℝ, x ≠ (0 : ℝ) from by simp [ae_iff,measure_singleton]),
        (show ∀ᵐ x : ℝ, x ≠ (1 : ℝ) from by simp [ae_iff,measure_singleton])]
        with x hxE hxq hx0 hx1
      intro hx
      have hxi : x ∈ Ioo (0 : ℝ) 1 :=
        ⟨lt_of_le_of_ne hx.1 (Ne.symm hx0),lt_of_le_of_ne hx.2 hx1⟩
      rw [hxq hx]
      linear_combination -(hxE hxi))
  simpa only [physicalMiuraSolution_zero,deriv_physicalMiuraSolution_zero] using he

theorem physicalMiuraDiscriminant_eq_classicalHill
    (U : Curve ℂ) (u : ℝ → ℂ) (hU : ∀ t, U t = u t)
    (hu : AbsolutelyContinuousOnInterval u 0 1) (q : Curve ℂ)
    (hq : ∀ᵐ x : ℝ, x ∈ Icc (0 : ℝ) 1 → extend q x = miuraPotential u x)
    (μ : ℂ) :
    physicalMiuraDiscriminant U μ = classicalHillDiscriminant q μ := by
  have ht : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by constructor <;> norm_num
  have h1 := congrArg Prod.fst
    (physicalMiuraState_eq_classicalHillFlow U u hU hu q hq μ (1,0) ht)
  have h2 := congrArg Prod.snd
    (physicalMiuraState_eq_classicalHillFlow U u hU hu q hq μ (0,1) ht)
  exact (congrArg₂ (fun a b : ℂ => a+b) h1 h2).trans (classicalHillFlow_trace q μ)

/-- The continuous literal Miura potential of a C¹ profile. -/
def miuraHillProfileCurve (u : ℝ → ℂ) (hu : ContDiff ℝ 1 u) : Curve ℂ :=
  miuraProfileCurve (miuraPotential u)
    ((hu.continuous_deriv (by norm_num)).add (hu.continuous.pow 2))

theorem physicalMiuraDiscriminant_profile_eq_classicalHill
    (u : ℝ → ℂ) (hu : ContDiff ℝ 1 u) (μ : ℂ) :
    physicalMiuraDiscriminant (miuraProfileCurve u hu.continuous) μ =
      classicalHillDiscriminant (miuraHillProfileCurve u hu) μ := by
  apply physicalMiuraDiscriminant_eq_classicalHill _ u (fun _ => rfl)
    hu.contDiffOn.absolutelyContinuousOnInterval
  exact Filter.Eventually.of_forall (fun x hx => by
    rw [extend_coe _ ⟨x,hx⟩]
    rfl)

/-- Literal Hill/diagonal-ZS trace equality, in the shared scalar
normalization, on every complex C¹ periodic profile and every energy z². -/
theorem classicalHillDiscriminant_miura_eq_ZS
    (u : ℝ → ℂ) (hu : ContDiff ℝ 1 u) (hp : Function.Periodic u 1) (z : ℂ) :
    classicalHillDiscriminant (miuraHillProfileCurve u hu) (z^2) =
      classicalDiscriminant (classicalPotentialOfFunctions u u hu.continuous hu.continuous) z := by
  rw [← physicalMiuraDiscriminant_profile_eq_classicalHill u hu]
  exact physicalMiuraDiscriminant_profile_eq_ZS u hu.continuous hp z

end NLS.MKdV
