import NLS.KdV.HillDirichletGradientCurves

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.ZakharovShabat NLS.FunctionalAnalysis
open scoped ENNReal Classical

namespace NLS.KdV



/-- The original rough scalar potential representative, read from the lower
component of the actual constant-upper first-order potential. -/
def hillL2ScalarRepresentative (q : Coeff 2) (x : ℝ) : ℂ :=
  -(intervalL2Representative (physicalRestrictionL2 (hillFirstOrderPotential q)) x).2

/-- The scalar state transformation retains both original differential equations. -/
theorem constantUpperStateMap_ode (z : ℂ) (a y : ℂ × ℂ) (ha : a.1 = -1) :
    constantUpperStateMap z (classicalODECoefficient a z y) =
      ((constantUpperStateMap z y).2,(-a.2-z^2)*(constantUpperStateMap z y).1) := by
  apply Prod.ext <;> simp only [constantUpperStateMap_apply,classicalODECoefficient_apply,ha]
  · ring
  · ring_nf
    simp only [I_sq]
    ring

/-- The actual rough Hill state satisfies its full scalar system almost everywhere. -/
theorem ae_hasDerivAt_hillL2FrequencyStateCurve (q : Coeff 2) (z : ℂ) (v : ℂ × ℂ) :
    ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1),
      HasDerivAt (extend (hillL2FrequencyStateCurve q z v))
        ((extend (hillL2FrequencyStateCurve q z v) x).2,
          (hillL2ScalarRepresentative q x-z^2)*(extend (hillL2FrequencyStateCurve q z v) x).1) x := by
  filter_upwards [ae_hasDerivAt_l2SolutionCurve
    (physicalRestrictionL2 (hillFirstOrderPotential q)) z (constantUpperInitialVector z v),
    hillFirstOrder_upper_eq_neg_one_ae q] with x hx hu
  have hd := ((constantUpperStateMap z).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt x hx
  change HasDerivAt (fun t => constantUpperStateMap z
    (extend (l2SolutionCurve (physicalRestrictionL2 (hillFirstOrderPotential q)) z
      (constantUpperInitialVector z v)) t))
    (constantUpperStateMap z (classicalODECoefficient
      (intervalL2Representative (physicalRestrictionL2 (hillFirstOrderPotential q)) x) z
      (extend (l2SolutionCurve (physicalRestrictionL2 (hillFirstOrderPotential q)) z
        (constantUpperInitialVector z v)) x))) x at hd
  rw [constantUpperStateMap_ode z _ _ hu] at hd
  exact hd

/-- The derivative coordinate is absolutely continuous with the actual rough
Schrodinger source, not merely a distributional substitute. -/
theorem ae_hasDerivAt_hillL2FrequencyStateCurve_snd (q : Coeff 2) (z : ℂ) (v : ℂ × ℂ) :
    ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1),
      HasDerivAt (fun t => (extend (hillL2FrequencyStateCurve q z v) t).2)
        ((hillL2ScalarRepresentative q x-z^2)*(extend (hillL2FrequencyStateCurve q z v) x).1) x := by
  filter_upwards [ae_hasDerivAt_hillL2FrequencyStateCurve q z v] with x hx
  simpa using! HasFDerivAt.hasDerivAt hx.snd

/-- The original L2 potential times the continuous position is integrable. -/
theorem intervalIntegrable_hillL2ScalarRepresentative_mul_state (q : Coeff 2) (z : ℂ) (v : ℂ × ℂ) :
    IntervalIntegrable (fun x => hillL2ScalarRepresentative q x*
      (extend (hillL2FrequencyStateCurve q z v) x).1) volume 0 1 := by
  have hi := (intervalIntegrable_intervalL2_mul
    (physicalRestrictionL2 (hillFirstOrderPotential q)).ofLp.2
    (l2BoundedFirst (hillL2FrequencyStateCurve q z v)) ⟨1,by norm_num⟩).neg
  convert hi using 1
  funext x
  simp only [hillL2ScalarRepresentative,intervalL2Representative,l2BoundedFirst,
    ContinuousLinearMap.compLeftContinuousBounded_apply,curveBoundedExtension_apply,
    ContinuousLinearMap.coe_fst',neg_mul,Pi.neg_apply]

/-- For a continuous source potential this is its original physical restriction. -/
theorem hillL2ScalarRepresentative_eq_continuous
    (Q : C(AddCircle (2 : ℝ),ℂ)) :
    hillL2ScalarRepresentative (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q))
      =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] extend (hillUnitPotentialCurve Q) := by
  filter_upwards [physicalRestrictionL2_representative
    (hillFirstOrderPotential (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q))),
    hillFirstOrder_continuous_compatibility Q] with x hx hQ
  dsimp only [hillL2ScalarRepresentative]
  rw [hx]
  have hh := congrArg Prod.snd hQ
  change -(physicalBase (hillFirstOrderPotential
    (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q))) x).2 = _
  rw [hh]
  simp only [NLS.LinearVolterra.extend,constantUpperPotential_apply,neg_neg]

end NLS.KdV
