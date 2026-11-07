import NLS.KdV.SingularDirichletForcedCharts
import NLS.MKdV.QuasiHillL2ForcedCurve
import NLS.FunctionalAnalysis.ClosedIntervalDerivativeCongruence

/-! # Actual forced scalar states realize native Dirichlet equations

Both scalar positions are retained on the full closed interval. The native
equation uses the same preceding H1 vector and all native weak tests.
-/
noncomputable section
open Set Complex MeasureTheory NLS.LinearVolterra NLS.FunctionalAnalysis
namespace NLS.KdV
open NLS.Fourier NLS.MKdV

/-- Representing both actual scalar positions transports a rough forced
physical state to the ENTIRE native Miura inhomogeneous equation. -/
theorem singularDirichletMiura_forced_of_state (u : Coeff 2) (lambda : ℂ)
    (v w : Curve (ℂ × ℂ)) (hw : IsQuasiHillL2ForcedSolution u lambda v w)
    (f g : UnitDirichletH1)
    (hf : ∀ x ∈ Icc (0:ℝ) 1, (extend w x).1 = unitDirichletRepresentative f x)
    (hg : ∀ x ∈ Icc (0:ℝ) 1, (extend v x).1 = unitDirichletRepresentative g x) :
    singularDirichletOperator (periodOneOriginal (periodOneMiura u)) f-
      lambda • singularDirichletDomainInclusion f = singularDirichletDomainInclusion g := by
  let G := fun x : ℝ => (extend w x).2
  have hregs := hw.intervalH1 u lambda v w
  have hfirst : ∀ᵐ x ∂volume.restrict (Ioc 0 1), HasDerivAt (unitDirichletRepresentative f)
      (unitL2SynthesisEquiv u x*unitDirichletRepresentative f x+G x) x := by
    have h := ae_hasDerivAt_Ioc_congr_of_eqOn_Icc hf (hw.position_row u lambda v w)
    filter_upwards [h, ae_restrict_mem measurableSet_Ioc] with x hx hxi
    rw [hf x ⟨hxi.1.le,hxi.2⟩] at hx
    exact hx
  have hsecond : ∀ᵐ x ∂volume.restrict (Ioc 0 1), HasDerivAt G
      (-lambda*unitDirichletRepresentative f x-unitL2SynthesisEquiv u x*G x-
        unitDirichletRepresentative g x) x := by
    filter_upwards [hw.quasiDerivative_row u lambda v w, ae_restrict_mem measurableSet_Ioc]
      with x hx hxi
    rw [hf x ⟨hxi.1.le,hxi.2⟩, hg x ⟨hxi.1.le,hxi.2⟩] at hx
    exact hx
  exact singularDirichletMiura_forced_of_physical_rows u lambda f g G
    (continuous_extend w).snd hregs.2.1 hregs.2.2 hfirst hsecond

/-- The same realization holds for EVERY original complex unit-period
source, using its actual shifted Miura chart. -/
theorem singularDirichlet_source_forced_of_state (q : PeriodOneHminusOne) (lambda : ℂ)
    (v w : Curve (ℂ × ℂ))
    (hw : IsQuasiHillL2ForcedSolution ((hillHminusMiuraChartAt q).lift q)
      (lambda+(hillHminusMiuraChartAt q).energyShift) v w)
    (f g : UnitDirichletH1)
    (hf : ∀ x ∈ Icc (0:ℝ) 1, (extend w x).1 = unitDirichletRepresentative f x)
    (hg : ∀ x ∈ Icc (0:ℝ) 1, (extend v x).1 = unitDirichletRepresentative g x) :
    singularDirichletOperator (periodOneOriginal q) f-lambda • singularDirichletDomainInclusion f =
      singularDirichletDomainInclusion g :=
  (singularDirichlet_forced_iff_shiftedMiura q lambda f g).mpr
    (singularDirichletMiura_forced_of_state _ _ v w hw f g hf hg)

end NLS.KdV
