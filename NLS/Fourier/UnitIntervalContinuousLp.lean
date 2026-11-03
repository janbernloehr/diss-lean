import NLS.ZakharovShabat.PhysicalL2IntegralPairing
import NLS.Fourier.UnitDirichletContinuous

/-! Exact physical inclusions of closed-unit-interval continuous functions
in ordinary Lebesgue Lp, including the essential-supremum endpoint.
The unit interval has measure one, so every inclusion has norm at most one. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace NLS.Fourier
open NLS.ZakharovShabat NLS.LinearVolterra

/-- The ordinary physical unit-interval Lp class of the same continuous curve. -/
def unitIntervalContinuousToLp (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    C(Icc (0:ℝ) 1,ℂ) →L[ℂ] Lp ℂ p (volume.restrict (Ioc (0:ℝ) 1)) :=
  (BoundedContinuousFunction.toLp p (volume.restrict (Ioc (0:ℝ) 1)) ℂ).comp
    (curveBoundedExtension ℂ)

/-- Every such Lp class retains the identical interval representative. -/
theorem unitIntervalContinuousToLp_representative (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : C(Icc (0:ℝ) 1,ℂ)) :
    unitIntervalContinuousToLp p f =ᵐ[volume.restrict (Ioc (0:ℝ) 1)] extend f :=
  BoundedContinuousFunction.coeFn_toLp p (volume.restrict (Ioc (0:ℝ) 1)) ℂ _

/-- The actual ordinary Lp norm is controlled by the closed-interval
uniform norm with constant EXACTLY one, including p=infinity. -/
theorem norm_unitIntervalContinuousToLp_le (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : C(Icc (0:ℝ) 1,ℂ)) : ‖unitIntervalContinuousToLp p f‖ ≤ ‖f‖ := by
  have hm : measureUnivNNReal (volume.restrict (Ioc (0:ℝ) 1)) = 1 := by
    norm_num [measureUnivNNReal]
  have hb := BoundedContinuousFunction.Lp_norm_le (p := p)
    (μ := volume.restrict (Ioc (0:ℝ) 1)) (curveBoundedExtension ℂ f)
  change ‖unitIntervalContinuousToLp p f‖ ≤ _ at hb
  simp only [hm,NNReal.coe_one,Real.one_rpow,one_mul] at hb
  apply hb.trans
  apply (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr
  intro x
  exact f.norm_coe_le_norm _

/-- On the full native domain, this is the SAME original physical L2 inclusion. -/
theorem unitIntervalContinuousToLp_two_dirichlet (g : UnitDirichletH1) :
    unitIntervalContinuousToLp 2 (unitDirichletContinuousInclusion g) = unitDirichletL2Inclusion g := by
  apply Lp.ext
  filter_upwards [unitIntervalContinuousToLp_representative 2 (unitDirichletContinuousInclusion g),
    unitDirichletL2Inclusion_representative g,ae_restrict_mem measurableSet_Ioc] with x hx hy hxi
  have he := extend_coe (unitDirichletContinuousInclusion g) ⟨x,⟨hxi.1.le,hxi.2⟩⟩
  exact (hx.trans he).trans hy.symm

/-- The exact original domain L2 norm is at most its physical uniform norm. -/
theorem norm_unitDirichletL2Inclusion_le_uniform (g : UnitDirichletH1) :
    ‖unitDirichletL2Inclusion g‖ ≤ ‖unitDirichletContinuousInclusion g‖ := by
  rw [← unitIntervalContinuousToLp_two_dirichlet]
  exact norm_unitIntervalContinuousToLp_le _ _

end NLS.Fourier
