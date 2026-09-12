import NLS.ZakharovShabat.PhysicalPotentialExtension
import NLS.ZakharovShabat.ClassicalIntervalRestriction

/-!
# The full Dirichlet interval `L²` isomorphism

The original physical extension has closed range by its exact lower norm bound.
Classical boundary restrictions supply a dense subset of this range, so every
Dirichlet coefficient vector comes from an original interval `L²` class. The
result is a continuous linear equivalence, with both exact norm factors.
-/

noncomputable section
open MeasureTheory Set NLS.Fourier
open scoped ENNReal
namespace NLS.ZakharovShabat
namespace BoundaryCondition

/-- The weighted boundary domain is dense in the corresponding base boundary space. -/
theorem inclusion_denseRange {p : ℝ≥0∞} [Fact (1 ≤ p)] (b : BoundaryCondition) (hp : p ≠ ⊤) :
    DenseRange (inclusion (p := p) b) := by
  have hr : Function.Surjective (retract (p := p) b) := by
    intro a
    exact ⟨a.val, Subtype.ext (projection_eq_self b a.property)⟩
  have hd := hr.denseRange.comp (domainInclusion_denseRange hp) (retract b).continuous
  apply Dense.mono _ hd
  rintro a ⟨f, rfl⟩
  exact ⟨domainRetract b f, Subtype.ext (inclusion_projection b f)⟩

/-- A classical boundary representative gives a physical interval `L²` class. -/
theorem memLp_classicalIntervalRestriction (b : BoundaryCondition) (a : Domain 2)
    (ha : a ∈ domain b) : MemLp (classicalIntervalRestriction a) 2 (volume.restrict (Ioc 0 1)) := by
  have hf := classicalIntervalRestriction_mem b a ha
  exact memLp_prod_iff.mpr ⟨memLp_of_intervalH1Regularity hf.fst_regular,
    memLp_of_intervalH1Regularity hf.snd_regular⟩

end BoundaryCondition
open BoundaryCondition

/-- Physical Dirichlet extension of a restricted domain vector recovers its unweighted coefficients. -/
theorem intervalPotentialCoefficients_classicalRestriction (a : Domain 2) (ha : a ∈ domain .dirichlet) :
    intervalPotentialCoefficients (intervalL2OfFunction (classicalIntervalRestriction a)
      (memLp_classicalIntervalRestriction .dirichlet a ha)) = domainInclusion a := by
  rw [intervalPotentialCoefficients_ofFunction]
  have he : dirichletPotentialCoefficients (classicalIntervalRestriction a)
      (memLp_classicalIntervalRestriction .dirichlet a ha) =
      domainInclusion (classicalIntervalExtension .dirichlet (classicalIntervalRestriction a)
        (classicalIntervalRestriction_mem .dirichlet a ha)) := by
    apply Prod.ext <;> apply Subtype.ext <;> funext n
    · simp only [domainInclusion_apply, scalarInclusion_apply,
        dirichletPotentialCoefficients_fst, classicalIntervalExtension_fst]
    · simp only [domainInclusion_apply, scalarInclusion_apply,
        dirichletPotentialCoefficients_snd, classicalIntervalExtension_snd]
  rw [classicalIntervalExtension_classicalIntervalRestriction .dirichlet a ha] at he
  exact he

/-- The image of physical Dirichlet extension contains the dense weighted domain. -/
theorem intervalPotentialToDirichlet_denseRange : DenseRange intervalPotentialToDirichlet := by
  apply Dense.mono _ (inclusion_denseRange (p := 2) .dirichlet (by simp))
  rintro y ⟨a, rfl⟩
  exact ⟨intervalL2OfFunction (classicalIntervalRestriction a.val)
    (memLp_classicalIntervalRestriction .dirichlet a.val a.property),
    Subtype.ext (intervalPotentialCoefficients_classicalRestriction a.val a.property)⟩

/-- A lower norm bound prevents loss of any physical `L²` limits in the coefficient image. -/
theorem isClosed_range_intervalPotentialToDirichlet : IsClosed (Set.range intervalPotentialToDirichlet) := by
  have ha : AntilipschitzWith 2 intervalPotentialToDirichlet :=
    intervalPotentialToDirichlet.antilipschitz_of_bound (fun u => by
      have he := norm_sq_intervalPotentialCoefficients u
      change ‖intervalPotentialToDirichlet u‖ ^ 2 = (1 / 2 : ℝ) * ‖u‖ ^ 2 at he
      change ‖u‖ ≤ 2 * ‖intervalPotentialToDirichlet u‖
      nlinarith [norm_nonneg u, norm_nonneg (intervalPotentialToDirichlet u)])
  exact ha.isClosed_range intervalPotentialToDirichlet.uniformContinuous

/-- Every Dirichlet coefficient vector has an original interval `L²` representative. -/
theorem intervalPotentialToDirichlet_surjective : Function.Surjective intervalPotentialToDirichlet := by
  intro a
  have h := intervalPotentialToDirichlet_denseRange a
  rwa [isClosed_range_intervalPotentialToDirichlet.closure_eq] at h

/-- Dirichlet signed extension identifies the whole physical interval base space. -/
def dirichletIntervalL2Equiv : IntervalPairL2 ≃L[ℂ] dirichletSubspace (p := 2) :=
  (LinearEquiv.ofBijective intervalPotentialToDirichlet.toLinearMap
    ⟨intervalPotentialToDirichlet_injective, intervalPotentialToDirichlet_surjective⟩).toContinuousLinearEquivOfBounds
    (Real.sqrt 2 / 2) 2
    (fun u => (norm_intervalPotentialToDirichlet u).le)
    (fun a => by
      let e := LinearEquiv.ofBijective intervalPotentialToDirichlet.toLinearMap
        ⟨intervalPotentialToDirichlet_injective, intervalPotentialToDirichlet_surjective⟩
      have he := norm_sq_intervalPotentialCoefficients (e.symm a)
      change ‖e (e.symm a)‖ ^ 2 = (1 / 2 : ℝ) * ‖e.symm a‖ ^ 2 at he
      rw [e.apply_symm_apply] at he
      nlinarith [norm_nonneg (e.symm a), norm_nonneg a])

@[simp] theorem dirichletIntervalL2Equiv_apply (u : IntervalPairL2) :
    dirichletIntervalL2Equiv u = intervalPotentialToDirichlet u := rfl

/-- The forward isomorphism has the exact normalized Fourier norm. -/
theorem norm_dirichletIntervalL2Equiv (u : IntervalPairL2) :
    ‖dirichletIntervalL2Equiv u‖ = (Real.sqrt 2 / 2) * ‖u‖ := norm_intervalPotentialToDirichlet u

/-- Physical restriction has the reciprocal norm factor. -/
theorem norm_dirichletIntervalL2Equiv_symm (a : dirichletSubspace (p := 2)) :
    ‖dirichletIntervalL2Equiv.symm a‖ = Real.sqrt 2 * ‖a‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg a))).mp
  rw [mul_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have he := norm_sq_intervalPotentialCoefficients (dirichletIntervalL2Equiv.symm a)
  change ‖dirichletIntervalL2Equiv (dirichletIntervalL2Equiv.symm a)‖ ^ 2 =
    (1 / 2 : ℝ) * ‖dirichletIntervalL2Equiv.symm a‖ ^ 2 at he
  rw [dirichletIntervalL2Equiv.apply_symm_apply] at he
  linarith

/-- The inverse is actual physical restriction almost everywhere on the original interval. -/
theorem dirichletIntervalL2Equiv_symm_restrict (a : dirichletSubspace (p := 2)) :
    intervalL2Representative (dirichletIntervalL2Equiv.symm a) =ᵐ[volume.restrict (Ioc 0 1)] physicalBase a.val := by
  have h := physicalBase_dirichletPotentialCoefficients
    (intervalL2Representative (dirichletIntervalL2Equiv.symm a)) (memLp_intervalL2Representative _)
  have he : intervalPotentialCoefficients (dirichletIntervalL2Equiv.symm a) = a.val :=
    congrArg Subtype.val (dirichletIntervalL2Equiv.apply_symm_apply a)
  change physicalBase (intervalPotentialCoefficients (dirichletIntervalL2Equiv.symm a)) =ᵐ[_] _ at h
  rw [he] at h
  have hr := ae_restrict_of_ae_restrict_of_subset
    (Ioc_subset_Ioc_right (show (1 : ℝ) ≤ 2 by norm_num)) h
  filter_upwards [hr, ae_restrict_mem measurableSet_Ioc] with x hx hmem
  exact ((intervalExtension_left .dirichlet _ x hmem.2).symm.trans hx.symm)

end NLS.ZakharovShabat
