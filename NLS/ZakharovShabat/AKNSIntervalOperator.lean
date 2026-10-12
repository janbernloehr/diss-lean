import NLS.ZakharovShabat.AKNSPhysicalNorms

/-! # The original classical AKNS operators

The AKNS domain consists of actual closed-interval H¹ functions with the
printed endpoint conditions. The physical L² unitary and H¹ isometry conjugate
the inclusion and operator, and realize the actual AKNS differential expression.
-/
noncomputable section
open MeasureTheory Set NLS.Fourier
namespace NLS.ZakharovShabat
open BoundaryCondition

/-- Pointwise coordinates on functions on the original closed interval. -/
def aknsIntervalLinear : (Icc (0 : ℝ) 1 → ℂ × ℂ) →ₗ[ℂ] (Icc (0 : ℝ) 1 → ℂ × ℂ) where
  toFun f x := aknsToZS (f x)
  map_add' f g := by funext x; exact aknsCoordinateEquiv.map_add _ _
  map_smul' c f := by funext x; exact aknsCoordinateEquiv.map_smul c _

/-- The original AKNS domain as a linear subspace of closed-interval functions. -/
def aknsIntervalSubmodule (b : BoundaryCondition) : Submodule ℂ (Icc (0 : ℝ) 1 → ℂ × ℂ) :=
  (classicalIntervalSubmodule b).comap aknsIntervalLinear

/-- Membership is exactly the printed H¹ domain, without a periodicity assumption. -/
theorem mem_aknsIntervalSubmodule_iff (b : BoundaryCondition) (u : Icc (0 : ℝ) 1 → ℂ × ℂ) :
    u ∈ aknsIntervalSubmodule b ↔ ∃ g : ℝ → ℂ × ℂ,
      HasAKNSIntervalDomain b g ∧ ∀ x : Icc (0 : ℝ) 1, u x = g x.val := by
  change aknsIntervalLinear u ∈ classicalIntervalSubmodule b ↔ _
  rw [mem_classicalIntervalSubmodule_iff]
  constructor
  · rintro ⟨f, hf, hu⟩
    refine ⟨fun x => zsToAKNS (f x), (hasAKNSIntervalDomain_zsToAKNS_iff b f).mpr hf, ?_⟩
    intro x
    have he := congrArg zsToAKNS (hu x)
    simpa only [aknsIntervalLinear, LinearMap.coe_mk, AddHom.coe_mk, zsToAKNS_aknsToZS] using he
  · rintro ⟨g, hg, hu⟩
    exact ⟨fun x => aknsToZS (g x), (hasClassicalIntervalDomain_aknsToZS_iff b g).mpr hg,
      fun x => congrArg aknsToZS (hu x)⟩

/-- Actual AKNS endpoint-domain functions. -/
def AKNSIntervalDomain (b : BoundaryCondition) := ↥(aknsIntervalSubmodule b)

instance (b : BoundaryCondition) : AddCommGroup (AKNSIntervalDomain b) :=
  inferInstanceAs (AddCommGroup ↥(aknsIntervalSubmodule b))
instance (b : BoundaryCondition) : Module ℂ (AKNSIntervalDomain b) :=
  inferInstanceAs (Module ℂ ↥(aknsIntervalSubmodule b))

/-- Pointwise coordinate equivalence of the two actual domains. -/
def aknsDomainLinearEquiv (b : BoundaryCondition) : AKNSIntervalDomain b ≃ₗ[ℂ] ClassicalIntervalDomain b where
  toFun u := ⟨aknsIntervalLinear u.val, u.property⟩
  invFun v := ⟨fun x => zsToAKNS (v.val x), by
    change (fun x => aknsToZS (zsToAKNS (v.val x))) ∈ classicalIntervalSubmodule b
    simpa only [aknsToZS_zsToAKNS] using v.property⟩
  left_inv u := by apply Subtype.ext; funext x; exact zsToAKNS_aknsToZS _
  right_inv v := by apply Subtype.ext; funext x; exact aknsToZS_zsToAKNS _
  map_add' u v := by apply Subtype.ext; exact aknsIntervalLinear.map_add _ _
  map_smul' c u := by apply Subtype.ext; exact aknsIntervalLinear.map_smul c _

instance (b : BoundaryCondition) : NormedAddCommGroup (AKNSIntervalDomain b) :=
  NormedAddCommGroup.induced _ _ (aknsDomainLinearEquiv b) (aknsDomainLinearEquiv b).injective
instance (b : BoundaryCondition) : NormedSpace ℂ (AKNSIntervalDomain b) :=
  NormedSpace.induced ℂ _ _ (aknsDomainLinearEquiv b).toLinearMap

/-- The coordinate map is an isometry for the physical H¹ norm. -/
def aknsDomainEquiv (b : BoundaryCondition) : AKNSIntervalDomain b ≃ₗᵢ[ℂ] ClassicalIntervalDomain b where
  toLinearEquiv := aknsDomainLinearEquiv b
  norm_map' _ := rfl

/-- An arbitrary original AKNS function defines a domain element. -/
def aknsDomainOfFunction (b : BoundaryCondition) (g : ℝ → ℂ × ℂ)
    (hg : HasAKNSIntervalDomain b g) : AKNSIntervalDomain b :=
  ⟨fun x => g x.val, (mem_aknsIntervalSubmodule_iff b _).mpr ⟨g, hg, fun _ => rfl⟩⟩

@[simp] theorem aknsDomainEquiv_ofFunction (b : BoundaryCondition) (g : ℝ → ℂ × ℂ)
    (hg : HasAKNSIntervalDomain b g) :
    aknsDomainEquiv b (aknsDomainOfFunction b g hg) =
      classicalDomainOfFunction b (fun x => aknsToZS (g x))
        ((hasClassicalIntervalDomain_aknsToZS_iff b g).mpr hg) := rfl

/-- The induced domain norm is exactly the physical component-sum H¹ norm. -/
theorem norm_aknsDomainOfFunction (b : BoundaryCondition) (g : ℝ → ℂ × ℂ)
    (hg : HasAKNSIntervalDomain b g) :
    ‖aknsDomainOfFunction b g hg‖ = classicalIntervalNorm g := by
  rw [← (aknsDomainEquiv b).norm_map, aknsDomainEquiv_ofFunction, norm_classicalDomainOfFunction]
  exact classicalIntervalNorm_aknsToZS hg.fst_regular hg.snd_regular

/-- Original AKNS domain inclusion into physical L². -/
def aknsInclusion (b : BoundaryCondition) : AKNSIntervalDomain b →L[ℂ] IntervalPairL2 :=
  aknsL2Equiv.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((classicalInclusion b).comp (aknsDomainEquiv b).toContinuousLinearEquiv.toContinuousLinearMap)

/-- The potential map is bounded on arbitrary original L² representatives. -/
theorem memLp_aknsPotential {q p : ℝ → ℂ}
    (hq : MemLp q 2 (volume.restrict (Ioc 0 1))) (hp : MemLp p 2 (volume.restrict (Ioc 0 1))) :
    MemLp (fun x => aknsPotential (q x) (p x)) 2 (volume.restrict (Ioc 0 1)) :=
  memLp_prod_iff.mpr ⟨hq.add (hp.const_mul Complex.I), hq.sub (hp.const_mul Complex.I)⟩

/-- The original operator at a pair of L² potential representatives. -/
def aknsIntervalOperator (b : BoundaryCondition) (q p : ℝ → ℂ)
    (hq : MemLp q 2 (volume.restrict (Ioc 0 1))) (hp : MemLp p 2 (volume.restrict (Ioc 0 1))) :
    AKNSIntervalDomain b →L[ℂ] IntervalPairL2 :=
  aknsL2Equiv.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((classicalOperator b (intervalL2OfFunction (fun x => aknsPotential (q x) (p x)) (memLp_aknsPotential hq hp))).comp
      (aknsDomainEquiv b).toContinuousLinearEquiv.toContinuousLinearMap)

/-- Exact unitary conjugation of the domain inclusion. -/
theorem aknsL2Equiv_inclusion (b : BoundaryCondition) (u : AKNSIntervalDomain b) :
    aknsL2Equiv (aknsInclusion b u) = classicalInclusion b (aknsDomainEquiv b u) :=
  aknsL2Equiv.apply_symm_apply _

/-- Exact unitary conjugation of the original unbounded operator's action. -/
theorem aknsL2Equiv_operator (b : BoundaryCondition) (q p : ℝ → ℂ)
    (hq : MemLp q 2 (volume.restrict (Ioc 0 1))) (hp : MemLp p 2 (volume.restrict (Ioc 0 1)))
    (u : AKNSIntervalDomain b) :
    aknsL2Equiv (aknsIntervalOperator b q p hq hp u) =
      classicalOperator b (intervalL2OfFunction (fun x => aknsPotential (q x) (p x))
        (memLp_aknsPotential hq hp)) (aknsDomainEquiv b u) := aknsL2Equiv.apply_symm_apply _

theorem aknsInclusion_injective (b : BoundaryCondition) : Function.Injective (aknsInclusion b) :=
  aknsL2Equiv.symm.injective.comp ((classicalInclusion_injective b).comp (aknsDomainEquiv b).injective)

/-- Both original AKNS endpoint domains are dense in physical L². -/
theorem aknsInclusion_denseRange (b : BoundaryCondition) : DenseRange (aknsInclusion b) :=
  aknsL2Equiv.symm.surjective.denseRange.comp
    ((classicalInclusion_denseRange b).comp (aknsDomainEquiv b).surjective.denseRange (classicalInclusion b).continuous)
    aknsL2Equiv.symm.continuous

/-- Inclusion takes the original function's L² class. -/
theorem aknsInclusion_realization (b : BoundaryCondition) (g : ℝ → ℂ × ℂ)
    (hg : HasAKNSIntervalDomain b g) :
    intervalL2Representative (aknsInclusion b (aknsDomainOfFunction b g hg))
      =ᵐ[volume.restrict (Ioc 0 1)] g := by
  have hL : MemLp g 2 (volume.restrict (Ioc 0 1)) := memLp_prod_iff.mpr
    ⟨memLp_of_intervalH1Regularity hg.fst_regular, memLp_of_intervalH1Regularity hg.snd_regular⟩
  have hC := classicalInclusion_ofFunction b (fun x => aknsToZS (g x))
    ((hasClassicalIntervalDomain_aknsToZS_iff b g).mpr hg) (memLp_aknsToZS hL)
  have he := aknsL2Inverse_representative (classicalInclusion b
    (aknsDomainEquiv b (aknsDomainOfFunction b g hg)))
  rw [aknsDomainEquiv_ofFunction, hC] at he
  change intervalL2Representative (aknsL2Inverse (classicalInclusion b
    (aknsDomainEquiv b (aknsDomainOfFunction b g hg)))) =ᵐ[volume.restrict (Ioc 0 1)] g
  rw [aknsDomainEquiv_ofFunction, hC]
  filter_upwards [he, intervalL2Representative_ofFunction (fun x => aknsToZS (g x)) (memLp_aknsToZS hL)] with x hx hy
  exact hx.trans (by rw [hy, zsToAKNS_aknsToZS])

/-- The conjugated operator is the actual AKNS differential expression almost everywhere. -/
theorem aknsIntervalOperator_realization (b : BoundaryCondition) (q p : ℝ → ℂ)
    (hq : MemLp q 2 (volume.restrict (Ioc 0 1))) (hp : MemLp p 2 (volume.restrict (Ioc 0 1)))
    (g : ℝ → ℂ × ℂ) (hg : HasAKNSIntervalDomain b g) :
    intervalL2Representative (aknsIntervalOperator b q p hq hp (aknsDomainOfFunction b g hg))
      =ᵐ[volume.restrict (Ioc 0 1)] aknsPhysicalOperator q p g := by
  have he := aknsL2Inverse_representative
    (classicalOperator b (intervalL2OfFunction (fun x => aknsPotential (q x) (p x)) (memLp_aknsPotential hq hp))
      (aknsDomainEquiv b (aknsDomainOfFunction b g hg)))
  rw [aknsDomainEquiv_ofFunction] at he
  have hc := classicalOperator_realization_ofFunction b (fun x => aknsPotential (q x) (p x))
    (fun x => aknsToZS (g x)) (memLp_aknsPotential hq hp) ((hasClassicalIntervalDomain_aknsToZS_iff b g).mpr hg)
  filter_upwards [he, hc, physicalOperator_aknsToZS hg.fst_regular hg.snd_regular q p] with x hx hy hz
  exact hx.trans (by rw [hy, hz, zsToAKNS_aknsToZS])

end NLS.ZakharovShabat
