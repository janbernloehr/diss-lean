import NLS.ZakharovShabat.SourceBoundaryCounting
import NLS.ZakharovShabat.SourceContourTrace
import NLS.ZakharovShabat.BoundaryEigenvalues

/-!
# Lemma 4.5: the original boundary trace formula

The trace is taken on the actual original-norm boundary contour range. A
bounded lift represents its vectors in the original one-derivative boundary
domain, and the intrinsic endomorphism acts by the original operator there.
Continuous conjugation preserves its trace. On each high disk it equals the
unique simple boundary eigenvalue and depends analytically on the original
interval input for 1<p<infinity. The printed p=1 endpoint is treated separately
in `SourceLemma4_5Endpoint`, through the classical Hilbert realization.
-/

noncomputable section
open scoped ENNReal
namespace NLS

private theorem trace_conjugate {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (e : E ≃L[ℂ] F) (P A : F →L[ℂ] F)
    (hP : IsIdempotentElem P) (hA : Commute P A) :
    ProjectionTrace.trace (e.symm.conjContinuousAlgEquiv P) (e.symm.conjContinuousAlgEquiv A) =
      ProjectionTrace.trace P A := by
  let r := ConjugatedRanges.rangeEquiv e P
  have he : r.conjAlgEquiv ℂ
      (ProjectionTrace.restriction (e.symm.conjContinuousAlgEquiv P)
        (e.symm.conjContinuousAlgEquiv A)).toLinearMap = (ProjectionTrace.restriction P A).toLinearMap := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (r (ProjectionTrace.restriction _ _ (r.symm x))).val = _
    change e ((ProjectionTrace.restriction _ _ (r.symm x)).val) = _
    rw [ProjectionTrace.restriction_apply _ _ (hP.map _) (hA.map _)]
    change e (e.symm (A (e (r.symm x).val))) = _
    rw [e.apply_symm_apply]
    have hx : e (r.symm x).val = x.val := congrArg Subtype.val (r.apply_symm_apply x)
    rw [hx]
    exact (ProjectionTrace.restriction_apply P A hP hA x).symm
  unfold ProjectionTrace.trace
  rw [← he,LinearMap.trace_map]

namespace ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The original circle integral projected onto the selected boundary space. -/
def sourceBoundaryAmbientCircleProjection (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (c : ℂ) (r : ℝ) : CoeffPair p →L[ℂ] CoeffPair p :=
  sourceBoundaryProjection b * sourceResolventCircleIntegral hp φ c r

/-- A bounded lift into the original one-derivative boundary domain. -/
def sourceBoundaryAmbientContourLift (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (c : ℂ) (r : ℝ) : CoeffPair p →L[ℂ] WeightedCoeffPair (Weight.sobolev 1) p :=
  (WeightedCoeffPair.toMax (Weight.sobolev 1) p).symm.toContinuousLinearMap.comp
    ((b.contourLift hp (CoeffPair.toMax p φ) c r).comp (CoeffPair.toMax p).toContinuousLinearMap)

/-- The bounded map L P, formed with the actual original operator and its domain lift. -/
def sourceBoundaryAmbientContourOperator (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (c : ℂ) (r : ℝ) : CoeffPair p →L[ℂ] CoeffPair p :=
  (sourceOperator hp φ).comp (sourceBoundaryAmbientContourLift b hp φ c r)

theorem sourceBoundaryAmbientCircleProjection_eq_conj (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hc : Metric.sphere c r ⊆ sourceResolventSet hp φ) :
    sourceBoundaryAmbientCircleProjection b hp φ c r =
      (CoeffPair.toMax p).symm.conjContinuousAlgEquiv (b.contourProjection hp (CoeffPair.toMax p φ) c r) := by
  rw [sourceBoundaryAmbientCircleProjection,sourceResolventCircleIntegral_eq_conj hp φ c r hr hc]
  exact ((CoeffPair.toMax p).symm.conjContinuousAlgEquiv.map_mul _ _).symm

theorem sourceBoundaryAmbientContourOperator_eq_conj (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (c : ℂ) (r : ℝ) :
    sourceBoundaryAmbientContourOperator b hp φ c r =
      (CoeffPair.toMax p).symm.conjContinuousAlgEquiv (b.contourOperator hp (CoeffPair.toMax p φ) c r) := by
  ext x : 1
  change (CoeffPair.toMax p).symm (operator hp (CoeffPair.toMax p φ)
    ((WeightedCoeffPair.toMax (Weight.sobolev 1) p) ((WeightedCoeffPair.toMax (Weight.sobolev 1) p).symm _))) = _
  rw [ContinuousLinearEquiv.apply_symm_apply]
  rfl

/-- Intrinsic trace on the actual original boundary contour range. -/
def sourceBoundaryContourTrace (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (c : ℂ) (r : ℝ) : ℂ :=
  ProjectionTrace.trace (sourceBoundaryAmbientCircleProjection b hp φ c r)
    (sourceBoundaryAmbientContourOperator b hp φ c r)

/-- Continuous norm conversion preserves the trace of the original spectral restriction. -/
theorem sourceBoundaryContourTrace_eq (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .dirichlet) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hc : Metric.sphere c r ⊆ sourceResolventSet hp φ) :
    sourceBoundaryContourTrace b hp φ c r = b.contourTrace hp (CoeffPair.toMax p φ) c r := by
  unfold sourceBoundaryContourTrace BoundaryCondition.contourTrace
  rw [sourceBoundaryAmbientCircleProjection_eq_conj b hp φ c r hr hc,sourceBoundaryAmbientContourOperator_eq_conj]
  exact trace_conjugate (CoeffPair.toMax p) _ _
    (b.contourProjection_idempotent hp (CoeffPair.toMax p φ) hφ c r hr (by rwa [sourceResolventSet_eq] at hc))
    (b.contourOperator_commute_projection hp (CoeffPair.toMax p φ) hφ c r hr (by rwa [sourceResolventSet_eq] at hc))

/-- The original contour trace is analytic after the completed interval extension. -/
theorem analyticAt_sourceBoundaryContourTrace (b : BoundaryCondition) (hp1 : 1 < p) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hc : Metric.sphere c r ⊆ sourceResolventSet hp (sourceReflectedPotential hp1 hp φ)) :
    AnalyticAt ℂ (fun ψ => sourceBoundaryContourTrace b hp (sourceReflectedPotential hp1 hp ψ) c r) φ := by
  let F := periodOneBoundaryPotential hp hp1
  have hc' : Metric.sphere c r ⊆ resolventSet hp (F φ).val := by
    rw [sourceResolventSet_eq,toMax_sourceReflectedPotential] at hc
    exact hc
  have ha := (b.analyticAt_contourTrace hp (F φ) c r hr hc').comp (F.analyticAt φ)
  apply ha.congr
  have ho := (isOpen_resolventCircleDomain hp c r).preimage
    (((dirichletSubspace (p := p)).subtypeL.comp F).continuous)
  filter_upwards [ho.mem_nhds hc'] with ψ hψ
  have hcψ : Metric.sphere c r ⊆ sourceResolventSet hp (sourceReflectedPotential hp1 hp ψ) := by
    rw [sourceResolventSet_eq,toMax_sourceReflectedPotential]
    exact hψ
  change b.contourTrace hp (F ψ).val c r = _
  rw [sourceBoundaryContourTrace_eq b hp _ (sourceReflectedPotential_mem hp1 hp ψ) c r hr hcψ,
    toMax_sourceReflectedPotential]

/-- The high-index ordinary boundary branch, defined by the original trace formula. -/
def sourceBoundaryEigenvalue (b : BoundaryCondition) (hp1 : 1 < p) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (n : ℤ) : ℂ :=
  sourceBoundaryContourTrace b hp (sourceReflectedPotential hp1 hp φ) ((Real.pi : ℂ)*n) (Real.pi/4)

/-- The trace-defined original branch agrees with the existing period-one branch. -/
theorem sourceBoundaryEigenvalue_eq_periodOne (b : BoundaryCondition) (hp1 : 1 < p) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (n : ℤ)
    (hc : Metric.sphere ((Real.pi : ℂ)*n) (Real.pi/4) ⊆ sourceResolventSet hp (sourceReflectedPotential hp1 hp φ)) :
    sourceBoundaryEigenvalue b hp1 hp φ n = periodOneBoundaryEigenvalue hp hp1 b φ n := by
  rw [sourceBoundaryEigenvalue,sourceBoundaryContourTrace_eq b hp _ (sourceReflectedPotential_mem hp1 hp φ)
    _ _ (by positivity) hc,toMax_sourceReflectedPotential]
  rfl

theorem analyticAt_sourceBoundaryEigenvalue (b : BoundaryCondition) (hp1 : 1 < p) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (n : ℤ)
    (hc : Metric.sphere ((Real.pi : ℂ)*n) (Real.pi/4) ⊆ sourceResolventSet hp (sourceReflectedPotential hp1 hp φ)) :
    AnalyticAt ℂ (fun ψ => sourceBoundaryEigenvalue b hp1 hp ψ n) φ :=
  analyticAt_sourceBoundaryContourTrace b hp1 hp φ _ _ (by positivity) hc

theorem sourceBoundaryAmbientContourLift_mem (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (c : ℂ) (r : ℝ) (x : CoeffPair p) :
    sourceBoundaryAmbientContourLift b hp φ c r x ∈ sourceWeightedBoundarySubspace b 1 := by
  change WeightedCoeffPair.toMax (Weight.sobolev 1) p
    ((WeightedCoeffPair.toMax (Weight.sobolev 1) p).symm _) ∈ b.domain
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact b.contourLift_mem hp (CoeffPair.toMax p φ) c r (CoeffPair.toMax p x)

theorem sourceBoundaryAmbientContourLift_inclusion (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hc : Metric.sphere c r ⊆ sourceResolventSet hp φ) (x : CoeffPair p) :
    sourceDomainInclusion (sourceBoundaryAmbientContourLift b hp φ c r x) =
      sourceBoundaryAmbientCircleProjection b hp φ c r x := by
  rw [sourceBoundaryAmbientCircleProjection_eq_conj b hp φ c r hr hc]
  change (CoeffPair.toMax p).symm (domainInclusion
    ((WeightedCoeffPair.toMax (Weight.sobolev 1) p)
      ((WeightedCoeffPair.toMax (Weight.sobolev 1) p).symm _))) = _
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact congrArg (CoeffPair.toMax p).symm
    (b.inclusion_contourLift hp (CoeffPair.toMax p φ) c r hr
      (by rwa [sourceResolventSet_eq] at hc) (CoeffPair.toMax p x))

/-- The original operator restricted intrinsically to the boundary contour range. -/
def sourceBoundaryContourRestriction (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (c : ℂ) (r : ℝ) :
    (sourceBoundaryAmbientCircleProjection b hp φ c r).range →L[ℂ]
      (sourceBoundaryAmbientCircleProjection b hp φ c r).range :=
  ProjectionTrace.restriction (sourceBoundaryAmbientCircleProjection b hp φ c r)
    (sourceBoundaryAmbientContourOperator b hp φ c r)

/-- The intrinsic endomorphism acts by the actual original operator on its domain lift. -/
theorem sourceBoundaryContourRestriction_apply (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .dirichlet) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hc : Metric.sphere c r ⊆ sourceResolventSet hp φ)
    (x : (sourceBoundaryAmbientCircleProjection b hp φ c r).range) :
    (sourceBoundaryContourRestriction b hp φ c r x).val =
      sourceOperator hp φ (sourceBoundaryAmbientContourLift b hp φ c r x.val) := by
  have hc' : Metric.sphere c r ⊆ resolventSet hp (CoeffPair.toMax p φ) := by rwa [sourceResolventSet_eq] at hc
  have hP : IsIdempotentElem (sourceBoundaryAmbientCircleProjection b hp φ c r) := by
    rw [sourceBoundaryAmbientCircleProjection_eq_conj b hp φ c r hr hc]
    exact (b.contourProjection_idempotent hp (CoeffPair.toMax p φ) hφ c r hr hc').map _
  have hA : Commute (sourceBoundaryAmbientCircleProjection b hp φ c r)
      (sourceBoundaryAmbientContourOperator b hp φ c r) := by
    rw [sourceBoundaryAmbientCircleProjection_eq_conj b hp φ c r hr hc,sourceBoundaryAmbientContourOperator_eq_conj]
    exact (b.contourOperator_commute_projection hp (CoeffPair.toMax p φ) hφ c r hr hc').map _
  exact ProjectionTrace.restriction_apply _ _ hP hA x

/-- The original trace is the unique high-disk value, of original algebraic multiplicity one. -/
theorem sourceBoundaryEigenvalue_spec (b : BoundaryCondition) (hp1 : 1 < p) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (N : ℕ)
    (h : SourceBoundaryCountingData hp (sourceReflectedPotential hp1 hp φ)
      (sourceReflectedPotential_mem hp1 hp φ) N) (n : ℤ) (hn : N < n.natAbs) :
    sourceBoundaryEnclosedSpectrum b hp (sourceReflectedPotential hp1 hp φ)
      (sourceReflectedPotential_mem hp1 hp φ) ((Real.pi : ℂ)*n) (Real.pi/4) = {sourceBoundaryEigenvalue b hp1 hp φ n} ∧
    sourceBoundaryAlgebraicMultiplicity b hp (sourceReflectedPotential hp1 hp φ)
      (sourceReflectedPotential_mem hp1 hp φ) (sourceBoundaryEigenvalue b hp1 hp φ n) = 1 := by
  have he : sourceBoundaryEigenvalue b hp1 hp φ n =
      b.eigenvalue hp (CoeffPair.toMax p (sourceReflectedPotential hp1 hp φ)) n := by
    rw [sourceBoundaryEigenvalue,sourceBoundaryContourTrace_eq b hp _
      (sourceReflectedPotential_mem hp1 hp φ) _ _ (by positivity) (h.disk_resolvent n hn)]
    rfl
  simp only [he,sourceBoundaryAlgebraicMultiplicity_eq,sourceBoundaryEnclosedSpectrum]
  exact h.coefficient_counts.eigenvalue_spec b n hn

/-- Lemma 4.5 for 1<p<infinity, on one common original-input neighborhood. -/
theorem sourceLemma4_5 (hp1 : 1 < p) (hp : p ≠ ⊤) (φ : CoeffPair p) :
    ∃ N₀ : ℕ, ∃ U : Set (CoeffPair p), 0 < N₀ ∧ IsOpen U ∧ Convex ℝ U ∧ IsConnected U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ b : BoundaryCondition, ∀ n : ℤ, N₀ < n.natAbs →
        AnalyticOnNhd ℂ (fun ψ => sourceBoundaryEigenvalue b hp1 hp ψ n) U ∧
        ∀ ψ ∈ U,
          sourceBoundaryEnclosedSpectrum b hp (sourceReflectedPotential hp1 hp ψ)
            (sourceReflectedPotential_mem hp1 hp ψ) ((Real.pi : ℂ)*n) (Real.pi/4) =
              {sourceBoundaryEigenvalue b hp1 hp ψ n} ∧
          sourceBoundaryAlgebraicMultiplicity b hp (sourceReflectedPotential hp1 hp ψ)
            (sourceReflectedPotential_mem hp1 hp ψ) (sourceBoundaryEigenvalue b hp1 hp ψ n) = 1 := by
  obtain ⟨N,U,hN,ho,hconv,hconn,hφ,h0,hd⟩ := exists_uniform_sourceBoundaryCountingData hp1 hp φ
  refine ⟨N,U,hN,ho,hconv,hconn,hφ,h0,?_⟩
  intro b n hn
  refine ⟨?_,?_⟩
  · intro ψ hψ
    exact analyticAt_sourceBoundaryEigenvalue b hp1 hp ψ n (((hd N le_rfl).2.2 ψ hψ).disk_resolvent n hn)
  · intro ψ hψ
    exact sourceBoundaryEigenvalue_spec b hp1 hp ψ N ((hd N le_rfl).2.2 ψ hψ) n hn

theorem sourceBoundaryAmbientCircleProjection_idempotent (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .dirichlet) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hc : Metric.sphere c r ⊆ sourceResolventSet hp φ) :
    IsIdempotentElem (sourceBoundaryAmbientCircleProjection b hp φ c r) := by
  rw [sourceBoundaryAmbientCircleProjection_eq_conj b hp φ c r hr hc]
  exact (b.contourProjection_idempotent hp (CoeffPair.toMax p φ) hφ c r hr
    (by rwa [sourceResolventSet_eq] at hc)).map _

theorem sourceBoundaryAmbientCircleProjection_range_mem (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (c : ℂ) (r : ℝ)
    (x : (sourceBoundaryAmbientCircleProjection b hp φ c r).range) :
    x.val ∈ sourceBoundaryBaseSubspace b := by
  obtain ⟨y,hy⟩ := x.property
  rw [← hy]
  exact sourceBoundaryProjection_mem b _

theorem sourceBoundaryCircleProjection_mem_range_iff_ambient (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .dirichlet) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hc : Metric.sphere c r ⊆ sourceResolventSet hp φ) (x : sourceBoundaryBaseSubspace (p := p) b) :
    x ∈ (sourceBoundaryCircleProjection b hp φ c r).range ↔
      x.val ∈ (sourceBoundaryAmbientCircleProjection b hp φ c r).range := by
  constructor
  · rintro ⟨y,hy⟩
    exact ⟨y.val,congrArg Subtype.val hy⟩
  · rintro ⟨y,hy⟩
    refine ⟨x,?_⟩
    apply Subtype.ext
    change sourceBoundaryAmbientCircleProjection b hp φ c r x.val = x.val
    rw [← hy]
    exact DFunLike.congr_fun (sourceBoundaryAmbientCircleProjection_idempotent b hp φ hφ c r hr hc) y

/-- The ambient boundary range is exactly the actual typed boundary-projector range, with its original norm. -/
def sourceBoundaryContourRangeEquiv (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .dirichlet) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hc : Metric.sphere c r ⊆ sourceResolventSet hp φ) :
    (sourceBoundaryCircleProjection b hp φ c r).range ≃ₗᵢ[ℂ]
      (sourceBoundaryAmbientCircleProjection b hp φ c r).range where
  toFun x := ⟨x.val.val,(sourceBoundaryCircleProjection_mem_range_iff_ambient b hp φ hφ c r hr hc x.val).mp x.property⟩
  invFun x := ⟨⟨x.val,sourceBoundaryAmbientCircleProjection_range_mem b hp φ c r x⟩,
    (sourceBoundaryCircleProjection_mem_range_iff_ambient b hp φ hφ c r hr hc _).mpr x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' _ := rfl

/-- On the spectral range, the domain lift represents the given vector itself. -/
theorem sourceBoundaryAmbientContourLift_range (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .dirichlet) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hc : Metric.sphere c r ⊆ sourceResolventSet hp φ)
    (x : (sourceBoundaryAmbientCircleProjection b hp φ c r).range) :
    sourceDomainInclusion (sourceBoundaryAmbientContourLift b hp φ c r x.val) = x.val := by
  rw [sourceBoundaryAmbientContourLift_inclusion b hp φ c r hr hc]
  obtain ⟨y,hy⟩ := x.property
  rw [← hy]
  exact DFunLike.congr_fun (sourceBoundaryAmbientCircleProjection_idempotent b hp φ hφ c r hr hc) y

/-- The printed trace is the intrinsic trace of the actual original operator restriction. -/
theorem sourceBoundaryContourTrace_eq_trace_restriction (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (c : ℂ) (r : ℝ) :
    sourceBoundaryContourTrace b hp φ c r = LinearMap.trace ℂ
      (sourceBoundaryAmbientCircleProjection b hp φ c r).range
      (sourceBoundaryContourRestriction b hp φ c r).toLinearMap := rfl

/-- A rank-one original boundary range has trace equal to its enclosed eigenvalue. -/
theorem sourceBoundaryContourTrace_eq_of_rank_one (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .dirichlet) (c z : ℂ) (r : ℝ)
    (hr : 0 ≤ r) (hc : Metric.sphere c r ⊆ sourceResolventSet hp φ)
    (hrank : Module.finrank ℂ (sourceBoundaryCircleProjection b hp φ c r).range = 1)
    (hz : z ∈ sourceBoundaryEnclosedSpectrum b hp φ hφ c r) : sourceBoundaryContourTrace b hp φ c r = z := by
  rw [sourceBoundaryContourTrace_eq b hp φ hφ c r hr hc]
  apply b.contourTrace_eq_of_rank_one hp (CoeffPair.toMax p φ) hφ c z r
    (by rwa [sourceResolventSet_eq] at hc) _ hz
  rwa [← finrank_range_sourceBoundaryCircleProjection b hp φ hφ c r hr hc]

end ZakharovShabat
end NLS
