import NLS.ZakharovShabat.ContourSpectrum
import NLS.FunctionalAnalysis.CircleIntegrationMap
import NLS.FunctionalAnalysis.ProjectionRank
import Mathlib.Topology.ContinuousMap.Units
import Mathlib.Topology.ContinuousMap.Algebra

/-!
# Analytic dependence for fixed resolvent circles

The normalized pencil along a compact circle belongs to a Banach algebra of
continuous operator-valued functions. Its invertibility persists under small
changes of the potential, and inversion is analytic in the uniform norm.
Bounded linear circle integration then yields analytic contour projections.
-/

noncomputable section
open Complex Metric Topology
open scoped ENNReal

namespace NLS.ZakharovShabat

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

private theorem reference_off : I ∉ freeLattice :=
  notMem_freeLattice_of_im_ne_zero (by simp)

/-- Potentials for which a fixed circle lies in the resolvent set. -/
def resolventCircleDomain (hp : p ≠ ⊤) (c : ℂ) (r : ℝ) : Set (PairSpace p) :=
  {φ | sphere c r ⊆ resolventSet hp φ}

private def circlePencil (hp : p ≠ ⊤) (c : ℂ) (r : ℝ) (φ : PairSpace p) :
    C(sphere c r, PairSpace p →L[ℂ] PairSpace p) where
  toFun z := normalizedPencil hp φ z
  continuous_toFun := by
    have h : Continuous (fun z : ℂ => normalizedPencil hp φ z) :=
      continuous_iff_continuousAt.mpr fun z =>
        ((analyticAt_normalizedPencil hp (φ, z)).comp
          (analyticAt_const.prod analyticAt_id)).continuousAt
    exact h.comp continuous_subtype_val

private def circlePencilVariation (hp : p ≠ ⊤) (c : ℂ) (r : ℝ) :
    PairSpace p →L[ℂ] C(sphere c r, PairSpace p →L[ℂ] PairSpace p) :=
  (ContinuousLinearMap.const ℂ (sphere c r)).comp
    (((ContinuousLinearMap.compL ℂ (PairSpace p) (Domain p) (PairSpace p)).flip
      (freeResolventToDomain I reference_off)).comp (potentialOperatorCLM hp))

private theorem circlePencil_affine (hp : p ≠ ⊤) (c : ℂ) (r : ℝ) (φ : PairSpace p) :
    circlePencil hp c r φ = circlePencil hp c r 0 - circlePencilVariation hp c r φ := by
  apply ContinuousMap.ext
  intro z
  apply ContinuousLinearMap.ext
  intro x
  change z.val • domainInclusion _ - (freeOperator _ + potentialOperator hp φ _) =
    (z.val • domainInclusion _ - (freeOperator _ + potentialOperator hp 0 _)) -
      potentialOperator hp φ _
  have hz : potentialOperator hp 0 = 0 := (potentialOperatorCLM hp).map_zero
  rw [hz, zero_apply, add_zero]
  abel

private theorem analyticAt_circlePencil (hp : p ≠ ⊤) (c : ℂ) (r : ℝ) (φ : PairSpace p) :
    AnalyticAt ℂ (circlePencil hp c r) φ := by
  have ha : AnalyticAt ℂ (fun ψ : PairSpace p =>
      circlePencil hp c r 0 - circlePencilVariation hp c r ψ) φ :=
    analyticAt_const.sub (ContinuousLinearMap.analyticAt (𝕜 := ℂ)
      (E := PairSpace p) (F := C(sphere c r, PairSpace p →L[ℂ] PairSpace p))
      (circlePencilVariation hp c r) φ)
  exact ha.congr (Filter.Eventually.of_forall fun ψ => (circlePencil_affine hp c r ψ).symm)

private theorem mem_circleDomain_iff (hp : p ≠ ⊤) (c : ℂ) (r : ℝ) (φ : PairSpace p) :
    φ ∈ resolventCircleDomain hp c r ↔ IsUnit (circlePencil hp c r φ) := by
  rw [ContinuousMap.isUnit_iff_forall_isUnit]
  exact ⟨fun h z => (mem_resolventSet_iff_isUnit hp φ z).mp (h z.property),
    fun h z hz => (mem_resolventSet_iff_isUnit hp φ z).mpr (h ⟨z, hz⟩)⟩

/-- A compact resolvent circle persists on an open set of potentials. -/
theorem isOpen_resolventCircleDomain (hp : p ≠ ⊤) (c : ℂ) (r : ℝ) :
    IsOpen (resolventCircleDomain hp c r) := by
  have he : resolventCircleDomain hp c r =
      (circlePencil hp c r) ⁻¹' {A | IsUnit A} :=
    Set.ext (mem_circleDomain_iff hp c r)
  rw [he]
  exact (Units.isOpen (R := C(sphere c r, PairSpace p →L[ℂ] PairSpace p))).preimage
    (continuous_iff_continuousAt.mpr fun φ => (analyticAt_circlePencil hp c r φ).continuousAt)

private def circleResolvent (hp : p ≠ ⊤) (c : ℂ) (r : ℝ) (φ : PairSpace p) :
    C(sphere c r, PairSpace p →L[ℂ] PairSpace p) :=
  (ContinuousLinearMap.compLeftContinuous ℂ (sphere c r)
    ((ContinuousLinearMap.compL ℂ (PairSpace p) (PairSpace p) (PairSpace p))
      (freeResolvent I reference_off))) (Ring.inverse (circlePencil hp c r φ))

private theorem continuousMap_inverse_apply {X A : Type*} [TopologicalSpace X]
    [NormedRing A] [CompleteSpace A] (f : C(X, A)) (hf : IsUnit f) (x : X) :
    Ring.inverse f x = Ring.inverse (f x) := by
  have hx := (ContinuousMap.isUnit_iff_forall_isUnit f).mp hf x
  have hm := congrArg (fun g : C(X, A) => g x) (Ring.mul_inverse_cancel f hf)
  change f x * Ring.inverse f x = 1 at hm
  calc
    _ = Ring.inverse (f x) * (f x * Ring.inverse f x) := by
      rw [← mul_assoc, Ring.inverse_mul_cancel _ hx, one_mul]
    _ = _ := by rw [hm, mul_one]

private theorem compLeftContinuous_apply {X E F : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℂ E] [NormedSpace ℂ F]
    (L : E →L[ℂ] F) (f : C(X, E)) (x : X) :
    (ContinuousLinearMap.compLeftContinuous ℂ X L f) x = L (f x) := rfl

private theorem circleResolvent_apply (hp : p ≠ ⊤) (c : ℂ) (r : ℝ) (φ : PairSpace p)
    (hc : φ ∈ resolventCircleDomain hp c r) (z : sphere c r) :
    circleResolvent hp c r φ z = resolvent hp φ z := by
  have hu := (mem_circleDomain_iff hp c r φ).mp hc
  calc
    circleResolvent hp c r φ z = (freeResolvent I reference_off).comp
        (Ring.inverse (circlePencil hp c r φ) z) :=
      compLeftContinuous_apply _ _ _
    _ = (freeResolvent I reference_off).comp
        (Ring.inverse (normalizedPencil hp φ z)) :=
      congrArg (fun A : PairSpace p →L[ℂ] PairSpace p =>
        (freeResolvent I reference_off).comp A)
        (continuousMap_inverse_apply (circlePencil hp c r φ) hu z)
    _ = resolvent hp φ z := ContinuousLinearMap.comp_assoc _ _ _

private theorem analyticAt_circleResolvent (hp : p ≠ ⊤) (c : ℂ) (r : ℝ) (φ : PairSpace p)
    (hc : φ ∈ resolventCircleDomain hp c r) :
    AnalyticAt ℂ (circleResolvent hp c r) φ := by
  have hi := (analyticOnNhd_inverse (𝕜 := ℂ)
    (A := C(sphere c r, PairSpace p →L[ℂ] PairSpace p)) _
    ((mem_circleDomain_iff hp c r φ).mp hc)).comp
      (f := circlePencil hp c r) (analyticAt_circlePencil hp c r φ)
  exact (ContinuousLinearMap.analyticAt (𝕜 := ℂ)
    (E := C(sphere c r, PairSpace p →L[ℂ] PairSpace p))
    (F := C(sphere c r, PairSpace p →L[ℂ] PairSpace p))
    (ContinuousLinearMap.compLeftContinuous ℂ (sphere c r)
      ((ContinuousLinearMap.compL ℂ (PairSpace p) (PairSpace p) (PairSpace p))
        (freeResolvent I reference_off))) _).comp hi

/-- Fixed-circle contour projections depend complex analytically on the potential
in operator norm wherever the circle stays in the resolvent set. -/
theorem analyticAt_resolventCircleIntegral (hp : p ≠ ⊤) (φ : PairSpace p)
    (c : ℂ) (r : ℝ) (hr : 0 ≤ r) (hc : sphere c r ⊆ resolventSet hp φ) :
    AnalyticAt ℂ (fun ψ => resolventCircleIntegral hp ψ c r) φ := by
  have ha := (ContinuousLinearMap.analyticAt (𝕜 := ℂ)
    (E := C(sphere c r, PairSpace p →L[ℂ] PairSpace p))
    (F := PairSpace p →L[ℂ] PairSpace p)
    (NLS.CircleIntegral.integrationCLM (PairSpace p →L[ℂ] PairSpace p) c r hr) _).comp
      (analyticAt_circleResolvent hp c r φ hc)
  apply ha.congr
  filter_upwards [(isOpen_resolventCircleDomain hp c r).mem_nhds hc] with ψ hψ
  exact NLS.CircleIntegral.integrationCLM_eq c r hr _ (resolvent hp ψ)
    (circleResolvent_apply hp c r ψ hψ)

/-- Analyticity holds throughout the open set of admissible potentials. -/
theorem analyticOnNhd_resolventCircleIntegral (hp : p ≠ ⊤) (c : ℂ) (r : ℝ)
    (hr : 0 ≤ r) :
    AnalyticOnNhd ℂ (fun ψ => resolventCircleIntegral hp ψ c r)
      (resolventCircleDomain hp c r) :=
  fun φ hc => analyticAt_resolventCircleIntegral hp φ c r hr hc

/-- On a neighborhood of an admissible potential, the circle stays in the
resolvent set and the contour projection has constant rank. -/
theorem eventually_finrank_resolventCircleIntegral_eq (hp : p ≠ ⊤) (φ : PairSpace p)
    (c : ℂ) (r : ℝ) (hr : 0 ≤ r) (hc : sphere c r ⊆ resolventSet hp φ) :
    ∀ᶠ ψ in 𝓝 φ, sphere c r ⊆ resolventSet hp ψ ∧
      Module.finrank ℂ (resolventCircleIntegral hp ψ c r).range =
        Module.finrank ℂ (resolventCircleIntegral hp φ c r).range := by
  have hcont := (analyticAt_resolventCircleIntegral hp φ c r hr hc).continuousAt
  have hnear : ∀ᶠ ψ in 𝓝 φ,
      ‖resolventCircleIntegral hp ψ c r - resolventCircleIntegral hp φ c r‖ < 1 := by
    have hevent : ∀ᶠ ψ in 𝓝 φ, resolventCircleIntegral hp ψ c r ∈
        ball (resolventCircleIntegral hp φ c r) 1 :=
      hcont.preimage_mem_nhds (Metric.ball_mem_nhds _ zero_lt_one)
    filter_upwards [hevent] with ψ hψ
    simpa only [Metric.mem_ball, dist_eq_norm] using hψ
  filter_upwards [(isOpen_resolventCircleDomain hp c r).mem_nhds hc, hnear] with ψ hψ hnorm
  refine ⟨hψ, ?_⟩
  let : FiniteDimensional ℂ (resolventCircleIntegral hp ψ c r).range :=
    finiteDimensional_range_resolventCircleIntegral hp ψ c r hr hψ
  let : FiniteDimensional ℂ (resolventCircleIntegral hp φ c r).range :=
    finiteDimensional_range_resolventCircleIntegral hp φ c r hr hc
  exact NLS.ProjectionRank.finrank_eq_of_norm_sub_lt_one _ _
    (resolventCircleIntegral_idempotent hp ψ c r hr hψ)
    (resolventCircleIntegral_idempotent hp φ c r hr hc) hnorm

/-- Total enclosed algebraic multiplicity is locally constant, even if individual
spectral values split or move within the disk. -/
theorem eventually_sum_enclosed_multiplicity_eq (hp : p ≠ ⊤) (φ : PairSpace p)
    (c : ℂ) (r : ℝ) (hr : 0 ≤ r) (hc : sphere c r ⊆ resolventSet hp φ) :
    ∀ᶠ ψ in 𝓝 φ,
      ∑ z ∈ enclosedPeriodicSpectrum hp ψ c r, periodicAlgebraicMultiplicity hp ψ z =
        ∑ z ∈ enclosedPeriodicSpectrum hp φ c r, periodicAlgebraicMultiplicity hp φ z := by
  filter_upwards [eventually_finrank_resolventCircleIntegral_eq hp φ c r hr hc] with ψ hψ
  rw [← finrank_range_resolventCircleIntegral hp ψ c r hr hψ.1,
    ← finrank_range_resolventCircleIntegral hp φ c r hr hc]
  exact hψ.2

end NLS.ZakharovShabat
