import NLS.ZakharovShabat.SourceEquation2_29
import NLS.ZakharovShabat.SourcePsiFullProductInterpolation
import NLS.ZakharovShabat.SourcePsiFullProductGapZeros
import NLS.SequenceSpaces.RealOperator

/-!
# Invertibility of the limit operator on the original real domain

The actual original contour action identifies every real kernel direction
with a full product variation vanishing once in each gap. Entire-function
uniqueness and original-disk separation force that direction to vanish.
Real matrix entries give complex injectivity; the Fredholm alternative
gives bijectivity. Only original disk placement and real roots are needed.
-/

noncomputable section
open Set Complex Metric Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem SourceLemma12_4Data.originalLimitOperator_apply_eq_fullProductContour
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (H : SourceLemma12_4Data hp hp1 W)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (φ : CoeffPair p) (hφW : φ ∈ W) (hφV : φ ∈ V)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (a : Coeff p) (ha : a ∈ sourcePsiOriginalRootPlacement D)
    (m : ℤ) (d r : ℝ) (hr : 0 < r) (he : D m = ball (d:ℂ) r) (h : Coeff p) :
    (sourcePsiOriginalLimitOperator hp hp1 a φ h) m =
      -(∮ z in C((d:ℂ),r), sourcePsiFullProductVariation a h z /
        sourceCanonicalRoot hp hp1 φ z)/(Real.pi:ℂ) := by
  let P := hD.periodCircle φ hφV m d r hr he
  let A : Coeff p →L[ℂ] ℂ := (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p m).comp
    (sourcePsiOriginalLimitOperator hp hp1 a φ)
  let B := sourcePsiFullProductContourDerivative hp hp1 a φ (d:ℂ) r
  have heq : A = B := by
    apply Coeff.continuousLinearMap_eq_of_single hp
    intro k
    change (sourcePsiOriginalLimitOperator hp hp1 a φ (lp.single p k 1)) m = _
    rw [H.originalLimitOperator_entry hD φ hφW hφV hφ a ha m k d r hr he]
    exact sourcePsiLimitMatrixEntry_eq_fullProductContourDerivative hp hp1 m k a φ hφ
      (d:ℂ) r hr.le P.sphere_subset_rootDomain
      (hD.originalRootPlacement_avoids_sphere a ha m k d r hr he)
  change A h = _
  rw [heq]
  exact sourcePsiFullProductContourDerivative_apply hp hp1 a h φ hφ (d:ℂ) r hr.le P.sphere_subset_rootDomain

theorem SourceLemma12_4Data.originalLimitOperator_realKernel_gapZeros
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (H : SourceLemma12_4Data hp hp1 W)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (φ : CoeffPair p) (hφW : φ ∈ W) (hφV : φ ∈ V)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (a : Coeff p) (ha : a ∈ sourcePsiOriginalRootPlacement D)
    (haReal : ∀ k : ℤ, (a k).im = 0)
    (h : Coeff p) (hreal : ∀ k : ℤ, (h k).im = 0)
    (hker : sourcePsiOriginalLimitOperator hp hp1 a φ h = 0) :
    ∃ ρ : ℤ → ℂ, Memℓp (fun m => ρ m-(Real.pi:ℂ)*m) p ∧
      ∀ m : ℤ, ρ m ∈ sourcePeriodicSegment hp hp1 φ m ∧
        sourcePsiFullProductVariation a h (ρ m) = 0 := by
  have hgap (m : ℤ) : ∃ μ ∈ sourcePeriodicSegment hp hp1 φ m,
      sourcePsiFullProductVariation a h μ = 0 := by
    obtain ⟨d,r,hr,he⟩ := hD.discs m
    let P := hD.periodCircle φ hφV m d r hr he
    have hi := H.originalLimitOperator_apply_eq_fullProductContour hD φ hφW hφV hφ a ha m d r hr he h
    rw [hker] at hi
    have hz : (∮ z in C((d:ℂ),r), sourcePsiFullProductVariation a h z /
        sourceCanonicalRoot hp hp1 φ z) = 0 := by
      have hπ : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      exact neg_eq_zero.mp ((div_eq_zero_iff.mp hi.symm).resolve_right hπ)
    exact exists_sourcePsiFullProductVariation_zero_on_realGap hp hp1 φ hφ m a h
      (fun k => by simp [displacedRoots,haReal]) hreal d r hr P.gap
      P.closedBall_subset_omittedDomain P.sphere_subset_rootDomain hz
  choose ρ hρ using hgap
  exact ⟨ρ,memℓp_sourcePeriodicSegment_samples hp hp1 φ ρ (fun m => (hρ m).1),hρ⟩

theorem SourceLemma12_4Data.originalLimitOperator_realKernel_eq_zero
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (H : SourceLemma12_4Data hp hp1 W)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (φ : CoeffPair p) (hφW : φ ∈ W) (hφV : φ ∈ V)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (a : Coeff p) (ha : a ∈ sourcePsiOriginalRootPlacement D)
    (haReal : ∀ k : ℤ, (a k).im = 0)
    (h : Coeff p) (hreal : ∀ k : ℤ, (h k).im = 0)
    (hker : sourcePsiOriginalLimitOperator hp hp1 a φ h = 0) : h = 0 := by
  obtain ⟨ρ,hρlp,hρ⟩ := H.originalLimitOperator_realKernel_gapZeros hD φ hφW hφV hφ a ha haReal h hreal hker
  have hz := sourcePsiFullProductVariation_eq_zero_of_gapZero_sequence hp hp1 φ hφ ρ hρlp
    (fun m => (hρ m).1) a h (fun m => (hρ m).2)
  exact sourcePsiFullProductVariation_zero_imp_direction_zero hp hp1 a h
    (hD.originalRootPlacement_injective a ha) (fun z => congrFun hz z)

theorem SourceLemma12_4Data.originalLimitOperator_entry_real
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (H : SourceLemma12_4Data hp hp1 W)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (φ : CoeffPair p) (hφW : φ ∈ W) (hφV : φ ∈ V)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (a : Coeff p) (ha : a ∈ sourcePsiOriginalRootPlacement D)
    (haReal : ∀ k : ℤ, (a k).im = 0) (m k : ℤ) :
    ((sourcePsiOriginalLimitOperator hp hp1 a φ (lp.single p k 1)) m).im = 0 := by
  let : NeBot (Filter.comap Int.natAbs atTop) :=
    (inferInstance : NeBot (atTop : Filter ℕ)).comap_of_surj Int.natAbs_surjective
  obtain ⟨d,r,hr,he⟩ := hD.discs m
  rw [H.originalLimitOperator_entry hD φ hφW hφV hφ a ha m k d r hr he]
  have hlim := (Complex.continuous_im.tendsto _).comp
    (H.originalJacobianEntry_tendsto hD φ hφW hφV hφ a ha m k d r hr he)
  have heq : (fun n : ℤ => (sourcePsiOriginalJacobianEntry hp hp1 n m k a φ).im) = fun _ => 0 :=
    funext (fun n => H.originalJacobianEntry_real φ hφW hφ n m k a haReal)
  change Tendsto (fun n : ℤ => (sourcePsiOriginalJacobianEntry hp hp1 n m k a φ).im) _ _ at hlim
  rw [heq] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

theorem SourceLemma12_4Data.originalLimitOperator_injective
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (H : SourceLemma12_4Data hp hp1 W)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (φ : CoeffPair p) (hφW : φ ∈ W) (hφV : φ ∈ V)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (a : Coeff p) (ha : a ∈ sourcePsiOriginalRootPlacement D)
    (haReal : ∀ k : ℤ, (a k).im = 0) :
    Function.Injective (sourcePsiOriginalLimitOperator hp hp1 a φ) :=
  Coeff.operator_injective_of_realKernelZero hp _
    (H.originalLimitOperator_entry_real hD φ hφW hφV hφ a ha haReal)
    (H.originalLimitOperator_realKernel_eq_zero hD φ hφW hφV hφ a ha haReal)

theorem SourceLemma12_4Data.originalLimitOperator_bijective
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (H : SourceLemma12_4Data hp hp1 W) (hW : IsOpen W)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c) (hV : IsOpen V)
    (φ : CoeffPair p) (hφW : φ ∈ W) (hφV : φ ∈ V)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (a : Coeff p) (ha : a ∈ sourcePsiOriginalRootPlacement D)
    (haReal : ∀ k : ℤ, (a k).im = 0) :
    Function.Bijective (sourcePsiOriginalLimitOperator hp hp1 a φ) :=
  (H.equation2_29 hW hD hV φ hφW hφV hφ a ha haReal).bijective_of_injective
    (H.originalLimitOperator_injective hD φ hφW hφV hφ a ha haReal)

end NLS.ZakharovShabat
