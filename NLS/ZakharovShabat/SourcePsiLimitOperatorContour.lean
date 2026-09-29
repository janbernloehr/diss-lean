import NLS.ZakharovShabat.SourcePsiFullProductContourVariation
import NLS.ZakharovShabat.SourcePsiJacobianNormLimit
import NLS.SequenceSpaces.OperatorBasisExt

/-!
# Directional contour formula for the actual limit operator

The limit matrix entries are full-product variation contours on basis
directions. Both the bounded limit operator and the contour derivative
are continuous linear maps, so density extends the identity to every
root direction. The fixed-root norm limit, compact correction, and
contour formula below share the same operator and contour family.
-/

noncomputable section
open Set Filter Topology Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Roots in their indexed real periodic gaps are pairwise distinct,
including when individual gaps collapse. -/
theorem displacedRoots_injective_of_periodicGapRootSet
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (a : Coeff p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (ha : a ∈ sourcePeriodicGapRootSet hp hp1 φ) :
    Function.Injective (displacedRoots a) := by
  have hmono : StrictMono (fun m : ℤ => (displacedRoots a m).re) := by
    intro i j hij
    have hi := sourcePeriodicSegment_re_mem_Icc hp hp1 φ i
      (displacedRoots a i) (ha i)
    have hj := sourcePeriodicSegment_re_mem_Icc hp hp1 φ j
      (displacedRoots a j) (ha j)
    exact hi.2.trans_lt ((canonicalPeriodicRight_re_lt_left_of_lt hp hp1
      (periodOnePotential φ) (periodOnePotential_mem φ)
      (isRealType_periodOnePotential φ hφ) hij).trans_le hj.1)
  intro i j hij
  exact hmono.injective (congrArg Complex.re hij)

/-- On the dissertation's full gap product, an identically zero
variation recovers the zero direction without an extra separation
assumption. -/
theorem sourcePsiFullProductVariation_zero_imp_direction_zero_of_gapRoots
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (a h : Coeff p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (ha : a ∈ sourcePeriodicGapRootSet hp hp1 φ)
    (hvariation : ∀ z : ℂ, sourcePsiFullProductVariation a h z = 0) :
    h = 0 :=
  sourcePsiFullProductVariation_zero_imp_direction_zero hp hp1 a h
    (displacedRoots_injective_of_periodicGapRootSet hp hp1 a φ hφ ha) hvariation

/-- The apparent row-dependent limit integrand is the negative full
product variation in a basis direction, over the canonical root. -/
theorem sourcePsiLimitMatrixIntegrand_eq_fullProductVariation_single
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (m k : ℤ) (a : Coeff p) (φ : CoeffPair p) (z : ℂ)
    (hz : z ∈ sourceCanonicalRootDomain hp hp1 φ)
    (hzk : z ≠ displacedRoots a k) :
    sourcePsiLimitMatrixIntegrand hp hp1 m k a φ z =
      -(sourcePsiFullProductVariation a (lp.single p k 1) z /
        sourceCanonicalRoot hp hp1 φ z) := by
  have hgap := sourcePsiContourIntegrandJoint_eq_gap_factor
    hp hp1 k m a φ z hz hzk
  calc
    sourcePsiLimitMatrixIntegrand hp hp1 m k a φ z =
        ((displacedRoots a m-z) / sourceStandardRoot hp hp1 φ m z) *
          sourcePsiGapRegularFactor hp hp1 k m a φ z := by
      simp only [sourcePsiLimitMatrixIntegrand, sourcePsiGapRegularFactor,
        div_eq_mul_inv]
      ring
    _ = sourcePsiContourIntegrandJoint hp hp1 k (z,(a,φ)) := hgap.symm
    _ = -(sourcePsiFullProductVariation a (lp.single p k 1) z /
        sourceCanonicalRoot hp hp1 φ z) := by
      rw [sourcePsiFullProductVariation_single hp hp1]
      simp [sourcePsiContourIntegrandJoint, div_eq_mul_inv]

/-- Each scalar limit matrix entry is the corresponding value of the
continuous full-product contour derivative. -/
theorem sourcePsiLimitMatrixEntry_eq_fullProductContourDerivative
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (m k : ℤ) (a : Coeff p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hcircle : sphere c R ⊆ sourceCanonicalRootDomain hp hp1 φ)
    (havoid : ∀ z ∈ sphere c R, z ≠ displacedRoots a k) :
    sourcePsiLimitMatrixEntry hp hp1 m k a φ c R =
      sourcePsiFullProductContourDerivative hp hp1 a φ c R (lp.single p k 1) := by
  rw [sourcePsiFullProductContourDerivative_apply hp hp1 a
    (lp.single p k 1) φ hφ c R hR hcircle]
  unfold sourcePsiLimitMatrixEntry
  have hintegrand : EqOn (sourcePsiLimitMatrixIntegrand hp hp1 m k a φ)
      (fun z => (-1 : ℂ) * (sourcePsiFullProductVariation a (lp.single p k 1) z /
        sourceCanonicalRoot hp hp1 φ z)) (sphere c R) := by
    intro z hz
    simpa using sourcePsiLimitMatrixIntegrand_eq_fullProductVariation_single
      hp hp1 m k a φ z (hcircle hz) (havoid z hz)
  rw [circleIntegral.integral_congr hR hintegrand, circleIntegral.integral_const_mul]
  simp

/-- A bounded operator with the actual limit matrix entries acts by
the full variation contour on every `ℓᵖ` direction. -/
theorem sourcePsiLimitMatrixOperator_apply_eq_fullProductContour
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (a : Coeff p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (ha : a ∈ sourcePeriodicGapRootSet hp hp1 φ)
    (c : ℤ → ℂ) (R : ℤ → ℝ)
    (hR : ∀ m : ℤ, 0 ≤ R m)
    (hcircle : ∀ m : ℤ, sphere (c m) (R m) ⊆ sourceCanonicalRootDomain hp hp1 φ)
    (Qstar : Coeff p →L[ℂ] Coeff p)
    (hentry : ∀ m k : ℤ, (Qstar (lp.single p k 1)) m =
      sourcePsiLimitMatrixEntry hp hp1 m k a φ (c m) (R m))
    (h : Coeff p) (m : ℤ) :
    (Qstar h) m = -(∮ z in C(c m,R m), sourcePsiFullProductVariation a h z /
      sourceCanonicalRoot hp hp1 φ z) / (Real.pi : ℂ) := by
  let A : Coeff p →L[ℂ] ℂ :=
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p m).comp Qstar
  let B := sourcePsiFullProductContourDerivative hp hp1 a φ (c m) (R m)
  have heq : A = B := by
    apply Coeff.continuousLinearMap_eq_of_single hp
    intro k
    change (Qstar (lp.single p k 1)) m = _
    rw [hentry]
    apply sourcePsiLimitMatrixEntry_eq_fullProductContourDerivative
      hp hp1 m k a φ hφ (c m) (R m) (hR m) (hcircle m)
    intro z hz hzk
    exact (hcircle m hz k) (hzk.symm ▸ ha k)
  change A h = _
  rw [heq]
  exact sourcePsiFullProductContourDerivative_apply
    hp hp1 a h φ hφ (c m) (R m) (hR m) (hcircle m)

/-- The kernel of the bounded contour-limit operator is exactly the
directions whose full variation has zero contour around every gap. -/
theorem sourcePsiLimitMatrixOperator_kernel_iff_fullProductContours_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (a : Coeff p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (ha : a ∈ sourcePeriodicGapRootSet hp hp1 φ)
    (c : ℤ → ℂ) (R : ℤ → ℝ) (hR : ∀ m : ℤ, 0 ≤ R m)
    (hcircle : ∀ m : ℤ, sphere (c m) (R m) ⊆ sourceCanonicalRootDomain hp hp1 φ)
    (Qstar : Coeff p →L[ℂ] Coeff p)
    (hentry : ∀ m k : ℤ, (Qstar (lp.single p k 1)) m =
      sourcePsiLimitMatrixEntry hp hp1 m k a φ (c m) (R m))
    (h : Coeff p) :
    Qstar h = 0 ↔ ∀ m : ℤ, (∮ z in C(c m,R m),
      sourcePsiFullProductVariation a h z / sourceCanonicalRoot hp hp1 φ z) = 0 := by
  have hformula := sourcePsiLimitMatrixOperator_apply_eq_fullProductContour
    hp hp1 a φ hφ ha c R hR hcircle Qstar hentry h
  constructor
  · intro hzero m
    have hvalue := hformula m
    rw [hzero] at hvalue
    have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hneg := (div_eq_zero_iff.mp hvalue.symm).resolve_right hπ
    exact neg_eq_zero.mp hneg
  · intro hzero
    ext m
    simp [hformula m, hzero m]

/-- The actual fixed-root norm limit and compact correction admit
the directional contour formula on the same selected circles. -/
theorem exists_sourcePsiLimitMatrixOperator_normLimit_compact_contour_realCentered
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (a : Coeff p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (ha : a ∈ sourcePeriodicGapRootSet hp hp1 φ) :
    ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ,
      (∀ m : ℤ, (c m).im = 0) ∧
      (∀ m : ℤ,
        0 < R m ∧ sourcePeriodicSegment hp hp1 φ m ⊆ ball (c m) (R m) ∧
        closedBall (c m) (R m) ⊆ sourceStandardRootOmittedDomain hp hp1 φ m ∧
        sphere (c m) (R m) ⊆ sourceCanonicalRootDomain hp hp1 φ) ∧
      ∃ Qstar : Coeff p →L[ℂ] Coeff p, ∃ M : ℝ,
        0 ≤ M ∧ ‖Qstar‖ ≤ M ∧
        (∀ᶠ n : ℤ in Filter.comap Int.natAbs Filter.atTop,
          ‖sourcePsiFullRootJacobian hp hp1 n c R
            (Coeff.deleteCoordinateTo n a) φ‖ ≤ M) ∧
        (∀ m k : ℤ, (Qstar (lp.single p k 1)) m =
          sourcePsiLimitMatrixEntry hp hp1 m k a φ (c m) (R m)) ∧
        Tendsto (fun n : ℤ => sourcePsiFullRootJacobian hp hp1 n c R
          (Coeff.deleteCoordinateTo n a) φ)
          (Filter.comap Int.natAbs Filter.atTop) (𝓝 Qstar) ∧
        IsCompactOperator (Qstar - (2 : ℂ) • ContinuousLinearMap.id ℂ (Coeff p)) ∧
        (Function.Injective Qstar → Function.Bijective Qstar) ∧
        (∀ h : Coeff p, ∀ m : ℤ, (Qstar h) m =
          -(∮ z in C(c m,R m), sourcePsiFullProductVariation a h z /
            sourceCanonicalRoot hp hp1 φ z) / (Real.pi : ℂ)) := by
  obtain ⟨c,R,hcReal,hgeom,Qstar,M,hM,hQnorm,hbound,hentry,hlimit,hcompact,hbij⟩ :=
    exists_sourcePsiLimitMatrixOperator_normLimit_compact_realCentered hp hp1 a φ hφ ha
  refine ⟨c,R,hcReal,hgeom,Qstar,M,hM,hQnorm,hbound,hentry,hlimit,hcompact,hbij,?_⟩
  exact sourcePsiLimitMatrixOperator_apply_eq_fullProductContour
    hp hp1 a φ hφ ha c R (fun m => (hgeom m).1.le)
    (fun m => (hgeom m).2.2.2) Qstar hentry

/-- Compatibility form of the real-centered construction, retaining
the original statement. -/
theorem exists_sourcePsiLimitMatrixOperator_normLimit_compact_contour
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (a : Coeff p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (ha : a ∈ sourcePeriodicGapRootSet hp hp1 φ) :
    ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ,
      (∀ m : ℤ,
        0 < R m ∧ sourcePeriodicSegment hp hp1 φ m ⊆ ball (c m) (R m) ∧
        closedBall (c m) (R m) ⊆ sourceStandardRootOmittedDomain hp hp1 φ m ∧
        sphere (c m) (R m) ⊆ sourceCanonicalRootDomain hp hp1 φ) ∧
      ∃ Qstar : Coeff p →L[ℂ] Coeff p, ∃ M : ℝ,
        0 ≤ M ∧ ‖Qstar‖ ≤ M ∧
        (∀ᶠ n : ℤ in Filter.comap Int.natAbs Filter.atTop,
          ‖sourcePsiFullRootJacobian hp hp1 n c R
            (Coeff.deleteCoordinateTo n a) φ‖ ≤ M) ∧
        (∀ m k : ℤ, (Qstar (lp.single p k 1)) m =
          sourcePsiLimitMatrixEntry hp hp1 m k a φ (c m) (R m)) ∧
        Tendsto (fun n : ℤ => sourcePsiFullRootJacobian hp hp1 n c R
          (Coeff.deleteCoordinateTo n a) φ)
          (Filter.comap Int.natAbs Filter.atTop) (𝓝 Qstar) ∧
        IsCompactOperator (Qstar - (2 : ℂ) • ContinuousLinearMap.id ℂ (Coeff p)) ∧
        (Function.Injective Qstar → Function.Bijective Qstar) ∧
        (∀ h : Coeff p, ∀ m : ℤ, (Qstar h) m =
          -(∮ z in C(c m,R m), sourcePsiFullProductVariation a h z /
            sourceCanonicalRoot hp hp1 φ z) / (Real.pi : ℂ)) := by
  obtain ⟨c,R,_,hdata⟩ :=
    exists_sourcePsiLimitMatrixOperator_normLimit_compact_contour_realCentered hp hp1 a φ hφ ha
  exact ⟨c,R,hdata⟩

end NLS.ZakharovShabat
