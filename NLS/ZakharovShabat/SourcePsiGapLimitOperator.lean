import NLS.ZakharovShabat.SourcePsiLimitBijective
import NLS.ZakharovShabat.SourcePsiRealContourComparison

/-!
# A contour-independent limit operator on the full gap product

Each limit entry is twice the normalized psi contour in its input
index. Real-centered contour comparison therefore identifies all
valid choices. The bounded operator is unique by density, and its
intrinsic realization on the gap product is pointwise bijective.
-/

noncomputable section
open Set Filter Topology Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A real-centered contour family enclosing each assigned gap and
whose filled discs avoid all other gaps. -/
def sourcePsiRealCenteredContourFamily
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (c : ℤ → ℂ) (R : ℤ → ℝ) : Prop :=
  (∀ m : ℤ, (c m).im = 0) ∧
  ∀ m : ℤ, 0 < R m ∧
    sourcePeriodicSegment hp hp1 φ m ⊆ ball (c m) (R m) ∧
    closedBall (c m) (R m) ⊆ sourceStandardRootOmittedDomain hp hp1 φ m ∧
    sphere (c m) (R m) ⊆ sourceCanonicalRootDomain hp hp1 φ

theorem sourcePsiLimitMatrixEntry_eq_two_mul_contour
    (hp : p ≠ ⊤) (hp1 : 1 < p) (a : Coeff p) (φ : CoeffPair p)
    (ha : a ∈ sourcePeriodicGapRootSet hp hp1 φ)
    (m k : ℤ) (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hcircle : sphere c R ⊆ sourceCanonicalRootDomain hp hp1 φ) :
    sourcePsiLimitMatrixEntry hp hp1 m k a φ c R =
      2 * sourcePsiContour hp hp1 k a φ c R := by
  have hintegrand : EqOn (sourcePsiLimitMatrixIntegrand hp hp1 m k a φ)
      (fun z => sourcePsiContourIntegrandJoint hp hp1 k (z,(a,φ))) (sphere c R) := by
    intro z hz
    have hzk : z ≠ displacedRoots a k := by
      intro heq
      exact (hcircle hz k) (heq.symm ▸ ha k)
    rw [sourcePsiLimitMatrixIntegrand_eq_fullProductVariation_single
      hp hp1 m k a φ z (hcircle hz) hzk,
      sourcePsiFullProductVariation_single hp hp1]
    simp [sourcePsiContourIntegrandJoint,div_eq_mul_inv]
  unfold sourcePsiLimitMatrixEntry
  rw [circleIntegral.integral_congr hR hintegrand]
  simp [sourcePsiContour,div_eq_mul_inv]
  ring

/-- Actual limit entries agree across any two valid real-centered
families, including choices made at different numerator roots. -/
theorem sourcePsiLimitMatrixEntry_eq_of_realCentered_families
    (hp : p ≠ ⊤) (hp1 : 1 < p) (a : Coeff p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (ha : a ∈ sourcePeriodicGapRootSet hp hp1 φ)
    (c₀ c₁ : ℤ → ℂ) (R₀ R₁ : ℤ → ℝ)
    (h₀ : sourcePsiRealCenteredContourFamily hp hp1 φ c₀ R₀)
    (h₁ : sourcePsiRealCenteredContourFamily hp hp1 φ c₁ R₁) (m k : ℤ) :
    sourcePsiLimitMatrixEntry hp hp1 m k a φ (c₀ m) (R₀ m) =
      sourcePsiLimitMatrixEntry hp hp1 m k a φ (c₁ m) (R₁ m) := by
  rw [sourcePsiLimitMatrixEntry_eq_two_mul_contour hp hp1 a φ ha m k
    (c₀ m) (R₀ m) (h₀.2 m).1.le (h₀.2 m).2.2.2,
    sourcePsiLimitMatrixEntry_eq_two_mul_contour hp hp1 a φ ha m k
      (c₁ m) (R₁ m) (h₁.2 m).1.le (h₁.2 m).2.2.2]
  congr 1
  exact sourcePsiContour_eq_of_realCentered_enclosingCircles hp hp1 k m a φ hφ
    (c₀ m) (c₁ m) (R₀ m) (R₁ m) (h₀.1 m) (h₁.1 m)
    (h₀.2 m).1 (h₁.2 m).1 (h₀.2 m).2.1 (h₁.2 m).2.1
    (h₀.2 m).2.2.1 (h₁.2 m).2.2.1

/-- One bounded bijective operator realizes the limit entries on
every valid real-centered contour family. -/
theorem exists_sourcePsiGapLimitOperator
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (a : sourcePeriodicGapRootSet hp hp1 φ) :
    ∃ Q : Coeff p →L[ℂ] Coeff p,
      Function.Bijective Q ∧
      ∀ c : ℤ → ℂ, ∀ R : ℤ → ℝ,
        sourcePsiRealCenteredContourFamily hp hp1 φ c R →
        ∀ m k : ℤ, (Q (lp.single p k 1)) m =
          sourcePsiLimitMatrixEntry hp hp1 m k a.val φ (c m) (R m) := by
  obtain ⟨c₀,R₀,hcenter,hgeom,Q,hentry,_,_,hbij⟩ :=
    exists_sourcePsiLimitMatrixOperator_normLimit_bijective hp hp1 a.val φ hφ a.property
  refine ⟨Q,hbij,?_⟩
  intro c R hfamily m k
  rw [hentry]
  exact sourcePsiLimitMatrixEntry_eq_of_realCentered_families
    hp hp1 a.val φ hφ a.property c₀ c R₀ R ⟨hcenter,hgeom⟩ hfamily m k

/-- The intrinsic bounded limit operator at a full gap-root vector. -/
def sourcePsiGapLimitOperator
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (a : sourcePeriodicGapRootSet hp hp1 φ) : Coeff p →L[ℂ] Coeff p :=
  Classical.choose (exists_sourcePsiGapLimitOperator hp hp1 φ hφ a)

theorem sourcePsiGapLimitOperator_bijective
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (a : sourcePeriodicGapRootSet hp hp1 φ) :
    Function.Bijective (sourcePsiGapLimitOperator hp hp1 φ hφ a) :=
  (Classical.choose_spec (exists_sourcePsiGapLimitOperator hp hp1 φ hφ a)).1

theorem sourcePsiGapLimitOperator_entry
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (a : sourcePeriodicGapRootSet hp hp1 φ) (c : ℤ → ℂ) (R : ℤ → ℝ)
    (hfamily : sourcePsiRealCenteredContourFamily hp hp1 φ c R) (m k : ℤ) :
    (sourcePsiGapLimitOperator hp hp1 φ hφ a (lp.single p k 1)) m =
      sourcePsiLimitMatrixEntry hp hp1 m k a.val φ (c m) (R m) :=
  (Classical.choose_spec (exists_sourcePsiGapLimitOperator hp hp1 φ hφ a)).2
    c R hfamily m k

/-- Any bounded operator with the actual contour entries is this
intrinsic limit operator. -/
theorem sourcePsiGapLimitOperator_eq_of_entries
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (a : sourcePeriodicGapRootSet hp hp1 φ) (c : ℤ → ℂ) (R : ℤ → ℝ)
    (hfamily : sourcePsiRealCenteredContourFamily hp hp1 φ c R)
    (Q : Coeff p →L[ℂ] Coeff p)
    (hentry : ∀ m k : ℤ, (Q (lp.single p k 1)) m =
      sourcePsiLimitMatrixEntry hp hp1 m k a.val φ (c m) (R m)) :
    sourcePsiGapLimitOperator hp hp1 φ hφ a = Q := by
  apply Coeff.continuousLinearMap_eq_of_single hp
  intro k
  ext m
  rw [sourcePsiGapLimitOperator_entry hp hp1 φ hφ a c R hfamily m k,hentry]

/-- The intrinsic operator retains the actual fixed-root norm limit
and compact correction on one common real-centered contour family. -/
theorem exists_contours_tendsto_sourcePsiGapLimitOperator
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (a : sourcePeriodicGapRootSet hp hp1 φ) :
    ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ,
      sourcePsiRealCenteredContourFamily hp hp1 φ c R ∧
      Tendsto (fun n : ℤ => sourcePsiFullRootJacobian hp hp1 n c R
        (Coeff.deleteCoordinateTo n a.val) φ)
        (Filter.comap Int.natAbs Filter.atTop) (𝓝 (sourcePsiGapLimitOperator hp hp1 φ hφ a)) ∧
      IsCompactOperator (sourcePsiGapLimitOperator hp hp1 φ hφ a -
        (2:ℂ) • ContinuousLinearMap.id ℂ (Coeff p)) := by
  obtain ⟨c,R,hcenter,hgeom,Q,hentry,hlimit,hcompact,_⟩ :=
    exists_sourcePsiLimitMatrixOperator_normLimit_bijective hp hp1 a.val φ hφ a.property
  have heq := sourcePsiGapLimitOperator_eq_of_entries hp hp1 φ hφ a c R ⟨hcenter,hgeom⟩ Q hentry
  exact ⟨c,R,⟨hcenter,hgeom⟩,heq.symm ▸ hlimit,heq.symm ▸ hcompact⟩

end NLS.ZakharovShabat
