import NLS.ComplexAnalysis.PrimitiveRemovableBoundary
import NLS.ZakharovShabat.SourceCriticalRootRatioPrimitiveBoundary
import NLS.ZakharovShabat.SourceCriticalRootRatioCollapsed

/-! # Endpoint-normalized abelian primitives on both half-planes

For every real source and signed gap index, the critical-root quotient
has a uniquely endpoint-normalized primitive above and below the real
axis. Both endpoints have boundary value zero, including collapsed gaps.
These are the half-plane restrictions needed to construct Section 19's
abelian integrals; gluing and joint source analyticity are separate steps.
-/
noncomputable section
open Set Metric Filter Topology Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Choose the upper (`true`) or lower (`false`) open spectral half-plane. -/
def sourceAbelianHalfPlane (upper : Bool) : Set ℂ :=
  if upper then {z | 0 < z.im} else {z | z.im < 0}

theorem isOpen_sourceAbelianHalfPlane (upper : Bool) : IsOpen (sourceAbelianHalfPlane upper) := by
  cases upper
  · exact isOpen_lt continuous_im continuous_const
  · exact isOpen_lt continuous_const continuous_im

theorem convex_sourceAbelianHalfPlane (upper : Bool) : Convex ℝ (sourceAbelianHalfPlane upper) := by
  have hlin : IsLinearMap ℝ (fun z : ℂ => z.im) := ⟨by simp,by simp⟩
  cases upper
  · exact convex_halfSpace_lt hlin 0
  · exact convex_halfSpace_gt hlin 0

theorem nhdsWithin_sourceAbelianHalfPlane_neBot (upper : Bool) (c : ℂ) (hc : c.im = 0) :
    NeBot (𝓝[sourceAbelianHalfPlane upper] c) := by
  apply mem_closure_iff_nhdsWithin_neBot.mp
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  let y : ℝ := if upper then ε/2 else -(ε/2)
  refine ⟨c+(y:ℂ)*I,?_,?_⟩
  · cases upper <;> simp [sourceAbelianHalfPlane,y,hc] <;> linarith
  · have he : c-(c+(y:ℂ)*I) = -((y:ℂ)*I) := by ring
    rw [dist_eq_norm,he,norm_neg,norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs]
    cases upper <;> simp [y,abs_of_pos (half_pos hε)] <;> linarith

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The selected half-plane avoids every periodic cut of a real source. -/
theorem sourceAbelianHalfPlane_subset_rootDomain (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) (upper : Bool) :
    sourceAbelianHalfPlane upper ⊆ sourceCanonicalRootDomain hp hp1 φ := by
  intro z hz
  apply sourceCanonicalRootDomain_of_im_ne_zero hp hp1 φ hφ z
  cases upper
  · exact ne_of_lt hz
  · exact ne_of_gt hz

/-- Every half-plane primitive has a common finite endpoint limit at any gap,
with collapsed gaps handled by the proved removable extension. -/
theorem sourceAbelianHalfPlane_primitive_common_boundary
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) (upper : Bool)
    (F : ℂ → ℂ)
    (hF : ∀ z ∈ sourceAbelianHalfPlane upper, HasDerivAt F
      (deriv (canonicalDiscriminant hp (periodOnePotential φ)) z / sourceCanonicalRoot hp hp1 φ z) z) :
    ∃ A : ℂ,
      Tendsto F (𝓝[sourceAbelianHalfPlane upper]
        (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n)) (𝓝 A) ∧
      Tendsto F (𝓝[sourceAbelianHalfPlane upper]
        (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n)) (𝓝 A) := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n
  by_cases hopen : l.re < r.re
  · cases upper
    · exact sourceCriticalRootRatio_lowerPrimitive_common_boundary_limit hp hp1 φ hφ n hopen F hF
    · exact sourceCriticalRootRatio_upperPrimitive_common_boundary_limit hp hp1 φ hφ n hopen F hF
  · have hle : l.re ≤ r.re := NLS.ComplexAnalysis.re_le_of_complexLexLE
      ((canonicalPeriodicEndpoints_spec hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ)).2.1 n)
    obtain ⟨hl,hr⟩ := canonicalPeriodicEndpoints_im_eq_zero_of_realType hp hp1
      (periodOnePotential φ) (periodOnePotential_mem φ) (isRealType_periodOnePotential φ hφ) n
    have he : l = r := Complex.ext (le_antisymm hle (le_of_not_gt hopen)) (hl.trans hr.symm)
    have hgap : sourcePeriodicGapDisplacement hp hp1 φ n = 0 := by
      rw [sourcePeriodicGapDisplacement_apply]
      exact sub_eq_zero.mpr he.symm
    obtain ⟨W,_,hrealW,hdata⟩ := exists_global_sourceCriticalRootRatio_analytic_of_zeroGap hp hp1
    have hg := hdata φ (hrealW hφ) n hgap
    have hlmem : l ∈ sourceStandardRootOmittedDomain hp hp1 φ n := by
      apply sourceStandardRootGapSegment_subset_omittedDomain_of_realType hp hp1 φ hφ n
      refine ⟨-1,by norm_num,?_⟩
      exact sourceCanonicalRootGapPoint_neg_one_eq_left hp hp1 φ n
    obtain ⟨A,hA⟩ := NLS.ComplexAnalysis.exists_primitive_boundary_limit_of_derivative_extension
      (fun z => deriv (canonicalDiscriminant hp (periodOnePotential φ)) z / sourceCanonicalRoot hp hp1 φ z)
      F (sourceCriticalRootRatioExtension hp hp1 n φ) (sourceAbelianHalfPlane upper)
      (sourceStandardRootOmittedDomain hp hp1 φ n) l
      (isOpen_sourceAbelianHalfPlane upper) (convex_sourceAbelianHalfPlane upper)
      (isOpen_sourceStandardRootOmittedDomain_of_realType hp hp1 φ hφ n) hlmem hF hg.1
      (fun z hz => (hg.2 z (sourceAbelianHalfPlane_subset_rootDomain hp hp1 φ hφ upper hz.1)).symm)
    refine ⟨A,hA,?_⟩
    change Tendsto F (𝓝[sourceAbelianHalfPlane upper] r) (𝓝 A)
    rw [← he]
    exact hA

/-- Existence with the Section 19 endpoint normalization on each full half-plane. -/
theorem exists_sourceAbelianHalfPlane_primitive
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) (upper : Bool) :
    ∃ F : ℂ → ℂ,
      (∀ z ∈ sourceAbelianHalfPlane upper, HasDerivAt F
        (deriv (canonicalDiscriminant hp (periodOnePotential φ)) z / sourceCanonicalRoot hp hp1 φ z) z) ∧
      Tendsto F (𝓝[sourceAbelianHalfPlane upper]
        (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n)) (𝓝 0) ∧
      Tendsto F (𝓝[sourceAbelianHalfPlane upper]
        (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n)) (𝓝 0) := by
  have hex : ∃ G : ℂ → ℂ, ∀ z ∈ sourceAbelianHalfPlane upper, HasDerivAt G
      (deriv (canonicalDiscriminant hp (periodOnePotential φ)) z / sourceCanonicalRoot hp hp1 φ z) z := by
    cases upper
    · exact exists_sourceCriticalRootRatio_lowerHalfPlane_primitive hp hp1 φ hφ
    · exact exists_sourceCriticalRootRatio_upperHalfPlane_primitive hp hp1 φ hφ
  obtain ⟨G,hG⟩ := hex
  obtain ⟨A,hl,hr⟩ := sourceAbelianHalfPlane_primitive_common_boundary hp hp1 φ hφ n upper G hG
  refine ⟨fun z => G z-A,fun z hz => (hG z hz).sub_const A,?_,?_⟩
  · simpa only [sub_self] using hl.sub_const A
  · simpa only [sub_self] using hr.sub_const A

/-- The endpoint-normalized abelian integral on one complete half-plane. -/
def sourceAbelianHalfPlanePrimitive (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) (upper : Bool) : ℂ → ℂ :=
  Classical.choose (exists_sourceAbelianHalfPlane_primitive hp hp1 φ hφ n upper)

theorem sourceAbelianHalfPlanePrimitive_spec (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) (upper : Bool) :
    (∀ z ∈ sourceAbelianHalfPlane upper, HasDerivAt (sourceAbelianHalfPlanePrimitive hp hp1 φ hφ n upper)
      (deriv (canonicalDiscriminant hp (periodOnePotential φ)) z / sourceCanonicalRoot hp hp1 φ z) z) ∧
    Tendsto (sourceAbelianHalfPlanePrimitive hp hp1 φ hφ n upper) (𝓝[sourceAbelianHalfPlane upper]
      (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n)) (𝓝 0) ∧
    Tendsto (sourceAbelianHalfPlanePrimitive hp hp1 φ hφ n upper) (𝓝[sourceAbelianHalfPlane upper]
      (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n)) (𝓝 0) :=
  Classical.choose_spec (exists_sourceAbelianHalfPlane_primitive hp hp1 φ hφ n upper)

/-- Normalization makes the values independent of every primitive construction choice. -/
theorem sourceAbelianHalfPlanePrimitive_eq_of_normalized
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) (upper : Bool) (G : ℂ → ℂ)
    (hG : ∀ z ∈ sourceAbelianHalfPlane upper, HasDerivAt G
      (deriv (canonicalDiscriminant hp (periodOnePotential φ)) z / sourceCanonicalRoot hp hp1 φ z) z)
    (hGl : Tendsto G (𝓝[sourceAbelianHalfPlane upper]
      (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n)) (𝓝 0)) :
    EqOn (sourceAbelianHalfPlanePrimitive hp hp1 φ hφ n upper) G (sourceAbelianHalfPlane upper) := by
  have hs := sourceAbelianHalfPlanePrimitive_spec hp hp1 φ hφ n upper
  have hl := (canonicalPeriodicEndpoints_im_eq_zero_of_realType hp hp1
    (periodOnePotential φ) (periodOnePotential_mem φ) (isRealType_periodOnePotential φ hφ) n).1
  let := nhdsWithin_sourceAbelianHalfPlane_neBot upper _ hl
  exact NLS.ComplexAnalysis.primitives_eq_of_common_boundary_limit _ _ G _ _ 0
    (isOpen_sourceAbelianHalfPlane upper) (convex_sourceAbelianHalfPlane upper).isPreconnected
    hs.1 hG hs.2.1 hGl

end NLS.ZakharovShabat
