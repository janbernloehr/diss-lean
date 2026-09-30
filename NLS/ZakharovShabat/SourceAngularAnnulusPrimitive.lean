import NLS.ComplexAnalysis.AnnularHolomorphicPrimitive
import NLS.ComplexAnalysis.SegmentIsolatingCircles
import NLS.ZakharovShabat.SourceAngularIntegrand
import NLS.ZakharovShabat.SourcePsiEquationContourHomotopy

/-!
# Actual off-diagonal angular primitives around every spectral gap

The exact common contour normalization from Lemma 12.12 cancels the
annular period. Shrinking each assigned enclosing circle leaves a
nonempty annulus with a primitive of the literal canonical angular
integrand. The same annuli work simultaneously for all deleted indices.
-/

noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem sourceAngular_annulus_analyticOnNhd
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n m : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (ψ : CoeffPair p)
    (c : ℂ) (r R : ℝ)
    (hgap : sourcePeriodicSegment hp hp1 ψ m ⊆ ball c r)
    (hother : closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ m) :
    AnalyticOnNhd ℂ (fun z => sourceAngularIntegrand n s
      (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) (z,ψ)) (closedBall c R \ ball c r) := by
  apply (analyticOnNhd_sourcePsiContourIntegrand_fixed hp hp1 n (s n ψ : Coeff p) ψ).mono
  intro z hz k
  by_cases hkm : k = m
  · subst k
    exact fun h => hz.2 (hgap h)
  · exact (hother hz.1) k hkm

theorem sourceAngular_exists_annulus_primitive
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n m : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (ψ : CoeffPair p)
    (c : ℂ) (r R : ℝ) (hr : 0 < r) (hrR : r < R)
    (hgap : sourcePeriodicSegment hp hp1 ψ m ⊆ ball c r)
    (hother : closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ m)
    (hzero : sourcePsiContour hp hp1 n (s n ψ : Coeff p) ψ c r = 0) :
    ∃ F : ℂ → ℂ, ∀ z ∈ ball c R \ closedBall c r,
      HasDerivAt F (sourceAngularIntegrand n s
        (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) (z,ψ)) z := by
  apply exists_primitive_on_annulus_of_zero_period _ c r R hr hrR
    (sourceAngular_annulus_analyticOnNhd hp hp1 n m s ψ c r R hgap hother)
  change (2*Real.pi : ℂ)⁻¹ * (∮ z in C(c,r), sourceAngularIntegrand n s
    (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) (z,ψ)) = 0 at hzero
  exact (mul_eq_zero.mp hzero).resolve_left (inv_ne_zero (by simp [Real.pi_ne_zero]))

theorem sourceAngular_annulus_pathIntegral_eq_sub
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n m : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (ψ : CoeffPair p)
    (c : ℂ) (r R : ℝ)
    (hgap : sourcePeriodicSegment hp hp1 ψ m ⊆ ball c r)
    (hother : closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ m)
    (F : ℂ → ℂ) (hF : ∀ z ∈ ball c R \ closedBall c r,
      HasDerivAt F (sourceAngularIntegrand n s
        (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) (z,ψ)) z)
    {a b : ℂ} (γ : Path a b) (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (hγA : ∀ t : I, γ t ∈ ball c R \ closedBall c r) :
    CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand n s
      (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) (z,ψ))) γ ∧
      sourceAngularPathIntegral n s (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) ψ γ = F b-F a := by
  let f : ℂ → ℂ := fun z => sourceAngularIntegrand n s
    (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) (z,ψ)
  let A := ball c R \ closedBall c r
  have hA : A ⊆ closedBall c R \ ball c r := by
    intro z hz
    exact ⟨ball_subset_closedBall hz.1,fun h => hz.2 (ball_subset_closedBall h)⟩
  have hω : ContinuousOn (holomorphicOneForm f) A :=
    ((sourceAngular_annulus_analyticOnNhd hp hp1 n m s ψ c r R hgap hother).continuousOn.mono hA).smul
      continuousOn_const
  have hInt := hω.curveIntegrable_of_contDiffOn hγ hγA
  exact ⟨hInt,curveIntegral_eq_sub_of_primitive f F A hF γ hγ
    (fun t ht => by simpa only [Path.extend_apply γ ht] using hγA ⟨t,ht⟩) hInt⟩

namespace SourcePsiSquaredGapComplexExtension
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- Every complex source in the actual normalized psi domain has a
common all-gap family of annuli, each with primitives for every
off-diagonal angular integrand. No period assumption is supplied. -/
theorem exists_angular_annulus_primitives
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) :
    ∃ c : ℤ → ℂ, ∃ r R : ℤ → ℝ,
      (∀ m, 0 < r m ∧ r m < R m ∧
        sourcePeriodicSegment hp hp1 ψ m ⊆ ball (c m) (r m) ∧
        closedBall (c m) (R m) ⊆ sourceStandardRootOmittedDomain hp hp1 ψ m) ∧
      ∀ n m, m ≠ n → ∃ F : ℂ → ℂ, ∀ z ∈ ball (c m) (R m) \ closedBall (c m) (r m),
        HasDerivAt F (sourceAngularIntegrand n s
          (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) (z,ψ)) z := by
  obtain ⟨c,R,hfamily,horth⟩ := hs.contour_orthogonality ψ hψ
  have hinner : ∀ m : ℤ, ∃ r : ℝ, 0 < r ∧ r < R m ∧
      sourcePeriodicSegment hp hp1 ψ m ⊆ ball (c m) r := by
    intro m
    obtain ⟨r,ρ,hr,hrρ,hρR,hseg⟩ := exists_nested_radii_of_segment_subset_ball
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)
      (c m) (R m) (hfamily.2 m).2.1
    exact ⟨r,hr,hrρ.trans hρR,hseg⟩
  choose r hr hrR hseg using hinner
  refine ⟨c,r,R,fun m => ⟨hr m,hrR m,hseg m,(hfamily.2 m).2.2.1⟩,?_⟩
  intro n m hmn
  apply sourceAngular_exists_annulus_primitive hp hp1 n m s ψ (c m) (r m) (R m)
    (hr m) (hrR m) (hseg m) (hfamily.2 m).2.2.1
  rw [sourcePsiContour_eq_of_nested_enclosingCircles hp hp1 n m (s n ψ : Coeff p) ψ
    (c m) (c m) (r m) (R m) (hr m) (hfamily.2 m).1 (hseg m) (hfamily.2 m).2.1
    (closedBall_subset_closedBall (hrR m).le) (hfamily.2 m).2.2.1]
  simpa only [if_neg hmn] using horth n m

/-- The actual integrals of all C¹ paths in these common annuli are
primitive endpoint differences. In particular, arbitrary winding
does not affect an off-diagonal integral and every such loop is zero. -/
theorem exists_angular_annulus_integral_formula
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) :
    ∃ c : ℤ → ℂ, ∃ r R : ℤ → ℝ,
      (∀ m, 0 < r m ∧ r m < R m ∧
        sourcePeriodicSegment hp hp1 ψ m ⊆ ball (c m) (r m) ∧
        closedBall (c m) (R m) ⊆ sourceStandardRootOmittedDomain hp hp1 ψ m) ∧
      ∀ n m, m ≠ n → ∃ F : ℂ → ℂ,
        (∀ z ∈ ball (c m) (R m) \ closedBall (c m) (r m),
          HasDerivAt F (sourceAngularIntegrand n s
            (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) (z,ψ)) z) ∧
        ∀ {a b : ℂ} (γ : Path a b), ContDiffOn ℝ 1 γ.extend (Icc 0 1) →
          (∀ t : I, γ t ∈ ball (c m) (R m) \ closedBall (c m) (r m)) →
          CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand n s
            (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) (z,ψ))) γ ∧
            sourceAngularPathIntegral n s (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) ψ γ = F b-F a := by
  obtain ⟨c,r,R,hgeom,hprim⟩ := hs.exists_angular_annulus_primitives ψ hψ
  refine ⟨c,r,R,hgeom,?_⟩
  intro n m hmn
  obtain ⟨F,hF⟩ := hprim n m hmn
  refine ⟨F,hF,?_⟩
  intro a b γ hγ hγA
  exact sourceAngular_annulus_pathIntegral_eq_sub hp hp1 n m s ψ (c m) (r m) (R m)
    (hgeom m).2.2.1 (hgeom m).2.2.2 F hF γ hγ hγA

end SourcePsiSquaredGapComplexExtension
end NLS.ZakharovShabat
