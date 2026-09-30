import NLS.ComplexAnalysis.PrimitiveOnDiscComplement
import NLS.ZakharovShabat.SourceAngularAnnulusPrimitive

/-!
# Actual off-diagonal angular primitives on entire isolating cut complements

Continue the exact annular primitives from Lemma 12.12 inward from
each moving midpoint. The closed gap segment is convex, so the radial
connectors cannot re-enter it. Every off-diagonal angular integrand
therefore has a primitive throughout its isolating disc minus its cut,
including at complex sources and collapsed gaps.
-/

noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem sourceAngular_discComplement_analyticOnNhd
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n m : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (ψ : CoeffPair p)
    (c : ℂ) (R : ℝ)
    (hother : closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ m) :
    AnalyticOnNhd ℂ (fun z => sourceAngularIntegrand n s
      (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) (z,ψ))
      (ball c R \ sourcePeriodicSegment hp hp1 ψ m) := by
  apply (analyticOnNhd_sourcePsiContourIntegrand_fixed hp hp1 n (s n ψ : Coeff p) ψ).mono
  intro z hz k
  by_cases hkm : k = m
  · subst k
    exact hz.2
  · exact (hother (ball_subset_closedBall hz.1)) k hkm

theorem sourceAngular_discComplement_pathIntegral_eq_sub
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n m : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (ψ : CoeffPair p)
    (c : ℂ) (R : ℝ)
    (hother : closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ m)
    (F : ℂ → ℂ) (hF : ∀ z ∈ ball c R \ sourcePeriodicSegment hp hp1 ψ m,
      HasDerivAt F (sourceAngularIntegrand n s
        (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) (z,ψ)) z)
    {a b : ℂ} (γ : Path a b) (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (hγD : ∀ t : I, γ t ∈ ball c R \ sourcePeriodicSegment hp hp1 ψ m) :
    CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand n s
      (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) (z,ψ))) γ ∧
      sourceAngularPathIntegral n s (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) ψ γ = F b-F a := by
  let f : ℂ → ℂ := fun z => sourceAngularIntegrand n s
    (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) (z,ψ)
  let D := ball c R \ sourcePeriodicSegment hp hp1 ψ m
  have hω : ContinuousOn (holomorphicOneForm f) D :=
    (sourceAngular_discComplement_analyticOnNhd hp hp1 n m s ψ c R hother).continuousOn.smul
      continuousOn_const
  have hInt := hω.curveIntegrable_of_contDiffOn hγ hγD
  exact ⟨hInt,curveIntegral_eq_sub_of_primitive f F D hF γ hγ
    (fun t ht => by simpa only [Path.extend_apply γ ht] using hγD ⟨t,ht⟩) hInt⟩

namespace SourcePsiSquaredGapComplexExtension
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The actual normalized psi family gives primitives throughout the
whole disc complement for every off-diagonal pair, using one common
all-gap family at each complex source. -/
theorem exists_angular_discComplement_primitives
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) :
    ∃ c : ℤ → ℂ, ∃ r R : ℤ → ℝ,
      (∀ m, 0 < r m ∧ r m < R m ∧
        sourcePeriodicSegment hp hp1 ψ m ⊆ ball (c m) (r m) ∧
        closedBall (c m) (R m) ⊆ sourceStandardRootOmittedDomain hp hp1 ψ m) ∧
      ∀ n m, m ≠ n → ∃ F : ℂ → ℂ,
        ∀ z ∈ ball (c m) (R m) \ sourcePeriodicSegment hp hp1 ψ m,
          HasDerivAt F (sourceAngularIntegrand n s
            (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) (z,ψ)) z := by
  obtain ⟨c,r,R,hgeom,hprim⟩ := hs.exists_angular_annulus_primitives ψ hψ
  refine ⟨c,r,R,hgeom,?_⟩
  intro n m hmn
  obtain ⟨G,hG⟩ := hprim n m hmn
  have hKclosed : IsClosed (sourcePeriodicSegment hp hp1 ψ m) := by
    apply IsCompact.isClosed
    change IsCompact (segment ℝ
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m))
    rw [segment_eq_image_lineMap]
    exact isCompact_Icc.image AffineMap.lineMap_continuous
  have hconv : Convex ℝ (sourcePeriodicSegment hp hp1 ψ m) := convex_segment _ _
  have hmid := sourcePeriodicMidpoint_mem_segment hp hp1 ψ m
  obtain ⟨F,_,hF⟩ := exists_primitive_on_disc_complement_of_annular_primitive
    _ G (c m) (sourceStandardRootMidpoint hp hp1 ψ m) (r m) (R m)
    (hgeom m).1.le (hgeom m).2.1 (sourcePeriodicSegment hp hp1 ψ m) hKclosed hmid
    (hconv.starConvex hmid) (hgeom m).2.2.1
    (sourceAngular_discComplement_analyticOnNhd hp hp1 n m s ψ (c m) (R m) (hgeom m).2.2.2) hG
  exact ⟨F,hF⟩

/-- Every regular C¹ path in the full cut complement has an actual
off-diagonal integral equal to a primitive endpoint difference. This
includes paths entering the inner-circle region and arbitrary winding. -/
theorem exists_angular_discComplement_integral_formula
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) :
    ∃ c : ℤ → ℂ, ∃ r R : ℤ → ℝ,
      (∀ m, 0 < r m ∧ r m < R m ∧
        sourcePeriodicSegment hp hp1 ψ m ⊆ ball (c m) (r m) ∧
        closedBall (c m) (R m) ⊆ sourceStandardRootOmittedDomain hp hp1 ψ m) ∧
      ∀ n m, m ≠ n → ∃ F : ℂ → ℂ,
        (∀ z ∈ ball (c m) (R m) \ sourcePeriodicSegment hp hp1 ψ m,
          HasDerivAt F (sourceAngularIntegrand n s
            (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) (z,ψ)) z) ∧
        ∀ {a b : ℂ} (γ : Path a b), ContDiffOn ℝ 1 γ.extend (Icc 0 1) →
          (∀ t : I, γ t ∈ ball (c m) (R m) \ sourcePeriodicSegment hp hp1 ψ m) →
          CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand n s
            (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) (z,ψ))) γ ∧
            sourceAngularPathIntegral n s (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) ψ γ = F b-F a := by
  obtain ⟨c,r,R,hgeom,hprim⟩ := hs.exists_angular_discComplement_primitives ψ hψ
  refine ⟨c,r,R,hgeom,?_⟩
  intro n m hmn
  obtain ⟨F,hF⟩ := hprim n m hmn
  refine ⟨F,hF,?_⟩
  intro a b γ hγ hγD
  exact sourceAngular_discComplement_pathIntegral_eq_sub hp hp1 n m s ψ (c m) (R m)
    (hgeom m).2.2.2 F hF γ hγ hγD

end SourcePsiSquaredGapComplexExtension
end NLS.ZakharovShabat
