import NLS.ZakharovShabat.SourceAngularEtaRemainder
import NLS.ComplexAnalysis.PrimitiveOnDiscComplement

/-!
# Single-valued diagonal eta remainders on spectral cut complements

The actual normalized psi family supplies a zero-period diagonal
remainder on a common family of isolating discs. It has a primitive
throughout each disc minus its gap, for every complex source. Every
regular spectral path integral splits into the explicit model integral
and a primitive endpoint difference.
-/

noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem sourceAngularEtaRemainder_exists_discComplement_primitive
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (ψ : CoeffPair p)
    (c : ℂ) (r R : ℝ) (hr : 0 < r) (hrR : r < R)
    (hgap : sourcePeriodicSegment hp hp1 ψ n ⊆ ball c r)
    (hother : closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n)
    (hperiod : sourcePsiContour hp hp1 n (s n ψ : Coeff p) ψ c r = 1) :
    ∃ F : ℂ → ℂ, ∀ z ∈ ball c R \ sourcePeriodicSegment hp hp1 ψ n,
      HasDerivAt F (sourceAngularEtaRemainderIntegrand hp hp1 n s ψ z) z := by
  have hKclosed : IsClosed (sourcePeriodicSegment hp hp1 ψ n) := by
    apply IsCompact.isClosed
    change IsCompact (segment ℝ
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n))
    rw [segment_eq_image_lineMap]
    exact isCompact_Icc.image AffineMap.lineMap_continuous
  have hconv : Convex ℝ (sourcePeriodicSegment hp hp1 ψ n) := convex_segment _ _
  have hmid := sourcePeriodicMidpoint_mem_segment hp hp1 ψ n
  exact exists_primitive_on_disc_complement_of_zero_period
    (sourceAngularEtaRemainderIntegrand hp hp1 n s ψ) c
    (sourceStandardRootMidpoint hp hp1 ψ n) r R hr hrR
    (sourcePeriodicSegment hp hp1 ψ n) hKclosed hmid (hconv.starConvex hmid) hgap
    (sourceAngularEtaRemainderIntegrand_analyticOnNhd hp hp1 n s ψ c R hother)
    (circleIntegral_sourceAngularEtaRemainderIntegrand_eq_zero hp hp1 n s ψ c r hr hgap
      ((closedBall_subset_closedBall hrR.le).trans hother) hperiod)

/-- The remainder integral is a primitive endpoint difference along
any C¹ path in the entire disc minus its gap. -/
theorem sourceAngularEtaRemainder_discComplement_pathIntegral_eq_sub
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (ψ : CoeffPair p)
    (c : ℂ) (R : ℝ)
    (hother : closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n)
    (F : ℂ → ℂ) (hF : ∀ z ∈ ball c R \ sourcePeriodicSegment hp hp1 ψ n,
      HasDerivAt F (sourceAngularEtaRemainderIntegrand hp hp1 n s ψ z) z)
    {a b : ℂ} (γ : Path a b) (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (hγD : ∀ t : I, γ t ∈ ball c R \ sourcePeriodicSegment hp hp1 ψ n) :
    CurveIntegrable (holomorphicOneForm (sourceAngularEtaRemainderIntegrand hp hp1 n s ψ)) γ ∧
      (∫ᶜ z in γ, holomorphicOneForm (sourceAngularEtaRemainderIntegrand hp hp1 n s ψ) z) =
        F b-F a := by
  let D := ball c R \ sourcePeriodicSegment hp hp1 ψ n
  have hD : D ⊆ closedBall c R \ sourcePeriodicSegment hp hp1 ψ n :=
    fun _ hz => ⟨ball_subset_closedBall hz.1,hz.2⟩
  have hω : ContinuousOn
      (holomorphicOneForm (sourceAngularEtaRemainderIntegrand hp hp1 n s ψ)) D :=
    ((sourceAngularEtaRemainderIntegrand_analyticOnNhd hp hp1 n s ψ c R hother).continuousOn.mono hD).smul
      continuousOn_const
  have hint := hω.curveIntegrable_of_contDiffOn hγ hγD
  exact ⟨hint,curveIntegral_eq_sub_of_primitive _ F D hF γ hγ
    (fun t ht => by simpa only [Path.extend_apply γ ht] using hγD ⟨t,ht⟩) hint⟩

/-- All winding dependence of a regular diagonal angular integral is
carried by the explicit model; the actual remainder is single valued. -/
theorem sourceAngularEta_discComplement_pathIntegral_decomposition
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (ψ : CoeffPair p)
    (c : ℂ) (R : ℝ)
    (hother : closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n)
    (F : ℂ → ℂ) (hF : ∀ z ∈ ball c R \ sourcePeriodicSegment hp hp1 ψ n,
      HasDerivAt F (sourceAngularEtaRemainderIntegrand hp hp1 n s ψ z) z)
    {a b : ℂ} (γ : Path a b) (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (hγD : ∀ t : I, γ t ∈ ball c R \ sourcePeriodicSegment hp hp1 ψ n) :
    CurveIntegrable (holomorphicOneForm (sourceAngularEtaModelIntegrand hp hp1 n ψ)) γ ∧
      sourceAngularPathIntegral n s (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) ψ γ =
        (∫ᶜ z in γ, holomorphicOneForm (sourceAngularEtaModelIntegrand hp hp1 n ψ) z) +
          (F b-F a) := by
  let f : ℂ → ℂ := fun z => sourceAngularIntegrand n s
    (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) (z,ψ)
  let M := sourceAngularEtaModelIntegrand hp hp1 n ψ
  let D := ball c R \ sourcePeriodicSegment hp hp1 ψ n
  have hf : ContinuousOn f D := by
    apply (analyticOnNhd_sourcePsiContourIntegrand_fixed hp hp1 n (s n ψ : Coeff p) ψ).continuousOn.mono
    intro z hz m
    by_cases hmn : m = n
    · subst m; exact hz.2
    · exact (hother (ball_subset_closedBall hz.1)) m hmn
  have hM : ContinuousOn M D := by
    intro z hz
    exact (sourceAngularEtaModelIntegrand_analyticAt hp hp1 n ψ z hz.2).continuousAt.continuousWithinAt
  have hfω : ContinuousOn (holomorphicOneForm f) D := hf.smul continuousOn_const
  have hMω : ContinuousOn (holomorphicOneForm M) D := hM.smul continuousOn_const
  have hfInt := hfω.curveIntegrable_of_contDiffOn hγ hγD
  have hMInt := hMω.curveIntegrable_of_contDiffOn hγ hγD
  obtain ⟨_,hrem⟩ := sourceAngularEtaRemainder_discComplement_pathIntegral_eq_sub
    hp hp1 n s ψ c R hother F hF γ hγ hγD
  have hω : holomorphicOneForm (sourceAngularEtaRemainderIntegrand hp hp1 n s ψ) =
      fun z => holomorphicOneForm f z-holomorphicOneForm M z := by
    funext z
    exact sub_smul (f z) (M z) (ContinuousLinearMap.id ℂ ℂ)
  rw [hω,curveIntegral_fun_sub hfInt hMInt] at hrem
  refine ⟨hMInt,?_⟩
  change (∫ᶜ z in γ, holomorphicOneForm f z) =
    (∫ᶜ z in γ, holomorphicOneForm M z) + (F b-F a)
  exact sub_eq_iff_eq_add.mp hrem |>.trans (add_comm _ _)

namespace SourcePsiSquaredGapComplexExtension
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- Every actual complex source has one all-gap family of discs on
which the diagonal remainders have single-valued primitives. The
normalization is derived from Lemma 12.12, including collapsed gaps. -/
theorem exists_eta_remainder_discComplement_primitives
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) :
    ∃ c : ℤ → ℂ, ∃ r R : ℤ → ℝ,
      (∀ n, 0 < r n ∧ r n < R n ∧
        sourcePeriodicSegment hp hp1 ψ n ⊆ ball (c n) (r n) ∧
        closedBall (c n) (R n) ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n) ∧
      ∀ n, ∃ F : ℂ → ℂ, ∀ z ∈ ball (c n) (R n) \ sourcePeriodicSegment hp hp1 ψ n,
        HasDerivAt F (sourceAngularEtaRemainderIntegrand hp hp1 n s ψ z) z := by
  obtain ⟨c,R,hfamily,horth⟩ := hs.contour_orthogonality ψ hψ
  have hinner : ∀ n : ℤ, ∃ r : ℝ, 0 < r ∧ r < R n ∧
      sourcePeriodicSegment hp hp1 ψ n ⊆ ball (c n) r := by
    intro n
    obtain ⟨r,ρ,hr,hrρ,hρR,hseg⟩ := exists_nested_radii_of_segment_subset_ball
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)
      (c n) (R n) (hfamily.2 n).2.1
    exact ⟨r,hr,hrρ.trans hρR,hseg⟩
  choose r hr hrR hseg using hinner
  refine ⟨c,r,R,fun n => ⟨hr n,hrR n,hseg n,(hfamily.2 n).2.2.1⟩,?_⟩
  intro n
  apply sourceAngularEtaRemainder_exists_discComplement_primitive hp hp1 n s ψ (c n)
    (r n) (R n) (hr n) (hrR n) (hseg n) (hfamily.2 n).2.2.1
  rw [sourcePsiContour_eq_of_nested_enclosingCircles hp hp1 n n (s n ψ : Coeff p) ψ
    (c n) (c n) (r n) (R n) (hr n) (hfamily.2 n).1 (hseg n) (hfamily.2 n).2.1
    (closedBall_subset_closedBall (hrR n).le) (hfamily.2 n).2.2.1]
  simpa only [eq_self_iff_true,ite_true] using horth n n

/-- The literal regular diagonal integrals split into the model
integral and a single-valued remainder on the same all-gap family. -/
theorem exists_eta_discComplement_integral_decomposition
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) :
    ∃ c : ℤ → ℂ, ∃ r R : ℤ → ℝ,
      (∀ n, 0 < r n ∧ r n < R n ∧
        sourcePeriodicSegment hp hp1 ψ n ⊆ ball (c n) (r n) ∧
        closedBall (c n) (R n) ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n) ∧
      ∀ n, ∃ F : ℂ → ℂ,
        (∀ z ∈ ball (c n) (R n) \ sourcePeriodicSegment hp hp1 ψ n,
          HasDerivAt F (sourceAngularEtaRemainderIntegrand hp hp1 n s ψ z) z) ∧
        ∀ {a b : ℂ} (γ : Path a b), ContDiffOn ℝ 1 γ.extend (Icc 0 1) →
          (∀ t : I, γ t ∈ ball (c n) (R n) \ sourcePeriodicSegment hp hp1 ψ n) →
          CurveIntegrable (holomorphicOneForm (sourceAngularEtaModelIntegrand hp hp1 n ψ)) γ ∧
            sourceAngularPathIntegral n s (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) ψ γ =
              (∫ᶜ z in γ, holomorphicOneForm (sourceAngularEtaModelIntegrand hp hp1 n ψ) z) +
                (F b-F a) := by
  obtain ⟨c,r,R,hgeom,hprim⟩ := hs.exists_eta_remainder_discComplement_primitives ψ hψ
  refine ⟨c,r,R,hgeom,?_⟩
  intro n
  obtain ⟨F,hF⟩ := hprim n
  refine ⟨F,hF,?_⟩
  intro a b γ hγ hγD
  exact sourceAngularEta_discComplement_pathIntegral_decomposition hp hp1 n s ψ (c n) (R n)
    (hgeom n).2.2.2 F hF γ hγ hγD

end SourcePsiSquaredGapComplexExtension
end NLS.ZakharovShabat
