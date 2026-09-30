import NLS.ZakharovShabat.SourceAngularEtaPrescribedSheet
import NLS.ComplexAnalysis.GapRootPrimitiveGluing

/-!
# Glued diagonal eta remainders on prescribed root sheets

The normalized exterior remainder primitive continues analytically
through every interior cut point and glues onto the whole regular
prescribed-sheet part of the isolating disc. Both endpoint limits
remain zero, and its exterior value has the exact full-root sheet ratio.
-/

noncomputable section
open Set Filter Topology Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem exists_sourceAngularEta_glued_remainder_sheet_primitive
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (ψ : CoeffPair p)
    (c : ℂ) (R : ℝ)
    (hseg : sourcePeriodicSegment hp hp1 ψ n ⊆ ball c R)
    (hother : closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n)
    (hdata : SourceAngularEndpointSpectralData hp hp1 ψ n)
    (hgap : canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)
    (F : ℂ → ℂ)
    (hF : ∀ z ∈ ball c R \ sourcePeriodicSegment hp hp1 ψ n,
      HasDerivAt F (sourceAngularEtaRemainderIntegrand hp hp1 n s ψ z) z)
    (hleft : Tendsto F (𝓝[ball c R \ sourcePeriodicSegment hp hp1 ψ n]
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)) (𝓝 0))
    (hright : Tendsto F (𝓝[ball c R \ sourcePeriodicSegment hp hp1 ψ n]
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)) (𝓝 0))
    (w : ℂ) (hw : w ≠ 0) :
    ∃ E : ℂ → ℂ, AnalyticOnNhd ℂ E (sourceAngularRegularSheetDisc hp ψ c R w) ∧
      (∀ z ∈ sourceAngularRegularSheetDisc hp ψ c R w,
        HasDerivAt E (sourceAngularEtaRemainderSheetIntegrand hp hp1 n s ψ w z) z) ∧
      Tendsto E (𝓝[sourceAngularRegularSheetDisc hp ψ c R w]
        (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)) (𝓝 0) ∧
      Tendsto E (𝓝[sourceAngularRegularSheetDisc hp ψ c R w]
        (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)) (𝓝 0) ∧
      EqOn E (sourceAngularExteriorPrimitive hp hp1 ψ w F 0)
        (sourceAngularRegularSheetDisc hp ψ c R w \ sourcePeriodicSegment hp hp1 ψ n) ∧
      ∀ B : Set ℂ, ∀ P : ℂ → ℂ, IsOpen B → B ⊆ sourceAngularRegularSheetDisc hp ψ c R w →
        ContinuousOn P B → EqOn P (sourceAngularExteriorPrimitive hp hp1 ψ w F 0)
          (B \ sourcePeriodicSegment hp hp1 ψ n) → EqOn E P B := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  let τ := (l+r)/2
  let δ := (r-l)/2
  let Λ := sourceAngularRegularSheetDisc hp ψ c R w
  let g : ℂ → ℂ := fun z => sourceAngularGapNumerator hp hp1 n n s ψ z-I
  let Q := sourceStandardRoot hp hp1 ψ n
  let S := sourceAngularEtaSelectedSheetRoot hp hp1 n ψ w
  have hl : τ-δ = l := by dsimp [τ,δ]; ring
  have hr : τ+δ = r := by dsimp [τ,δ]; ring
  have hδ : δ ≠ 0 := div_ne_zero (sub_ne_zero.mpr hgap.symm) (by norm_num)
  have hΛ : IsOpen Λ := isOpen_sourceAngularRegularSheetDisc hp hp1 ψ c R w
  have hΛball : Λ ⊆ ball c R := inter_subset_left
  have hinter : ball c R ∩ Λ = Λ := inter_eq_right.mpr hΛball
  have hg : AnalyticOnNhd ℂ g (ball c R) :=
    ((sourceAngularGapNumerator_analyticOnNhd hp hp1 n n s ψ hdata.analytic_omitted).sub
      analyticOnNhd_const).mono (fun z hz => hother (ball_subset_closedBall hz))
  have hQ : ContinuousOn Q (ball c R \ segment ℝ (τ-δ) (τ+δ)) := by
    rw [hl,hr]
    intro z hz
    exact (sourceStandardRoot_analyticAt hp hp1 ψ n z hz.2).continuousAt.continuousWithinAt
  have hQsq : ∀ z ∈ ball c R \ segment ℝ (τ-δ) (τ+δ), Q z^2 = (τ-δ-z)*(τ+δ-z) := by
    rw [hl,hr]
    intro z hz
    exact sourceStandardRoot_sq_of_not_mem_segment hp hp1 ψ n z hz.2
  have hFd : ∀ z ∈ ball c R \ segment ℝ (τ-δ) (τ+δ), HasDerivAt F (g z/Q z) z := by
    rw [hl,hr]
    intro z hz
    rw [← sourceAngularEtaRemainderIntegrand_eq_gapNumerator]
    exact hF z hz
  have hS : AnalyticOnNhd ℂ S Λ :=
    sourceAngularEtaSelectedSheetRoot_analyticOnNhd hp hp1 n ψ w c R hother hdata
  have hSne : ∀ z ∈ Λ, S z ≠ 0 := fun z hz =>
    sourceAngularEtaSelectedSheetRoot_ne_zero hp hp1 n ψ w z hw hz.2
      (hother (ball_subset_closedBall hz.1))
  have hSsq : ∀ z ∈ Λ, S z^2 = (τ-δ-z)*(τ+δ-z) := by
    rw [hl,hr]
    intro z hz
    exact sourceAngularEtaSelectedSheetRoot_sq hp hp1 n ψ w z hw (hother (ball_subset_closedBall hz.1))
  obtain ⟨E,hEa,hEd,hmatch,hunique⟩ := exists_glued_gap_regular_sheet_primitive
    g Q F S (ball c R) Λ τ δ 0 isOpen_ball hΛ hδ (by rw [hl,hr]; exact hseg)
    hg hQ hQsq hFd (by rw [hl,hr]; exact hleft) hS hSne hSsq
  rw [hinter] at hEa hEd hmatch hunique
  rw [hl,hr] at hmatch hunique
  have hratio (z : ℂ) : rootRatioPrimitive Q S F 0 z =
      sourceAngularExteriorPrimitive hp hp1 ψ w F 0 z := by
    simp only [sourceAngularExteriorPrimitive,rootRatioPrimitive]
    rw [sourceCanonicalRoot_eq_omitted hp hp1 n ψ z]
    dsimp only [Q,S,sourceAngularEtaSelectedSheetRoot]
    rw [div_div_eq_mul_div]
    ring
  have hmatchFull : EqOn E (sourceAngularExteriorPrimitive hp hp1 ψ w F 0)
      (Λ \ sourcePeriodicSegment hp hp1 ψ n) :=
    fun z hz => (hmatch hz).trans (hratio z)
  have hEl := sourceAngular_glued_sheet_boundary_zero hp hp1 ψ n c R w hw hother
    F E 0 l hEa.continuousOn hmatchFull hleft
  have hEr := sourceAngular_glued_sheet_boundary_zero hp hp1 ψ n c R w hw hother
    F E 0 r hEa.continuousOn hmatchFull hright
  refine ⟨E,hEa,?_,hEl,hEr,hmatchFull,?_⟩
  · intro z hz
    rw [sourceAngularEtaRemainderSheetIntegrand_eq_gapNumerator hp hp1 n s ψ w z
      (hother (ball_subset_closedBall hz.1))]
    exact hEd z hz
  · intro B P hB hBΛ hP hPf
    apply hunique B P hB hBΛ hP
    intro z hz
    exact (hPf hz).trans (hratio z).symm

namespace SourcePsiSquaredGapComplexExtension
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- At every actual complex source, each open-gap remainder extends
onto every regular prescribed root sheet, with both endpoint values zero. -/
theorem exists_eta_remainder_glued_sheet_primitives
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W)
    (hdata : ∀ n, SourceAngularEndpointSpectralData hp hp1 ψ n) :
    ∃ c : ℤ → ℂ, ∃ r R : ℤ → ℝ,
      (∀ n, 0 < r n ∧ r n < R n ∧
        sourcePeriodicSegment hp hp1 ψ n ⊆ ball (c n) (r n) ∧
        closedBall (c n) (R n) ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n) ∧
      ∀ n, canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠
          canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n →
        ∃ F : ℂ → ℂ,
          (∀ z ∈ ball (c n) (R n) \ sourcePeriodicSegment hp hp1 ψ n,
            HasDerivAt F (sourceAngularEtaRemainderIntegrand hp hp1 n s ψ z) z) ∧
          ∀ w : ℂ, w ≠ 0 → ∃ E : ℂ → ℂ,
            AnalyticOnNhd ℂ E (sourceAngularRegularSheetDisc hp ψ (c n) (R n) w) ∧
            (∀ z ∈ sourceAngularRegularSheetDisc hp ψ (c n) (R n) w,
              HasDerivAt E (sourceAngularEtaRemainderSheetIntegrand hp hp1 n s ψ w z) z) ∧
            Tendsto E (𝓝[sourceAngularRegularSheetDisc hp ψ (c n) (R n) w]
              (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)) (𝓝 0) ∧
            Tendsto E (𝓝[sourceAngularRegularSheetDisc hp ψ (c n) (R n) w]
              (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)) (𝓝 0) ∧
            EqOn E (sourceAngularExteriorPrimitive hp hp1 ψ w F 0)
              (sourceAngularRegularSheetDisc hp ψ (c n) (R n) w \ sourcePeriodicSegment hp hp1 ψ n) := by
  obtain ⟨c,r,R,hgeom,hprim⟩ := hs.exists_eta_remainder_normalized_endpoint_primitives ψ hψ hdata
  refine ⟨c,r,R,hgeom,?_⟩
  intro n hgap
  obtain ⟨F,hF,hleft,hright⟩ := hprim n hgap
  refine ⟨F,hF,?_⟩
  intro w hw
  obtain ⟨E,hEa,hEd,hEl,hEr,hmatch,_⟩ := exists_sourceAngularEta_glued_remainder_sheet_primitive
    hp hp1 n s ψ (c n) (R n) ((hgeom n).2.2.1.trans (ball_subset_ball (hgeom n).2.1.le))
    (hgeom n).2.2.2 (hdata n) hgap F hF hleft hright w hw
  exact ⟨E,hEa,hEd,hEl,hEr,hmatch⟩

end SourcePsiSquaredGapComplexExtension
end NLS.ZakharovShabat
