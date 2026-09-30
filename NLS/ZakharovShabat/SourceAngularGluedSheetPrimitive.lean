import NLS.ComplexAnalysis.DensePrimitiveBoundary
import NLS.ZakharovShabat.SourceAngularCutInteriorPrimitive

/-!
# Glued normalized angular primitives on regular prescribed sheets

The canonical exterior value and the cosine continuations agree on the
dense complement of the selected gap. They glue to one analytic primitive
on the full regular prescribed-sheet part of the enclosing disc, including
cut-interior points. Every compatible continuous local continuation has
the same value there.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def sourceAngularRegularSheetDisc (hp : p ≠ ⊤) (ψ : CoeffPair p)
    (c : ℂ) (R : ℝ) (w : ℂ) : Set ℂ :=
  ball c R ∩ (fun z : ℂ => (z,ψ)) ⁻¹' sourceAngularRootSheetDomain hp w

def sourceAngularExteriorPrimitive (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    (w : ℂ) (F : ℂ → ℂ) (A : ℂ) : ℂ → ℂ :=
  rootRatioPrimitive (sourceCanonicalRoot hp hp1 ψ)
    (fun z => sourceAngularRootSheet hp w (z,ψ)) F A

theorem isOpen_sourceAngularRegularSheetDisc (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (c : ℂ) (R : ℝ) (w : ℂ) :
    IsOpen (sourceAngularRegularSheetDisc hp ψ c R w) :=
  isOpen_ball.inter ((isOpen_sourceAngularRootSheetDomain hp hp1 w).preimage (by fun_prop))

/-- A regular full-root sheet cannot contain either periodic endpoint
of any indexed pair. -/
theorem sourceAngularRootSheet_point_ne_periodic_endpoints
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (m : ℤ) (w z : ℂ)
    (hw : w ≠ 0) (hz : (z,ψ) ∈ sourceAngularRootSheetDomain hp w) :
    z ≠ canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m ∧
      z ≠ canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m := by
  have hne := pow_ne_zero 2 (sourceAngularRootSheet_ne_zero hp w hw (z,ψ) hz)
  have hs := sourceAngularRootSheet_sq hp w hw (z,ψ)
  dsimp only [sourceAngularRadicand] at hs
  rw [canonicalDiscriminant_sq_sub_four_eq_pair_mul hp hp1 _ (periodOnePotential_mem ψ) m z] at hs
  constructor <;> intro he <;> apply hne <;> rw [hs,he] <;> simp

/-- Gluing retains the zero normalized boundary value, including
approaches through the cut on the regular prescribed sheet. -/
theorem sourceAngular_glued_sheet_boundary_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (m : ℤ)
    (c : ℂ) (R : ℝ) (w : ℂ) (hw : w ≠ 0)
    (hother : closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ m)
    (F E : ℂ → ℂ) (A a : ℂ)
    (hE : ContinuousOn E (sourceAngularRegularSheetDisc hp ψ c R w))
    (hmatch : EqOn E (sourceAngularExteriorPrimitive hp hp1 ψ w F A)
      (sourceAngularRegularSheetDisc hp ψ c R w \ sourcePeriodicSegment hp hp1 ψ m))
    (hA : Tendsto F (𝓝[ball c R \ sourcePeriodicSegment hp hp1 ψ m] a) (𝓝 A)) :
    Tendsto E (𝓝[sourceAngularRegularSheetDisc hp ψ c R w] a) (𝓝 0) := by
  apply tendsto_zero_of_dense_exterior_norm F E (ball c R)
    (sourceAngularRegularSheetDisc hp ψ c R w) (sourcePeriodicSegment hp hp1 ψ m) a A
    (isOpen_sourceAngularRegularSheetDisc hp hp1 ψ c R w)
    (dense_complex_segment_complement _ _) inter_subset_left hE _ hA
  intro z hz
  have hzCan : z ∈ sourceCanonicalRootDomain hp hp1 ψ := by
    intro k
    by_cases hkm : k = m
    · subst k
      exact hz.2
    · exact (hother (ball_subset_closedBall hz.1.1)) k hkm
  have hsq := (sourceCanonicalRoot_sq_eq_discriminant_sq_sub_four hp hp1 ψ z hzCan).trans
    (sourceAngularRootSheet_sq hp w hw (z,ψ)).symm
  have hnorm : ‖sourceCanonicalRoot hp hp1 ψ z‖ = ‖sourceAngularRootSheet hp w (z,ψ)‖ := by
    rcases eq_or_eq_neg_of_sq_eq_sq _ _ hsq with h | h
    · rw [h]
    · rw [h,norm_neg]
  have hne := norm_ne_zero_iff.mpr (sourceAngularRootSheet_ne_zero hp w hw (z,ψ) hz.1.2)
  rw [hmatch hz]
  simp only [sourceAngularExteriorPrimitive,rootRatioPrimitive,norm_mul,norm_div,hnorm,
    div_self hne,one_mul]

/-- On the entire regular prescribed-sheet part of the enclosing disc,
the actual normalized exterior primitive has a unique continuous analytic
extension across the cut. Uniqueness also covers every local chart. -/
theorem exists_sourceAngular_glued_sheet_primitive
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n m : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (ψ : CoeffPair p)
    (c : ℂ) (R : ℝ)
    (hseg : sourcePeriodicSegment hp hp1 ψ m ⊆ ball c R)
    (hother : closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ m)
    (hdata : SourceAngularEndpointSpectralData hp hp1 ψ m)
    (hgap : canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m ≠
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)
    (F : ℂ → ℂ)
    (hF : ∀ z ∈ ball c R \ sourcePeriodicSegment hp hp1 ψ m,
      HasDerivAt F (sourceAngularIntegrand n s
        (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) (z,ψ)) z)
    (w : ℂ) (hw : w ≠ 0) :
    ∃ A : ℂ, ∃ E : ℂ → ℂ,
      Tendsto F (𝓝[ball c R \ sourcePeriodicSegment hp hp1 ψ m]
        (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)) (𝓝 A) ∧
      AnalyticOnNhd ℂ E (sourceAngularRegularSheetDisc hp ψ c R w) ∧
      (∀ z ∈ sourceAngularRegularSheetDisc hp ψ c R w,
        HasDerivAt E (sourceAngularIntegrand n s (sourceAngularRootSheet hp w) (z,ψ)) z) ∧
      Tendsto E (𝓝[sourceAngularRegularSheetDisc hp ψ c R w]
        (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)) (𝓝 0) ∧
      Tendsto E (𝓝[sourceAngularRegularSheetDisc hp ψ c R w]
        (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)) (𝓝 0) ∧
      EqOn E (sourceAngularExteriorPrimitive hp hp1 ψ w F A)
        (sourceAngularRegularSheetDisc hp ψ c R w \ sourcePeriodicSegment hp hp1 ψ m) ∧
      ∀ B : Set ℂ, ∀ P : ℂ → ℂ, IsOpen B → B ⊆ sourceAngularRegularSheetDisc hp ψ c R w →
        ContinuousOn P B → EqOn P (sourceAngularExteriorPrimitive hp hp1 ψ w F A)
          (B \ sourcePeriodicSegment hp hp1 ψ m) → EqOn E P B := by
  let K := sourcePeriodicSegment hp hp1 ψ m
  let Λ := (fun z : ℂ => (z,ψ)) ⁻¹' sourceAngularRootSheetDomain hp w
  let Q := sourceCanonicalRoot hp hp1 ψ
  let S : ℂ → ℂ := fun z => sourceAngularRootSheet hp w (z,ψ)
  let N : ℂ → ℂ := fun z => sourcePsiCandidate n (z,(s n ψ : Coeff p))
  have hΛ : IsOpen Λ := (isOpen_sourceAngularRootSheetDomain hp hp1 w).preimage (by fun_prop)
  have hK : IsClosed K := isClosed_sourcePeriodicSegment hp hp1 ψ m
  have hDense : Dense Kᶜ := dense_complex_segment_complement _ _
  have hcanonical (z : ℂ) (hz : z ∈ ball c R \ K) : z ∈ sourceCanonicalRootDomain hp hp1 ψ := by
    intro k
    by_cases hkm : k = m
    · subst k
      exact hz.2
    · exact (hother (ball_subset_closedBall hz.1)) k hkm
  have hQ : ContinuousOn Q (ball c R \ K) := by
    intro z hz
    exact ((sourceCanonicalRoot_analyticOnNhd hp hp1 ψ) z (hcanonical z hz)).continuousAt.continuousWithinAt
  have hS : ContinuousOn S Λ := by
    intro z hz
    exact (((analyticOnNhd_sourceAngularRootSheet hp hp1 w) (z,ψ) hz).comp
      (x := z) (f := fun u : ℂ => (u,ψ)) (analyticAt_id.prod analyticAt_const)).continuousAt.continuousWithinAt
  have hsq (z : ℂ) (hz : z ∈ (ball c R ∩ Λ) \ K) : Q z^2 = S z^2 :=
    (sourceCanonicalRoot_sq_eq_discriminant_sq_sub_four hp hp1 ψ z
      (hcanonical z ⟨hz.1.1,hz.2⟩)).trans (sourceAngularRootSheet_sq hp w hw (z,ψ)).symm
  have hne (z : ℂ) (hz : z ∈ Λ) : S z ≠ 0 := sourceAngularRootSheet_ne_zero hp w hw (z,ψ) hz
  obtain ⟨A,hA,hAr⟩ := exists_sourceAngular_primitive_common_endpoint_limit
    hp hp1 n m s ψ c R hseg hother hdata hgap F hF
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m
  let : NeBot (𝓝[ball c R \ K] l) := mem_closure_iff_nhdsWithin_neBot.mp
    (hDense.open_subset_closure_inter isOpen_ball (hseg (left_mem_segment ℝ _ _)))
  obtain ⟨E,hE,hEd,hmatch,hunique⟩ := exists_glued_normalized_root_primitive
    N Q S F (ball c R) Λ K A isOpen_ball hΛ hK hDense hQ hS hsq hne hF (by
      intro b hb hbK
      have hend := sourceAngularRootSheet_point_ne_periodic_endpoints hp hp1 ψ m w b hw hb.2
      obtain ⟨A',B,P,hA',hB,hbB,hBΩ,hBsheet,hP,hPd,hPf⟩ :=
        exists_sourceAngular_cutInterior_sheet_primitive hp hp1 n m s ψ c R hseg hother hdata
          hgap F hF b hbK hend.1 hend.2 w hw hb.2
      have hAA' : A = A' := tendsto_nhds_unique hA hA'
      subst A'
      exact ⟨B,P,hB,hbB,fun z hz => ⟨hBΩ hz,hBsheet z hz⟩,hP,hPd,
        fun z hz => hPf z hz.1 hz.2⟩)
  have hleft := sourceAngular_glued_sheet_boundary_zero hp hp1 ψ m c R w hw hother
    F E A _ hE.continuousOn hmatch hA
  have hright := sourceAngular_glued_sheet_boundary_zero hp hp1 ψ m c R w hw hother
    F E A _ hE.continuousOn hmatch hAr
  exact ⟨A,E,hA,hE,hEd,hleft,hright,hmatch,hunique⟩

namespace SourcePsiSquaredGapComplexExtension
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The actual normalized psi family supplies glued primitives on every
regular prescribed sheet of every noncollapsed off-diagonal gap, using
one all-gap enclosing-disc family at each complex source. -/
theorem exists_angular_glued_sheet_primitives
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W)
    (hdata : ∀ m, SourceAngularEndpointSpectralData hp hp1 ψ m) :
    ∃ c : ℤ → ℂ, ∃ r R : ℤ → ℝ,
      (∀ m, 0 < r m ∧ r m < R m ∧
        sourcePeriodicSegment hp hp1 ψ m ⊆ ball (c m) (r m) ∧
        closedBall (c m) (R m) ⊆ sourceStandardRootOmittedDomain hp hp1 ψ m) ∧
      ∀ n m, m ≠ n →
        canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m ≠
          canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m →
        ∀ w : ℂ, w ≠ 0 → ∃ F : ℂ → ℂ, ∃ A : ℂ, ∃ E : ℂ → ℂ,
          (∀ z ∈ ball (c m) (R m) \ sourcePeriodicSegment hp hp1 ψ m,
            HasDerivAt F (sourceAngularIntegrand n s
              (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) (z,ψ)) z) ∧
          Tendsto F (𝓝[ball (c m) (R m) \ sourcePeriodicSegment hp hp1 ψ m]
            (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)) (𝓝 A) ∧
          AnalyticOnNhd ℂ E (sourceAngularRegularSheetDisc hp ψ (c m) (R m) w) ∧
          (∀ z ∈ sourceAngularRegularSheetDisc hp ψ (c m) (R m) w,
            HasDerivAt E (sourceAngularIntegrand n s (sourceAngularRootSheet hp w) (z,ψ)) z) ∧
          Tendsto E (𝓝[sourceAngularRegularSheetDisc hp ψ (c m) (R m) w]
            (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)) (𝓝 0) ∧
          Tendsto E (𝓝[sourceAngularRegularSheetDisc hp ψ (c m) (R m) w]
            (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)) (𝓝 0) ∧
          EqOn E (sourceAngularExteriorPrimitive hp hp1 ψ w F A)
            (sourceAngularRegularSheetDisc hp ψ (c m) (R m) w \ sourcePeriodicSegment hp hp1 ψ m) ∧
          ∀ B : Set ℂ, ∀ P : ℂ → ℂ, IsOpen B → B ⊆ sourceAngularRegularSheetDisc hp ψ (c m) (R m) w →
            ContinuousOn P B → EqOn P (sourceAngularExteriorPrimitive hp hp1 ψ w F A)
              (B \ sourcePeriodicSegment hp hp1 ψ m) → EqOn E P B := by
  obtain ⟨c,r,R,hgeom,hprim⟩ := hs.exists_angular_discComplement_primitives ψ hψ
  refine ⟨c,r,R,hgeom,?_⟩
  intro n m hmn hgap w hw
  obtain ⟨F,hF⟩ := hprim n m hmn
  obtain ⟨A,E,hA,hE,hEd,hleft,hright,hmatch,hunique⟩ := exists_sourceAngular_glued_sheet_primitive
    hp hp1 n m s ψ (c m) (R m) ((hgeom m).2.2.1.trans (ball_subset_ball (hgeom m).2.1.le))
    (hgeom m).2.2.2 (hdata m) hgap F hF w hw
  exact ⟨F,A,E,hF,hA,hE,hEd,hleft,hright,hmatch,hunique⟩

end SourcePsiSquaredGapComplexExtension
end NLS.ZakharovShabat
