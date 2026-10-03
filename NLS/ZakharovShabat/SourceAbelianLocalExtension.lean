import NLS.ZakharovShabat.SourceAbelianDiscGluing
import NLS.ZakharovShabat.SourceAbelianHalfPlaneProperties

/-! # One abelian integral on both half-planes and an isolating cut disc

The disc chart joins the two complete half-planes across the real axis
on both sides of the selected gap. This constructs one analytic function
on their union, with the actual derivative and zero endpoint limits.
-/
noncomputable section
open Set Metric Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceAbelianDiscPrimitive
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p} {φ : CoeffPair p}
  {hφ : IsRealType (CoeffPair.toMax p φ)} {n : ℤ}

/-- Domain of the two half-planes joined by this chart. -/
def extensionDomain (D : SourceAbelianDiscPrimitive hp hp1 φ hφ n) : Set ℂ :=
  (sourceAbelianHalfPlane true ∪ sourceAbelianHalfPlane false) ∪
    (ball D.center D.radius \ sourcePeriodicSegment hp hp1 φ n)

/-- The half-plane values and the local real-axis values form one function. -/
def extension (D : SourceAbelianDiscPrimitive hp hp1 φ hφ n) (z : ℂ) : ℂ :=
  if 0 < z.im then sourceAbelianHalfPlanePrimitive hp hp1 φ hφ n true z
  else if z.im < 0 then sourceAbelianHalfPlanePrimitive hp hp1 φ hφ n false z
  else D.toFun z

theorem extension_eq_halfPlane (D : SourceAbelianDiscPrimitive hp hp1 φ hφ n) (upper : Bool) :
    EqOn D.extension (sourceAbelianHalfPlanePrimitive hp hp1 φ hφ n upper)
      (sourceAbelianHalfPlane upper) := by
  intro z hz
  cases upper
  · have hz' : z.im < 0 := hz
    simp [extension,hz',not_lt.mpr hz'.le]
  · have hz' : 0 < z.im := hz
    simp [extension,hz']

theorem extension_eq_disc (D : SourceAbelianDiscPrimitive hp hp1 φ hφ n) :
    EqOn D.extension D.toFun (ball D.center D.radius \ sourcePeriodicSegment hp hp1 φ n) := by
  intro z hz
  by_cases hu : 0 < z.im
  · exact (D.extension_eq_halfPlane true hu).trans (D.eq_halfPlane true ⟨hz.1,hu⟩).symm
  by_cases hl : z.im < 0
  · exact (D.extension_eq_halfPlane false hl).trans (D.eq_halfPlane false ⟨hz.1,hl⟩).symm
  · simp [extension,hu,hl]

theorem isOpen_discComplement (D : SourceAbelianDiscPrimitive hp hp1 φ hφ n) :
    IsOpen (ball D.center D.radius \ sourcePeriodicSegment hp hp1 φ n) := by
  apply isOpen_ball.sdiff
  apply IsCompact.isClosed
  change IsCompact (segment ℝ _ _)
  rw [segment_eq_image_lineMap]
  exact isCompact_Icc.image AffineMap.lineMap_continuous

theorem isOpen_extensionDomain (D : SourceAbelianDiscPrimitive hp hp1 φ hφ n) :
    IsOpen D.extensionDomain :=
  ((isOpen_sourceAbelianHalfPlane true).union (isOpen_sourceAbelianHalfPlane false)).union
    D.isOpen_discComplement

/-- The glued function has the actual quotient derivative at every point
of its open domain, including the newly included real-axis points. -/
theorem extension_hasDerivAt (D : SourceAbelianDiscPrimitive hp hp1 φ hφ n)
    (z : ℂ) (hz : z ∈ D.extensionDomain) :
    HasDerivAt D.extension (deriv (canonicalDiscriminant hp (periodOnePotential φ)) z /
      sourceCanonicalRoot hp hp1 φ z) z := by
  rcases hz with (hu | hl) | hd
  · apply ((sourceAbelianHalfPlanePrimitive_spec hp hp1 φ hφ n true).1 z hu).congr_of_eventuallyEq
    filter_upwards [(isOpen_sourceAbelianHalfPlane true).mem_nhds hu] with w hw
    exact D.extension_eq_halfPlane true hw
  · apply ((sourceAbelianHalfPlanePrimitive_spec hp hp1 φ hφ n false).1 z hl).congr_of_eventuallyEq
    filter_upwards [(isOpen_sourceAbelianHalfPlane false).mem_nhds hl] with w hw
    exact D.extension_eq_halfPlane false hw
  · apply (D.hasDerivAt z hd).congr_of_eventuallyEq
    filter_upwards [D.isOpen_discComplement.mem_nhds hd] with w hw
    exact D.extension_eq_disc hw

/-- Spectral analyticity includes continuation from above to below the
real axis through either side of the selected gap. -/
theorem extension_analytic (D : SourceAbelianDiscPrimitive hp hp1 φ hφ n) :
    AnalyticOnNhd ℂ D.extension D.extensionDomain :=
  (show DifferentiableOn ℂ D.extension D.extensionDomain from fun z hz =>
    (D.extension_hasDerivAt z hz).differentiableAt.differentiableWithinAt).analyticOnNhd
      D.isOpen_extensionDomain

theorem ball_inter_extensionDomain (D : SourceAbelianDiscPrimitive hp hp1 φ hφ n) :
    ball D.center D.radius ∩ D.extensionDomain =
      ball D.center D.radius \ sourcePeriodicSegment hp hp1 φ n := by
  ext z
  constructor
  · rintro ⟨hb,(hu | hl) | hd⟩
    · exact ⟨hb,(sourceAbelianHalfPlane_subset_rootDomain hp hp1 φ hφ true hu) n⟩
    · exact ⟨hb,(sourceAbelianHalfPlane_subset_rootDomain hp hp1 φ hφ false hl) n⟩
    · exact hd
  · intro hz
    exact ⟨hz.1,Or.inr hz⟩

/-- No point in the continued domain lies on any spectral cut. -/
theorem extensionDomain_subset_rootDomain (D : SourceAbelianDiscPrimitive hp hp1 φ hφ n) :
    D.extensionDomain ⊆ sourceCanonicalRootDomain hp hp1 φ := by
  intro z hz
  rcases hz with (hu | hl) | hd
  · exact sourceAbelianHalfPlane_subset_rootDomain hp hp1 φ hφ true hu
  · exact sourceAbelianHalfPlane_subset_rootDomain hp hp1 φ hφ false hl
  · exact sourceAbelian_discComplement_subset_rootDomain hp hp1 φ n D.center D.radius D.avoids_other hd

/-- Every smooth path in the continued domain, including paths crossing
the real axis, integrates the actual quotient to the endpoint difference. -/
theorem extension_pathIntegral_eq_sub (D : SourceAbelianDiscPrimitive hp hp1 φ hφ n)
    {a b : ℂ} (γ : Path a b) (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (hγD : ∀ t : unitInterval, γ t ∈ D.extensionDomain) :
    CurveIntegrable (holomorphicOneForm (fun z =>
      deriv (canonicalDiscriminant hp (periodOnePotential φ)) z / sourceCanonicalRoot hp hp1 φ z)) γ ∧
    (∫ᶜ z in γ, holomorphicOneForm (fun w =>
      deriv (canonicalDiscriminant hp (periodOnePotential φ)) w / sourceCanonicalRoot hp hp1 φ w) z) =
        D.extension b-D.extension a := by
  have hω : ContinuousOn (holomorphicOneForm (fun z =>
      deriv (canonicalDiscriminant hp (periodOnePotential φ)) z / sourceCanonicalRoot hp hp1 φ z))
      D.extensionDomain := ((sourceCriticalRootRatio_analyticOnNhd hp hp1 φ).mono
        D.extensionDomain_subset_rootDomain).continuousOn.smul continuousOn_const
  have hint := hω.curveIntegrable_of_contDiffOn hγ hγD
  exact ⟨hint,curveIntegral_eq_sub_of_primitive _ D.extension D.extensionDomain D.extension_hasDerivAt
    γ hγ (fun t ht => by simpa only [Path.extend_apply γ ht] using hγD ⟨t,ht⟩) hint⟩

/-- Both zero endpoint limits survive on the entire glued domain. -/
theorem extension_endpoint_limit (D : SourceAbelianDiscPrimitive hp hp1 φ hφ n)
    (a : ℂ) (ha : a ∈ ({canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n,
      canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n} : Set ℂ)) :
    Tendsto D.extension (𝓝[D.extensionDomain] a) (𝓝 0) := by
  have haball : a ∈ ball D.center D.radius := by
    rcases (by simpa only [mem_insert_iff,mem_singleton_iff] using ha) with rfl | rfl
    · exact D.segment_subset (left_mem_segment ℝ _ _)
    · exact D.segment_subset (right_mem_segment ℝ _ _)
  have hlim : Tendsto D.toFun
      (𝓝[ball D.center D.radius \ sourcePeriodicSegment hp hp1 φ n] a) (𝓝 0) := by
    rcases (by simpa only [mem_insert_iff,mem_singleton_iff] using ha) with rfl | rfl
    · exact D.left_limit
    · exact D.right_limit
  have heq : 𝓝[ball D.center D.radius \ sourcePeriodicSegment hp hp1 φ n] a =
      𝓝[D.extensionDomain] a := by
    rw [← D.ball_inter_extensionDomain,
      nhdsWithin_inter_of_mem (nhdsWithin_le_nhds (isOpen_ball.mem_nhds haball))]
  rw [← heq]
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact (D.extension_eq_disc hz).symm

/-- The continued value is independent of the isolating chart wherever
the two extended domains overlap. -/
theorem extension_eqOn_overlap (D E : SourceAbelianDiscPrimitive hp hp1 φ hφ n) :
    EqOn D.extension E.extension (D.extensionDomain ∩ E.extensionDomain) := by
  intro z hz
  by_cases hu : z ∈ sourceAbelianHalfPlane true
  · exact (D.extension_eq_halfPlane true hu).trans (E.extension_eq_halfPlane true hu).symm
  by_cases hl : z ∈ sourceAbelianHalfPlane false
  · exact (D.extension_eq_halfPlane false hl).trans (E.extension_eq_halfPlane false hl).symm
  have hd : z ∈ ball D.center D.radius \ sourcePeriodicSegment hp hp1 φ n :=
    hz.1.resolve_left (not_or.mpr ⟨hu,hl⟩)
  have he : z ∈ ball E.center E.radius \ sourcePeriodicSegment hp hp1 φ n :=
    hz.2.resolve_left (not_or.mpr ⟨hu,hl⟩)
  exact (D.extension_eq_disc hd).trans ((D.eqOn_overlap E ⟨⟨hd.1,he.1⟩,hd.2⟩).trans
    (E.extension_eq_disc he).symm)

end NLS.ZakharovShabat.SourceAbelianDiscPrimitive
