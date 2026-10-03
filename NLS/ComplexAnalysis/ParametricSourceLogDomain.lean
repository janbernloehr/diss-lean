import NLS.ComplexAnalysis.ParametricSourceLogarithm

/-! # Open domains for straight-source logarithm continuation

The set of parameters whose entire compact source segment lies in an
open joint domain is open. This gives analyticity even on the boundary
of a chosen spectral exterior, without requiring that exterior to be
open or bounded.
-/
noncomputable section
open Set Filter Topology Complex
namespace NLS.ComplexAnalysis
variable {A : Type} [NormedAddCommGroup A] [NormedSpace ℂ A]

/-- Every point of the straight segment from the anchor source stays
inside the joint domain, with the spectral coordinate held fixed. -/
def sourceSegmentDomain (b : A) (D : Set (ℂ × A)) : Set (ℂ × A) :=
  {t | ∀ s ∈ Icc (0:ℝ) 1, sourceSegmentMap b ((s : ℂ),t) ∈ D}

theorem sourceSegmentDomain_start (b : A) (D : Set (ℂ × A))
    (t : ℂ × A) (ht : t ∈ sourceSegmentDomain b D) : (t.1,b) ∈ D := by
  simpa [sourceSegmentMap] using ht 0 (by simp)

theorem sourceSegmentDomain_end (b : A) (D : Set (ℂ × A)) : sourceSegmentDomain b D ⊆ D := by
  intro t ht
  simpa [sourceSegmentMap] using ht 1 (by simp)

@[simp] theorem mem_sourceSegmentDomain_base (b : A) (D : Set (ℂ × A)) (z : ℂ) :
    (z,b) ∈ sourceSegmentDomain b D ↔ (z,b) ∈ D := by
  constructor
  · exact sourceSegmentDomain_start b D (z,b)
  · intro hz s hs
    simpa [sourceSegmentMap] using hz

/-- Compactness of the path parameter gives an open continuation
domain even when no uniform spectral bound is available. -/
theorem isOpen_sourceSegmentDomain (b : A) (D : Set (ℂ × A)) (hD : IsOpen D) :
    IsOpen (sourceSegmentDomain b D) := by
  have hT : Continuous (sourceSegmentMap b) :=
    continuous_iff_continuousAt.mpr (fun q => (analyticAt_sourceSegmentMap b q).continuousAt)
  let K := Complex.ofReal '' Icc (0:ℝ) 1
  have hK : IsCompact K := isCompact_Icc.image continuous_ofReal
  apply isOpen_iff_mem_nhds.mpr
  intro t ht
  have hsub : K ×ˢ {t} ⊆ sourceSegmentMap b ⁻¹' D := by
    rintro ⟨s,u⟩ ⟨⟨r,hr,rfl⟩,hu⟩
    obtain rfl := mem_singleton_iff.mp hu
    exact ht r hr
  obtain ⟨U,V,_,hV,hKU,htV,hUV⟩ := generalized_tube_lemma hK isCompact_singleton (hD.preimage hT) hsub
  apply mem_of_superset (hV.mem_nhds (htV (mem_singleton t)))
  intro u hu r hr
  exact hUV ⟨hKU ⟨r,hr,rfl⟩,hu⟩

/-- Source increments are jointly analytic wherever their full
straight source path lies in the analytic nonvanishing domain. -/
theorem analyticOnNhd_parametricSourceLogIncrement_segmentDomain
    (M : ℂ × A → ℂ) (b : A) (D : Set (ℂ × A)) (hD : IsOpen D)
    (hM : AnalyticOnNhd ℂ M D) (hne : ∀ t ∈ D, M t ≠ 0) :
    AnalyticOnNhd ℂ (parametricSourceLogIncrement M b) (sourceSegmentDomain b D) := by
  have hT : Continuous (sourceSegmentMap b) :=
    continuous_iff_continuousAt.mpr (fun q => (analyticAt_sourceSegmentMap b q).continuousAt)
  apply analyticOnNhd_intervalIntegral_of_jointAnalytic (sourceLogIntegrand M b)
    (hD.preimage hT) (analyticOnNhd_sourceLogIntegrand M b D hM hne) 0 1
    (isOpen_sourceSegmentDomain b D hD)
  intro t ht s hs
  exact ht s (by simpa only [uIcc_of_le zero_le_one] using hs)

/-- Continue a prescribed logarithm on the anchor source slice. -/
def parametricSourceLogExtension (M : ℂ × A → ℂ) (b : A) (H : ℂ → ℂ) (t : ℂ × A) : ℂ :=
  H t.1+parametricSourceLogIncrement M b t

@[simp] theorem parametricSourceLogExtension_base (M : ℂ × A → ℂ) (b : A) (H : ℂ → ℂ) (z : ℂ) :
    parametricSourceLogExtension M b H (z,b) = H z := by simp [parametricSourceLogExtension]

theorem analyticOnNhd_parametricSourceLogExtension
    (M : ℂ × A → ℂ) (b : A) (H : ℂ → ℂ) (D : Set (ℂ × A)) (hD : IsOpen D)
    (hM : AnalyticOnNhd ℂ M D) (hne : ∀ t ∈ D, M t ≠ 0)
    (hH : AnalyticOnNhd ℂ H {z | (z,b) ∈ D}) :
    AnalyticOnNhd ℂ (parametricSourceLogExtension M b H) (sourceSegmentDomain b D) := by
  intro t ht
  exact ((hH t.1 (sourceSegmentDomain_start b D t ht)).comp
    (f := Prod.fst) analyticAt_fst).add
    (analyticOnNhd_parametricSourceLogIncrement_segmentDomain M b D hD hM hne t ht)

theorem exp_parametricSourceLogExtension
    (M : ℂ × A → ℂ) (b : A) (H : ℂ → ℂ) (D : Set (ℂ × A))
    (hM : AnalyticOnNhd ℂ M D) (hne : ∀ t ∈ D, M t ≠ 0)
    (hH : ∀ z, (z,b) ∈ D → exp (H z) = M (z,b))
    (t : ℂ × A) (ht : t ∈ sourceSegmentDomain b D) :
    exp (parametricSourceLogExtension M b H t) = M t := by
  rw [parametricSourceLogExtension,exp_add,hH t.1 (sourceSegmentDomain_start b D t ht),mul_comm]
  exact exp_parametricSourceLogIncrement_mul_of_segment M D b hM hne t ht

/-- The continued logarithm has the exact full logarithmic
differential throughout the open segment domain. -/
theorem hasFDerivAt_parametricSourceLogExtension
    (M : ℂ × A → ℂ) (b : A) (H : ℂ → ℂ) (D : Set (ℂ × A)) (hD : IsOpen D)
    (hM : AnalyticOnNhd ℂ M D) (hne : ∀ t ∈ D, M t ≠ 0)
    (hH : AnalyticOnNhd ℂ H {z | (z,b) ∈ D})
    (hexp : ∀ z, (z,b) ∈ D → exp (H z) = M (z,b))
    (t : ℂ × A) (ht : t ∈ sourceSegmentDomain b D) :
    HasFDerivAt (parametricSourceLogExtension M b H) ((M t)⁻¹ • fderiv ℂ M t) t := by
  have hF := (analyticOnNhd_parametricSourceLogExtension M b H D hD hM hne hH t ht).differentiableAt
  have he : (fun u => exp (parametricSourceLogExtension M b H u)) =ᶠ[𝓝 t] M := by
    filter_upwards [(isOpen_sourceSegmentDomain b D hD).mem_nhds ht] with u hu
    exact exp_parametricSourceLogExtension M b H D hM hne hexp u hu
  have hd := (hF.hasFDerivAt.cexp.congr_of_eventuallyEq he.symm).fderiv
  rw [he.eq_of_nhds] at hd
  have hmne := hne t (sourceSegmentDomain_end b D ht)
  have hcancel : (M t)⁻¹ • fderiv ℂ M t = fderiv ℂ (parametricSourceLogExtension M b H) t := by
    rw [hd,smul_smul,inv_mul_cancel₀ hmne,one_smul]
  rw [hcancel]
  exact hF.hasFDerivAt

end NLS.ComplexAnalysis
