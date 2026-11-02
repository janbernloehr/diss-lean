import NLS.ZakharovShabat.SourceBoundaryExplicitHeight
import NLS.ZakharovShabat.SourceBoundaryCounting
import NLS.ZakharovShabat.HeightRectangleContour
import NLS.ZakharovShabat.SourceAuxiliaryExplicitHeight
import NLS.ZakharovShabat.SourceAuxiliaryExteriorContours

/-! # Corrected-height contours in the original boundary and auxiliary spaces

The actual four-edge integrals at the corrected height equal the original
central integrals. The full ambient integrals and both boundary restrictions retain analytic
dependence and the original algebraic ranks on one common source neighborhood.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
open BoundaryCondition
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A global strip sharpens the original box-and-disk exterior to the corrected height. -/
theorem sourceHeightExterior_subset_resolvent (hp : p ≠ ⊤) (φ : CoeffPair p) (N : ℕ)
    (H r : ℝ) (hext : spectralExterior N r ⊆ sourceResolventSet hp φ)
    (hh : ∀ z : ℂ, H ≤ |z.im| → z ∈ sourceResolventSet hp φ) :
    (heightSpectralBox N H ∪ highSpectralDisks N r)ᶜ ⊆ sourceResolventSet hp φ := by
  intro z hz
  by_cases hi : H ≤ |z.im|
  · exact hh z hi
  · apply hext
    change z ∉ centralSpectralBox N ∪ highSpectralDisks N r
    rintro (hc | hd)
    · exact hz (Or.inl ⟨hc.1, (lt_of_not_ge hi).le⟩)
    · exact hz (Or.inr hd)

/-- The actual original-norm integral around the rectangle of height `H`. -/
def sourceHeightRectangleIntegral (hp : p ≠ ⊤) (φ : CoeffPair p) (N : ℕ) (H : ℝ) :
    CoeffPair p →L[ℂ] CoeffPair p :=
  sourceResolventRectangleIntegral hp φ (heightLowerCorner N H) (heightUpperCorner N H)

/-- A sufficient resolvent strip makes the original moving contour admissible. -/
theorem sourceHeightCorner_boundary_subset_resolvent (hp : p ≠ ⊤) (φ : CoeffPair p) (N : ℕ)
    {H : ℝ} (hH : 0 ≤ H) (hHN : H ≤ (N : ℝ))
    (hc : centralRectangleBoundary N ⊆ sourceResolventSet hp φ)
    (hh : ∀ z : ℂ, H ≤ |z.im| → z ∈ sourceResolventSet hp φ) :
    RectangleIntegral.boundary (heightLowerCorner N H) (heightUpperCorner N H) ⊆
      sourceResolventSet hp φ := by
  simp only [sourceResolventSet_eq] at hc hh ⊢
  exact heightCorner_boundary_subset_resolvent hp _ N hH hHN hc hh

/-- Moving the horizontal edges within the exterior strip preserves the actual integral. -/
theorem sourceHeightRectangleIntegral_eq_central (hp : p ≠ ⊤) (φ : CoeffPair p) (N : ℕ)
    {H : ℝ} (hH : 0 ≤ H) (hHN : H ≤ (N : ℝ))
    (hc : centralRectangleBoundary N ⊆ sourceResolventSet hp φ)
    (hh : ∀ z : ℂ, H ≤ |z.im| → z ∈ sourceResolventSet hp φ) :
    sourceHeightRectangleIntegral hp φ N H = sourceCentralRectangleIntegral hp φ N := by
  have hc' : centralRectangleBoundary N ⊆ resolventSet hp (CoeffPair.toMax p φ) := by
    simpa only [sourceResolventSet_eq] using hc
  have hh' : ∀ z : ℂ, H ≤ |z.im| → z ∈ resolventSet hp (CoeffPair.toMax p φ) := by
    simpa only [sourceResolventSet_eq] using hh
  rw [sourceHeightRectangleIntegral, sourceResolventRectangleIntegral_eq_conj hp φ _ _
      (sourceHeightCorner_boundary_subset_resolvent hp φ N hH hHN hc hh),
    sourceCentralRectangleIntegral_eq_conj hp φ N hc,
    centralRectangleIntegral_eq_centralSpectralProjection hp _ N hc']
  exact congrArg (CoeffPair.toMax p).symm.conjContinuousAlgEquiv
    (heightRectangleIntegral_eq_centralSpectralProjection hp _ N hH hHN hc' hh')

/-- Compression of the actual corrected-height integral to an original boundary space. -/
def sourceBoundaryHeightProjection (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (N : ℕ) (H : ℝ) :
    sourceBoundaryBaseSubspace (p := p) b →L[ℂ] sourceBoundaryBaseSubspace (p := p) b :=
  sourceBoundaryCompression b (sourceHeightRectangleIntegral hp φ N H)

/-- The sufficient strip also identifies both boundary restrictions with their central ones. -/
theorem sourceBoundaryHeightProjection_eq_central (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (N : ℕ) {H : ℝ} (hH : 0 ≤ H) (hHN : H ≤ (N : ℝ))
    (hc : centralRectangleBoundary N ⊆ sourceResolventSet hp φ)
    (hh : ∀ z : ℂ, H ≤ |z.im| → z ∈ sourceResolventSet hp φ) :
    sourceBoundaryHeightProjection b hp φ N H = sourceBoundaryCentralProjection b hp φ N := by
  unfold sourceBoundaryHeightProjection sourceBoundaryCentralProjection
  rw [sourceHeightRectangleIntegral_eq_central hp φ N hH hHN hc hh]

/-- On the boundary space the compressed moving integral is its actual restriction. -/
theorem sourceBoundaryHeightProjection_apply (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .dirichlet) (N : ℕ)
    {H : ℝ} (hH : 0 ≤ H) (hHN : H ≤ (N : ℝ))
    (hc : centralRectangleBoundary N ⊆ sourceResolventSet hp φ)
    (hh : ∀ z : ℂ, H ≤ |z.im| → z ∈ sourceResolventSet hp φ)
    (x : sourceBoundaryBaseSubspace (p := p) b) :
    (sourceBoundaryHeightProjection b hp φ N H x).val = sourceHeightRectangleIntegral hp φ N H x.val := by
  rw [sourceBoundaryHeightProjection_eq_central b hp φ N hH hHN hc hh,
    sourceHeightRectangleIntegral_eq_central hp φ N hH hHN hc hh]
  exact sourceBoundaryCentralProjection_apply b hp φ hφ N hc x

/-- Both boundary conditions retain analytic corrected-height projections and rank `2N+1`
on one original-input neighborhood, simultaneously for every larger cutoff. -/
theorem exists_uniform_sourceBoundary_corrected_height_contours (hp1 : 1 < p) (hp : p ≠ ⊤)
    (φ : CoeffPair p) :
    ∃ N₀ : ℕ, ∃ U : Set (CoeffPair p),
      0 < N₀ ∧ IsOpen U ∧ Convex ℝ U ∧ IsConnected U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ N : ℕ, N₀ ≤ N →
        AnalyticOnNhd ℂ
          (fun ψ => sourceHeightRectangleIntegral hp (sourceReflectedPotential hp1 hp ψ) N
            (sourceBoundaryExplicitHeight hp hp1 ‖ψ‖)) U ∧
        (∀ b : BoundaryCondition, AnalyticOnNhd ℂ
          (fun ψ => sourceBoundaryHeightProjection b hp (sourceReflectedPotential hp1 hp ψ) N
            (sourceBoundaryExplicitHeight hp hp1 ‖ψ‖)) U) ∧
        (∀ n : ℤ, N < n.natAbs →
          AnalyticOnNhd ℂ
            (fun ψ => sourceResolventCircleIntegral hp (sourceReflectedPotential hp1 hp ψ)
              ((Real.pi : ℂ) * n) (Real.pi / 4)) U ∧
          ∀ b : BoundaryCondition, AnalyticOnNhd ℂ
          (fun ψ => sourceBoundaryCircleProjection b hp (sourceReflectedPotential hp1 hp ψ)
            ((Real.pi : ℂ) * n) (Real.pi / 4)) U) ∧
        ∀ ψ ∈ U,
          SourceBoundaryCountingData hp (sourceReflectedPotential hp1 hp ψ)
            (sourceReflectedPotential_mem hp1 hp ψ) N ∧
          RectangleIntegral.boundary
            (heightLowerCorner N (sourceBoundaryExplicitHeight hp hp1 ‖ψ‖))
            (heightUpperCorner N (sourceBoundaryExplicitHeight hp hp1 ‖ψ‖)) ⊆
              sourceResolventSet hp (sourceReflectedPotential hp1 hp ψ) ∧
          AnalyticOnNhd ℂ (sourceResolvent hp (sourceReflectedPotential hp1 hp ψ))
            (heightSpectralBox N (sourceBoundaryExplicitHeight hp hp1 ‖ψ‖) ∪
              highSpectralDisks N (Real.pi / 4))ᶜ ∧
          sourceHeightRectangleIntegral hp (sourceReflectedPotential hp1 hp ψ) N
            (sourceBoundaryExplicitHeight hp hp1 ‖ψ‖) =
            sourceCentralRectangleIntegral hp (sourceReflectedPotential hp1 hp ψ) N ∧
          ∀ b : BoundaryCondition,
            sourceBoundaryHeightProjection b hp (sourceReflectedPotential hp1 hp ψ) N
              (sourceBoundaryExplicitHeight hp hp1 ‖ψ‖) =
              sourceBoundaryCentralProjection b hp (sourceReflectedPotential hp1 hp ψ) N ∧
            Module.finrank ℂ (sourceBoundaryHeightProjection b hp (sourceReflectedPotential hp1 hp ψ) N
              (sourceBoundaryExplicitHeight hp hp1 ‖ψ‖)).range = 2 * N + 1 ∧
            Module.finrank ℂ ((sourceBoundaryHeightProjection b hp (sourceReflectedPotential hp1 hp ψ) N
              (sourceBoundaryExplicitHeight hp hp1 ‖ψ‖)).comp (sourceBoundaryInclusion b)).range = 2 * N + 1 ∧
            IsIdempotentElem (sourceBoundaryHeightProjection b hp (sourceReflectedPotential hp1 hp ψ) N
              (sourceBoundaryExplicitHeight hp hp1 ‖ψ‖)) ∧
            FiniteDimensional ℂ (sourceBoundaryHeightProjection b hp (sourceReflectedPotential hp1 hp ψ) N
              (sourceBoundaryExplicitHeight hp hp1 ‖ψ‖)).range := by
  let F := sourceReflectedPotentialCLM hp1 hp
  have hF (ψ : CoeffPair p) : F ψ = sourceReflectedPotential hp1 hp ψ :=
    sourceReflectedPotentialCLM_apply hp1 hp ψ
  obtain ⟨K₀, V₀, hK₀, ho₀, hc₀, _, hφ₀, h0₀, hdata₀⟩ := exists_uniform_sourceBoundaryCountingData hp1 hp φ
  obtain ⟨J, W, _, hWo, hWc, hφW, h0W, hanW, _⟩ :=
    exists_uniform_sourceCentralRectangleIntegral hp (F φ)
  let K := max K₀ J
  let V := V₀ ∩ (F ⁻¹' W)
  have hK : 0 < K := hK₀.trans_le (le_max_left _ _)
  have ho : IsOpen V := ho₀.inter (hWo.preimage F.continuous)
  have hc : Convex ℝ V := hc₀.inter (hWc.linear_preimage (F.restrictScalars ℝ).toLinearMap)
  have hφ : φ ∈ V := ⟨hφ₀, hφW⟩
  have h0 : (0 : CoeffPair p) ∈ V := ⟨h0₀, by simpa only [mem_preimage, map_zero] using h0W⟩
  have hdata (N : ℕ) (hN : K ≤ N) := hdata₀ N ((le_max_left K₀ J).trans hN)
  obtain ⟨L, hL⟩ := exists_nat_ge (sourceBoundaryExplicitHeight hp hp1 (‖φ‖ + 1))
  let U := V ∩ ball (0 : CoeffPair p) (‖φ‖ + 1)
  have hUo : IsOpen U := ho.inter isOpen_ball
  have hUc : Convex ℝ U := hc.inter (convex_ball 0 _)
  have hU0 : (0 : CoeffPair p) ∈ U := ⟨h0, by simp [mem_ball]; positivity⟩
  have hheight (ψ : CoeffPair p) (hψ : ψ ∈ U) (N : ℕ) (hN : max K L ≤ N) :
      sourceBoundaryExplicitHeight hp hp1 ‖ψ‖ ≤ (N : ℝ) := by
    apply (sourceBoundaryExplicitHeight_mono hp hp1 (norm_nonneg ψ)
      (mem_ball_zero_iff.mp hψ.2).le).trans
    exact hL.trans (by exact_mod_cast ((le_max_right K L).trans hN))
  have hstrip (ψ : CoeffPair p) (z : ℂ) (hz : sourceBoundaryExplicitHeight hp hp1 ‖ψ‖ ≤ |z.im|) :
      z ∈ sourceResolventSet hp (sourceReflectedPotential hp1 hp ψ) := by
    rw [sourceResolventSet_eq, toMax_sourceReflectedPotential]
    exact mem_resolventSet_of_sourceBoundaryExplicitHeight hp hp1 ψ le_rfl hz
  have he (ψ : CoeffPair p) (hψ : ψ ∈ U) (N : ℕ) (hN : max K L ≤ N) (b : BoundaryCondition) :
      sourceBoundaryHeightProjection b hp (sourceReflectedPotential hp1 hp ψ) N
        (sourceBoundaryExplicitHeight hp hp1 ‖ψ‖) =
        sourceBoundaryCentralProjection b hp (sourceReflectedPotential hp1 hp ψ) N :=
    sourceBoundaryHeightProjection_eq_central b hp _ N
      (sourceBoundaryExplicitHeight_pos hp hp1 (norm_nonneg ψ)).le (hheight ψ hψ N hN)
      ((hdata N ((le_max_left _ _).trans hN)).2.2 ψ hψ.1.1).central_boundary (hstrip ψ)
  have heAmbient (ψ : CoeffPair p) (hψ : ψ ∈ U) (N : ℕ) (hN : max K L ≤ N) :
      sourceHeightRectangleIntegral hp (sourceReflectedPotential hp1 hp ψ) N
        (sourceBoundaryExplicitHeight hp hp1 ‖ψ‖) =
        sourceCentralRectangleIntegral hp (sourceReflectedPotential hp1 hp ψ) N :=
    sourceHeightRectangleIntegral_eq_central hp _ N
      (sourceBoundaryExplicitHeight_pos hp hp1 (norm_nonneg ψ)).le (hheight ψ hψ N hN)
      ((hdata N ((le_max_left _ _).trans hN)).2.2 ψ hψ.1.1).central_boundary (hstrip ψ)
  refine ⟨max K L, U, hK.trans_le (le_max_left _ _), hUo, hUc,
    ⟨⟨0, hU0⟩, hUc.isPreconnected⟩, ⟨hφ, by simp [mem_ball]⟩, hU0, ?_⟩
  intro N hN
  have hKN := (le_max_left K L).trans hN
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ψ hψ
    have hf := (hanW N ((le_max_right K₀ J).trans hKN) (F ψ) hψ.1.2).comp (F.analyticAt ψ)
    have hf' : AnalyticAt ℂ
        (fun a => sourceCentralRectangleIntegral hp (sourceReflectedPotential hp1 hp a) N) ψ := by
      simpa only [Function.comp_def, hF] using hf
    apply hf'.congr
    filter_upwards [hUo.mem_nhds hψ] with a ha
    exact (heAmbient a ha N hN).symm
  · intro b ψ hψ
    apply ((hdata N hKN).1 b ψ hψ.1.1).congr
    filter_upwards [hUo.mem_nhds hψ] with a ha
    exact (he a ha N hN b).symm
  · intro n hn
    refine ⟨?_, ?_⟩
    · intro ψ hψ
      have hb : sphere ((Real.pi : ℂ) * n) (Real.pi / 4) ⊆ sourceResolventSet hp (F ψ) := by
        simpa only [hF] using ((hdata N hKN).2.2 ψ hψ.1.1).disk_resolvent n hn
      have ha := (analyticAt_sourceResolventCircleIntegral hp (F ψ) _ _ (by positivity) hb).comp
        (F.analyticAt ψ)
      simpa only [Function.comp_def, hF] using ha
    · intro b
      exact ((hdata N hKN).2.1 n hn b).mono (fun _ h => h.1.1)
  · intro ψ hψ
    have hd := (hdata N hKN).2.2 ψ hψ.1.1
    refine ⟨hd, sourceHeightCorner_boundary_subset_resolvent hp _ N
      (sourceBoundaryExplicitHeight_pos hp hp1 (norm_nonneg ψ)).le (hheight ψ hψ N hN)
      hd.central_boundary (hstrip ψ), ?_, heAmbient ψ hψ N hN, ?_⟩
    · apply (analyticOnNhd_sourceResolvent hp _).mono
      apply sourceHeightExterior_subset_resolvent hp _ N _ _ _ (hstrip ψ)
      rw [sourceResolventSet_eq]
      exact hd.coefficient_counts.periodic.exterior_resolvent
    intro b
    refine ⟨he ψ hψ N hN b, ?_⟩
    rw [he ψ hψ N hN b]
    exact ⟨hd.central_rank b, hd.central_domain_rank b, hd.central_properties b⟩

/-- The auxiliary phase preserves the sufficient original-norm exterior strip. -/
theorem mem_sourceResolventSet_of_auxiliaryExplicitHeight (hp1 : 1 < p) (hp : p ≠ ⊤)
    (φ : CoeffPair p) {M : ℝ} (hφ : ‖φ‖ ≤ M) {z : ℂ}
    (hz : sourceBoundaryExplicitHeight hp hp1 M ≤ |z.im|) :
    z ∈ sourceResolventSet hp (sourceAuxiliaryReflectedPotential hp1 hp φ) := by
  rw [sourceResolventSet_eq, toMax_sourceAuxiliaryReflectedPotential,
    mem_resolventSet_auxiliaryPotential_iff]
  change z ∈ resolventSet hp (auxiliaryPotential
    (BoundaryCondition.intervalExtensionCLM .neumann hp1 hp (CoeffPair.toMax p φ)))
  rw [auxiliaryPotential_intervalExtension_neumann hp hp1 (CoeffPair.toMax p φ)]
  exact mem_resolventSet_of_sourceBoundaryExplicitHeight hp hp1 (sourceAuxiliaryPotentialPhase hp φ)
    (by simpa only [LinearIsometryEquiv.norm_map] using hφ) hz

/-- Compression of the actual corrected-height integral to an original auxiliary space. -/
def sourceAuxiliaryHeightProjection (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (N : ℕ) (H : ℝ) :
    auxiliarySourceSpace (p := p) b →L[ℂ] auxiliarySourceSpace (p := p) b :=
  sourceAuxiliaryCompression b (sourceHeightRectangleIntegral hp φ N H)

/-- The sufficient strip also identifies both auxiliary restrictions with their central ones. -/
theorem sourceAuxiliaryHeightProjection_eq_central (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (N : ℕ) {H : ℝ} (hH : 0 ≤ H) (hHN : H ≤ (N : ℝ))
    (hc : centralRectangleBoundary N ⊆ sourceResolventSet hp φ)
    (hh : ∀ z : ℂ, H ≤ |z.im| → z ∈ sourceResolventSet hp φ) :
    sourceAuxiliaryHeightProjection b hp φ N H = sourceAuxiliaryCentralProjection b hp φ N := by
  unfold sourceAuxiliaryHeightProjection sourceAuxiliaryCentralProjection
  rw [sourceHeightRectangleIntegral_eq_central hp φ N hH hHN hc hh]

/-- On the auxiliary space the compressed moving integral is its actual restriction. -/
theorem sourceAuxiliaryHeightProjection_apply (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .neumann) (N : ℕ)
    {H : ℝ} (hH : 0 ≤ H) (hHN : H ≤ (N : ℝ))
    (hc : centralRectangleBoundary N ⊆ sourceResolventSet hp φ)
    (hh : ∀ z : ℂ, H ≤ |z.im| → z ∈ sourceResolventSet hp φ)
    (x : auxiliarySourceSpace (p := p) b) :
    (sourceAuxiliaryHeightProjection b hp φ N H x).val = sourceHeightRectangleIntegral hp φ N H x.val := by
  rw [sourceAuxiliaryHeightProjection_eq_central b hp φ N hH hHN hc hh,
    sourceHeightRectangleIntegral_eq_central hp φ N hH hHN hc hh]
  exact sourceAuxiliaryCentralProjection_apply b hp φ hφ N hc x

/-- Both auxiliary conditions retain analytic corrected-height projections and rank `2N+1`
on one original-input neighborhood, simultaneously for every larger cutoff. -/
theorem exists_uniform_sourceAuxiliary_corrected_height_contours (hp1 : 1 < p) (hp : p ≠ ⊤)
    (φ : CoeffPair p) :
    ∃ N₀ : ℕ, ∃ U : Set (CoeffPair p),
      0 < N₀ ∧ IsOpen U ∧ Convex ℝ U ∧ IsConnected U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ N : ℕ, N₀ ≤ N →
        AnalyticOnNhd ℂ
          (fun ψ => sourceHeightRectangleIntegral hp (sourceAuxiliaryReflectedPotential hp1 hp ψ) N
            (sourceBoundaryExplicitHeight hp hp1 ‖ψ‖)) U ∧
        (∀ b : BoundaryCondition, AnalyticOnNhd ℂ
          (fun ψ => sourceAuxiliaryHeightProjection b hp (sourceAuxiliaryReflectedPotential hp1 hp ψ) N
            (sourceBoundaryExplicitHeight hp hp1 ‖ψ‖)) U) ∧
        (∀ n : ℤ, N < n.natAbs →
          AnalyticOnNhd ℂ
            (fun ψ => sourceResolventCircleIntegral hp (sourceAuxiliaryReflectedPotential hp1 hp ψ)
              ((Real.pi : ℂ) * n) (Real.pi / 4)) U ∧
          ∀ b : BoundaryCondition, AnalyticOnNhd ℂ
          (fun ψ => sourceAuxiliaryCircleProjection b hp (sourceAuxiliaryReflectedPotential hp1 hp ψ)
            ((Real.pi : ℂ) * n) (Real.pi / 4)) U) ∧
        ∀ ψ ∈ U,
          SourceAuxiliaryExteriorContourData hp (sourceAuxiliaryReflectedPotential hp1 hp ψ)
            (sourceAuxiliaryReflectedPotential_mem hp1 hp ψ) N ∧
          RectangleIntegral.boundary
            (heightLowerCorner N (sourceBoundaryExplicitHeight hp hp1 ‖ψ‖))
            (heightUpperCorner N (sourceBoundaryExplicitHeight hp hp1 ‖ψ‖)) ⊆
              sourceResolventSet hp (sourceAuxiliaryReflectedPotential hp1 hp ψ) ∧
          AnalyticOnNhd ℂ (sourceResolvent hp (sourceAuxiliaryReflectedPotential hp1 hp ψ))
            (heightSpectralBox N (sourceBoundaryExplicitHeight hp hp1 ‖ψ‖) ∪
              highSpectralDisks N (Real.pi / 4))ᶜ ∧
          sourceHeightRectangleIntegral hp (sourceAuxiliaryReflectedPotential hp1 hp ψ) N
            (sourceBoundaryExplicitHeight hp hp1 ‖ψ‖) =
            sourceCentralRectangleIntegral hp (sourceAuxiliaryReflectedPotential hp1 hp ψ) N ∧
          ∀ b : BoundaryCondition,
            sourceAuxiliaryHeightProjection b hp (sourceAuxiliaryReflectedPotential hp1 hp ψ) N
              (sourceBoundaryExplicitHeight hp hp1 ‖ψ‖) =
              sourceAuxiliaryCentralProjection b hp (sourceAuxiliaryReflectedPotential hp1 hp ψ) N ∧
            Module.finrank ℂ (sourceAuxiliaryHeightProjection b hp (sourceAuxiliaryReflectedPotential hp1 hp ψ) N
              (sourceBoundaryExplicitHeight hp hp1 ‖ψ‖)).range = 2 * N + 1 ∧
            Module.finrank ℂ ((sourceAuxiliaryHeightProjection b hp (sourceAuxiliaryReflectedPotential hp1 hp ψ) N
              (sourceBoundaryExplicitHeight hp hp1 ‖ψ‖)).comp (sourceAuxiliaryInclusion b)).range = 2 * N + 1 ∧
            IsIdempotentElem (sourceAuxiliaryHeightProjection b hp (sourceAuxiliaryReflectedPotential hp1 hp ψ) N
              (sourceBoundaryExplicitHeight hp hp1 ‖ψ‖)) ∧
            FiniteDimensional ℂ (sourceAuxiliaryHeightProjection b hp (sourceAuxiliaryReflectedPotential hp1 hp ψ) N
              (sourceBoundaryExplicitHeight hp hp1 ‖ψ‖)).range := by
  let F := sourceAuxiliaryReflectedPotentialCLM hp1 hp
  have hF (ψ : CoeffPair p) : F ψ = sourceAuxiliaryReflectedPotential hp1 hp ψ :=
    sourceAuxiliaryReflectedPotentialCLM_apply hp1 hp ψ
  obtain ⟨K₀, V₀, hK₀, ho₀, hc₀, _, hφ₀, h0₀, hdata₀⟩ := exists_uniform_sourceAuxiliaryExteriorContourData hp1 hp φ
  obtain ⟨J, W, _, hWo, hWc, hφW, h0W, hanW, _⟩ :=
    exists_uniform_sourceCentralRectangleIntegral hp (F φ)
  let K := max K₀ J
  let V := V₀ ∩ (F ⁻¹' W)
  have hK : 0 < K := hK₀.trans_le (le_max_left _ _)
  have ho : IsOpen V := ho₀.inter (hWo.preimage F.continuous)
  have hc : Convex ℝ V := hc₀.inter (hWc.linear_preimage (F.restrictScalars ℝ).toLinearMap)
  have hφ : φ ∈ V := ⟨hφ₀, hφW⟩
  have h0 : (0 : CoeffPair p) ∈ V := ⟨h0₀, by simpa only [mem_preimage, map_zero] using h0W⟩
  have hdata (N : ℕ) (hN : K ≤ N) := hdata₀ N ((le_max_left K₀ J).trans hN)
  obtain ⟨L, hL⟩ := exists_nat_ge (sourceBoundaryExplicitHeight hp hp1 (‖φ‖ + 1))
  let U := V ∩ ball (0 : CoeffPair p) (‖φ‖ + 1)
  have hUo : IsOpen U := ho.inter isOpen_ball
  have hUc : Convex ℝ U := hc.inter (convex_ball 0 _)
  have hU0 : (0 : CoeffPair p) ∈ U := ⟨h0, by simp [mem_ball]; positivity⟩
  have hheight (ψ : CoeffPair p) (hψ : ψ ∈ U) (N : ℕ) (hN : max K L ≤ N) :
      sourceBoundaryExplicitHeight hp hp1 ‖ψ‖ ≤ (N : ℝ) := by
    apply (sourceBoundaryExplicitHeight_mono hp hp1 (norm_nonneg ψ)
      (mem_ball_zero_iff.mp hψ.2).le).trans
    exact hL.trans (by exact_mod_cast ((le_max_right K L).trans hN))
  have hstrip (ψ : CoeffPair p) (z : ℂ) (hz : sourceBoundaryExplicitHeight hp hp1 ‖ψ‖ ≤ |z.im|) :
      z ∈ sourceResolventSet hp (sourceAuxiliaryReflectedPotential hp1 hp ψ) := by
    exact mem_sourceResolventSet_of_auxiliaryExplicitHeight hp1 hp ψ le_rfl hz
  have he (ψ : CoeffPair p) (hψ : ψ ∈ U) (N : ℕ) (hN : max K L ≤ N) (b : BoundaryCondition) :
      sourceAuxiliaryHeightProjection b hp (sourceAuxiliaryReflectedPotential hp1 hp ψ) N
        (sourceBoundaryExplicitHeight hp hp1 ‖ψ‖) =
        sourceAuxiliaryCentralProjection b hp (sourceAuxiliaryReflectedPotential hp1 hp ψ) N :=
    sourceAuxiliaryHeightProjection_eq_central b hp _ N
      (sourceBoundaryExplicitHeight_pos hp hp1 (norm_nonneg ψ)).le (hheight ψ hψ N hN)
      ((hdata N ((le_max_left _ _).trans hN)).2.2 ψ hψ.1.1).toSourceAuxiliaryContourData.central_boundary (hstrip ψ)
  have heAmbient (ψ : CoeffPair p) (hψ : ψ ∈ U) (N : ℕ) (hN : max K L ≤ N) :
      sourceHeightRectangleIntegral hp (sourceAuxiliaryReflectedPotential hp1 hp ψ) N
        (sourceBoundaryExplicitHeight hp hp1 ‖ψ‖) =
        sourceCentralRectangleIntegral hp (sourceAuxiliaryReflectedPotential hp1 hp ψ) N :=
    sourceHeightRectangleIntegral_eq_central hp _ N
      (sourceBoundaryExplicitHeight_pos hp hp1 (norm_nonneg ψ)).le (hheight ψ hψ N hN)
      ((hdata N ((le_max_left _ _).trans hN)).2.2 ψ hψ.1.1).toSourceAuxiliaryContourData.central_boundary (hstrip ψ)
  refine ⟨max K L, U, hK.trans_le (le_max_left _ _), hUo, hUc,
    ⟨⟨0, hU0⟩, hUc.isPreconnected⟩, ⟨hφ, by simp [mem_ball]⟩, hU0, ?_⟩
  intro N hN
  have hKN := (le_max_left K L).trans hN
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ψ hψ
    have hf := (hanW N ((le_max_right K₀ J).trans hKN) (F ψ) hψ.1.2).comp (F.analyticAt ψ)
    have hf' : AnalyticAt ℂ
        (fun a => sourceCentralRectangleIntegral hp (sourceAuxiliaryReflectedPotential hp1 hp a) N) ψ := by
      simpa only [Function.comp_def, hF] using hf
    apply hf'.congr
    filter_upwards [hUo.mem_nhds hψ] with a ha
    exact (heAmbient a ha N hN).symm
  · intro b ψ hψ
    apply ((hdata N hKN).1 b ψ hψ.1.1).congr
    filter_upwards [hUo.mem_nhds hψ] with a ha
    exact (he a ha N hN b).symm
  · intro n hn
    refine ⟨?_, ?_⟩
    · intro ψ hψ
      have hb : sphere ((Real.pi : ℂ) * n) (Real.pi / 4) ⊆ sourceResolventSet hp (F ψ) := by
        simpa only [hF] using ((hdata N hKN).2.2 ψ hψ.1.1).toSourceAuxiliaryContourData.disk_resolvent n hn
      have ha := (analyticAt_sourceResolventCircleIntegral hp (F ψ) _ _ (by positivity) hb).comp
        (F.analyticAt ψ)
      simpa only [Function.comp_def, hF] using ha
    · intro b
      exact ((hdata N hKN).2.1 n hn b).mono (fun _ h => h.1.1)
  · intro ψ hψ
    have hd := (hdata N hKN).2.2 ψ hψ.1.1
    refine ⟨hd, sourceHeightCorner_boundary_subset_resolvent hp _ N
      (sourceBoundaryExplicitHeight_pos hp hp1 (norm_nonneg ψ)).le (hheight ψ hψ N hN)
      hd.toSourceAuxiliaryContourData.central_boundary (hstrip ψ), ?_, heAmbient ψ hψ N hN, ?_⟩
    · apply (analyticOnNhd_sourceResolvent hp _).mono
      apply sourceHeightExterior_subset_resolvent hp _ N _ _ _ (hstrip ψ)
      exact hd.exterior_resolvent
    intro b
    refine ⟨he ψ hψ N hN b, ?_⟩
    rw [he ψ hψ N hN b]
    exact ⟨hd.toSourceAuxiliaryContourData.central_rank b, hd.toSourceAuxiliaryContourData.central_domain_rank b, hd.toSourceAuxiliaryContourData.central_properties b⟩

end NLS.ZakharovShabat
