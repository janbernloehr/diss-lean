import NLS.ComplexAnalysis.ParametricSourceLogDomain

/-! # Joint regularity when the logarithm's source anchor moves

The straight-source logarithmic integral is analytic in the anchor,
spectral coordinate, and terminal source simultaneously, wherever the
whole source segment stays in the analytic nonvanishing domain.
-/
noncomputable section
open Set Filter Topology Complex
namespace NLS.ComplexAnalysis
variable {A : Type} [NormedAddCommGroup A] [NormedSpace ℂ A]

def movingSourceSegmentMap (q : ℂ × (A × (ℂ × A))) : ℂ × A :=
  sourceSegmentMap q.2.1 (q.1,q.2.2)

def movingSourceLogDomain (D : Set (ℂ × A)) : Set (A × (ℂ × A)) :=
  {t | t.2 ∈ sourceSegmentDomain t.1 D}

theorem analyticAt_movingSourceSegmentMap (q : ℂ × (A × (ℂ × A))) :
    AnalyticAt ℂ (movingSourceSegmentMap (A := A)) q := by
  have hb : AnalyticAt ℂ (fun q : ℂ × (A × (ℂ × A)) => q.2.1) q :=
    analyticAt_fst.comp (f := fun q : ℂ × (A × (ℂ × A)) => q.2) analyticAt_snd
  have hp : AnalyticAt ℂ (fun q : ℂ × (A × (ℂ × A)) => q.2.2) q :=
    analyticAt_snd.comp (f := fun q : ℂ × (A × (ℂ × A)) => q.2) analyticAt_snd
  have hz := analyticAt_fst.comp (f := fun q : ℂ × (A × (ℂ × A)) => q.2.2) hp
  have ha := analyticAt_snd.comp (f := fun q : ℂ × (A × (ℂ × A)) => q.2.2) hp
  exact hz.prod (hb.add (analyticAt_fst.smul (ha.sub hb)))

theorem isOpen_movingSourceLogDomain (D : Set (ℂ × A)) (hD : IsOpen D) :
    IsOpen (movingSourceLogDomain D) := by
  have hT : Continuous (movingSourceSegmentMap (A := A)) :=
    continuous_iff_continuousAt.mpr (fun q => (analyticAt_movingSourceSegmentMap q).continuousAt)
  let K := Complex.ofReal '' Icc (0:ℝ) 1
  have hK : IsCompact K := isCompact_Icc.image continuous_ofReal
  apply isOpen_iff_mem_nhds.mpr
  intro t ht
  have hsub : K ×ˢ {t} ⊆ movingSourceSegmentMap ⁻¹' D := by
    rintro ⟨s,u⟩ ⟨⟨r,hr,rfl⟩,hu⟩
    obtain rfl := mem_singleton_iff.mp hu
    exact ht r hr
  obtain ⟨U,V,_,hV,hKU,htV,hUV⟩ := generalized_tube_lemma hK isCompact_singleton (hD.preimage hT) hsub
  apply mem_of_superset (hV.mem_nhds (htV (mem_singleton t)))
  intro u hu r hr
  exact hUV (show ((r : ℂ),u) ∈ U ×ˢ V from ⟨hKU ⟨r,hr,rfl⟩,hu⟩)

/-- The logarithmic increment is jointly analytic also in its source
anchor; the terminal source and spectral point vary independently. -/
theorem analyticOnNhd_parametricSourceLogIncrement_moving_anchor
    (M : ℂ × A → ℂ) (D : Set (ℂ × A)) (hD : IsOpen D)
    (hM : AnalyticOnNhd ℂ M D) (hne : ∀ t ∈ D, M t ≠ 0) :
    AnalyticOnNhd ℂ (fun t : A × (ℂ × A) => parametricSourceLogIncrement M t.1 t.2)
      (movingSourceLogDomain D) := by
  let G : ℂ × (A × (ℂ × A)) → ℂ := fun q => sourceLogIntegrand M q.2.1 (q.1,q.2.2)
  have hT : Continuous (movingSourceSegmentMap (A := A)) :=
    continuous_iff_continuousAt.mpr (fun q => (analyticAt_movingSourceSegmentMap q).continuousAt)
  have hG : AnalyticOnNhd ℂ G (movingSourceSegmentMap ⁻¹' D) := by
    intro q hq
    have hTa := analyticAt_movingSourceSegmentMap q
    have hd := (hM.fderiv _ hq).comp (f := movingSourceSegmentMap) hTa
    have hb : AnalyticAt ℂ (fun q : ℂ × (A × (ℂ × A)) => q.2.1) q :=
      analyticAt_fst.comp (f := fun q : ℂ × (A × (ℂ × A)) => q.2) analyticAt_snd
    have hp : AnalyticAt ℂ (fun q : ℂ × (A × (ℂ × A)) => q.2.2) q :=
      analyticAt_snd.comp (f := fun q : ℂ × (A × (ℂ × A)) => q.2) analyticAt_snd
    have ha := analyticAt_snd.comp (f := fun q : ℂ × (A × (ℂ × A)) => q.2.2) hp
    have hv : AnalyticAt ℂ (fun q : ℂ × (A × (ℂ × A)) => ((0 : ℂ),q.2.2.2-q.2.1)) q :=
      analyticAt_const.prod (ha.sub hb)
    have happ := ((ContinuousLinearMap.id ℂ ((ℂ × A) →L[ℂ] ℂ)).analyticAt_bilinear
      (fderiv ℂ M (movingSourceSegmentMap q),(0,q.2.2.2-q.2.1))).comp
        (f := fun q : ℂ × (A × (ℂ × A)) => (fderiv ℂ M (movingSourceSegmentMap q),(0,q.2.2.2-q.2.1))) (hd.prod hv)
    exact happ.div ((hM _ hq).comp (f := movingSourceSegmentMap) hTa) (hne _ hq)
  apply analyticOnNhd_intervalIntegral_of_jointAnalytic G (hD.preimage hT) hG 0 1
    (isOpen_movingSourceLogDomain D hD)
  intro t ht s hs
  exact ht s (by simpa only [uIcc_of_le zero_le_one] using hs)

end NLS.ComplexAnalysis
