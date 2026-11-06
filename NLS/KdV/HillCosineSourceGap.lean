import NLS.KdV.HillHminusOriginalCosineLift

noncomputable section
set_option autoImplicit false
open Set Complex NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ComplexConjugate
namespace NLS.KdV.HillHminusPsiChart
variable (P : HillHminusPsiChart) (q : RealPeriodOneHillPotential)
  (hq : hillOriginalHminusSource q.val∈P.source)
  (hreal : ∀ a∈P.miura.domain, IsRealPeriodOneHminusOne a → ∀ k : ℤ,
    P.miura.lift a (-k)=conj (P.miura.lift a k))
  (houtside : hillHminusRadicand (hillOriginalHminusSource q.val) (-P.miura.energyShift)≠0)
  (c : ℝ) (hshift : P.miura.energyShift=(c:ℂ)^2)

 theorem originalCosineFrequencyPath_real (k : ℕ+)
    (hgap : hillRealGapHalfLength q.val q.property.1 q.property.2 k≠0) (t : ℝ) :
    ((P.originalCosineFrequencyPath q hq hreal houtside c hshift k hgap).extend t).im=0 := by
  change ((Real.sqrt _:ℝ):ℂ).im=0
  exact ofReal_im _

 theorem originalCosineFrequencyPath_re_pos (k : ℕ+)
    (hgap : hillRealGapHalfLength q.val q.property.1 q.property.2 k≠0) (t : ℝ) :
    0<((P.originalCosineFrequencyPath q hq hreal houtside c hshift k hgap).extend t).re := by
  exact Real.sqrt_pos.mpr (hillPhysicalCosineEnergyPath_shift_pos q.val q.property.1 q.property.2
    k k.pos _ _ (c^2) (P.original_gap_left_shift_pos q hq hreal houtside c hshift k) t)

/-- The CONSTRUCTED original positive frequency path lies in its exact
canonically labelled ordinary-source gap, including both endpoints. -/
theorem originalCosineFrequencyPath_mem_sourceGap (k : ℕ+)
    (hgap : hillRealGapHalfLength q.val q.property.1 q.property.2 k≠0) (t : ℝ) :
    (P.originalCosineFrequencyPath q hq hreal houtside c hshift k hgap).extend t∈
      sourcePeriodicSegment (by simp) (by norm_num)
        (P.dirichletSource (hillOriginalHminusSource q.val)) (k:ℕ) := by
  let u : PeriodOneRealL2 := ⟨P.miura.lift (hillOriginalHminusSource q.val),
    hreal _ hq.1 (hillOriginalHminusSource_real q.val q.property.2)⟩
  let z := (P.originalCosineFrequencyPath q hq hreal houtside c hshift k hgap).extend t
  let E := (hillPhysicalCosineEnergyPath q.val q.property.1 q.property.2 k
    (realCosineArcAnchor (hillDirichletSelectedRealAngle q.val q.property.1 q.property.2 k k.pos hgap))
    (hillDirichletSelectedRealAngle q.val q.property.1 q.property.2 k k.pos hgap)).extend t
  have hzreal := P.originalCosineFrequencyPath_real q hq hreal houtside c hshift k hgap t
  have hzpos := P.originalCosineFrequencyPath_re_pos q hq hreal houtside c hshift k hgap t
  have he := P.original_labels_eq_squared_miuraDirac q hq hreal houtside c hshift
  have hl : hillRealLabels q.val q.property.1 q.property.2 (2*(k:ℕ)-1)=
      (hillMiuraDiracLeft u.val (k:ℕ)).re^2-c^2 := by
    simpa only [hillMiuraSquaredLabels,hillMiuraPositiveFrequencies_left _ _ k.pos] using congrFun he (2*(k:ℕ)-1)
  have hu : hillRealLabels q.val q.property.1 q.property.2 (2*(k:ℕ))=
      (hillMiuraDiracRight u.val (k:ℕ)).re^2-c^2 := by
    simpa only [hillMiuraSquaredLabels,hillMiuraPositiveFrequencies_right _ _ k.pos] using congrFun he (2*(k:ℕ))
  have hbounds : E.re∈Icc (hillRealLabels q.val q.property.1 q.property.2 (2*(k:ℕ)-1))
      (hillRealLabels q.val q.property.1 q.property.2 (2*(k:ℕ))) :=
    re_mem_Icc_of_mem_real_segment _ _ (monotone_hillRealLabels _ _ _ (by omega)) _
      (hillPhysicalCosineEnergyPath_mem_gap q.val q.property.1 q.property.2 k k.pos _ _ t)
  rw [hl,hu] at hbounds
  have hsq : z.re^2-c^2=E.re := by
    have h := congrArg Complex.re (P.originalCosineFrequencyPath_squared q hq hreal houtside c hshift k hgap t)
    simpa only [hshift,← ofReal_pow,sub_re,ofReal_re,pow_two,mul_re,hzreal,ofReal_im,mul_zero,sub_zero] using h
  have hleft := hillMiura_positive_gap_left_pos u (k:ℕ) (by exact_mod_cast k.pos)
  change 0<(hillMiuraDiracLeft u.val (k:ℕ)).re at hleft
  have horder := hillMiuraDiracDirichlet_mem_gap u (k:ℕ)
  have hlr : (hillMiuraDiracLeft u.val (k:ℕ)).re≤(hillMiuraDiracRight u.val (k:ℕ)).re :=
    horder.1.trans horder.2
  have hfreq : z.re∈Icc (hillMiuraDiracLeft u.val (k:ℕ)).re
      (hillMiuraDiracRight u.val (k:ℕ)).re := by
    constructor <;> nlinarith [hbounds.1,hbounds.2]
  have hmem := ofReal_mem_ordered_segment _ _ z.re hlr hfreq
  have hpair := hillMiuraDiracPair_real u (k:ℕ)
  have hzl : ((hillMiuraDiracLeft u.val (k:ℕ)).re:ℂ)=hillMiuraDiracLeft u.val (k:ℕ) :=
    Complex.ext rfl hpair.1.symm
  have hzu : ((hillMiuraDiracRight u.val (k:ℕ)).re:ℂ)=hillMiuraDiracRight u.val (k:ℕ) :=
    Complex.ext rfl hpair.2.symm
  have hzz : (z.re:ℂ)=z := Complex.ext rfl hzreal.symm
  rw [hzl,hzu,hzz] at hmem
  change z∈sourcePeriodicSegment (by simp) (by norm_num) (sourcePhase (hillMiuraDiagonal u.val)) (k:ℕ)
  rw [sourcePeriodicSegment_sourcePhase]
  exact hmem

/-- Its actual negative path lies in the oppositely labelled gap;
the periodic endpoint slots reverse under this reflection. -/
theorem originalCosineFrequencyPath_neg_mem_sourceGap (k : ℕ+)
    (hgap : hillRealGapHalfLength q.val q.property.1 q.property.2 k≠0) (t : ℝ) :
    -(P.originalCosineFrequencyPath q hq hreal houtside c hshift k hgap).extend t∈
      sourcePeriodicSegment (by simp) (by norm_num)
        (P.dirichletSource (hillOriginalHminusSource q.val)) (-((k:ℕ):ℤ)) := by
  have h := P.originalCosineFrequencyPath_mem_sourceGap q hq hreal houtside c hshift k hgap t
  have href := P.sourcePhase_periodic_endpoint_reflection (hillOriginalHminusSource q.val) (k:ℕ)
  unfold sourcePeriodicSegment at h ⊢
  rw [href.1,href.2,segment_symm]
  rcases h with ⟨a,b,ha,hb,hab,he⟩
  exact ⟨a,b,ha,hb,hab,by rw [smul_neg,smul_neg,← neg_add,he]⟩

end NLS.KdV.HillHminusPsiChart
