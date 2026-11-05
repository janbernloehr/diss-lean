import NLS.KdV.HillPhysicalCosineFrequencyPath
import NLS.KdV.HillHminusDirichletSignedReflection

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
include P hq hreal houtside hshift

/-- The ACTUAL original gap lies strictly above the quadratic origin
of its actual Miura chart, at EVERY positive index. -/
theorem original_gap_left_shift_pos (k : ℕ+) :
    0<hillRealLabels q.val q.property.1 q.property.2 (2*(k:ℕ)-1)+c^2 := by
  let u : PeriodOneRealL2 := ⟨P.miura.lift (hillOriginalHminusSource q.val),
    hreal _ hq.1 (hillOriginalHminusSource_real q.val q.property.2)⟩
  have he := congrFun (P.original_labels_eq_squared_miuraDirac q hq hreal houtside c hshift) (2*(k:ℕ)-1)
  have hl : hillRealLabels q.val q.property.1 q.property.2 (2*(k:ℕ)-1)=
      (hillMiuraDiracLeft u.val (k:ℕ)).re^2-c^2 := by
    simpa only [hillMiuraSquaredLabels,hillMiuraPositiveFrequencies_left _ _ k.pos] using he
  have hp := hillMiura_positive_gap_left_pos u (k:ℕ) (by exact_mod_cast k.pos)
  change 0<(hillMiuraDiracLeft u.val (k:ℕ)).re at hp
  rw [hl]
  nlinarith [sq_pos_of_pos hp]

theorem original_cosine_lift_left (k : ℕ+) (θ : ℝ) :
    positiveRealEnergyLift (c^2)
      (cosineGapPoint (hillRealGapCenter q.val q.property.1 q.property.2 k)
        (hillRealGapHalfLength q.val q.property.1 q.property.2 k) (realCosineArcAnchor θ:ℂ))=
      canonicalPeriodicLeft (by simp) (by norm_num)
        (periodOnePotential (P.dirichletSource (hillOriginalHminusSource q.val)))
          (periodOnePotential_mem _) (k:ℕ) := by
  let u : PeriodOneRealL2 := ⟨P.miura.lift (hillOriginalHminusSource q.val),
    hreal _ hq.1 (hillOriginalHminusSource_real q.val q.property.2)⟩
  have he := congrFun (P.original_labels_eq_squared_miuraDirac q hq hreal houtside c hshift) (2*(k:ℕ)-1)
  have hl : hillRealLabels q.val q.property.1 q.property.2 (2*(k:ℕ)-1)=
      (hillMiuraDiracLeft u.val (k:ℕ)).re^2-c^2 := by
    simpa only [hillMiuraSquaredLabels,hillMiuraPositiveFrequencies_left _ _ k.pos] using he
  have hpoint : cosineGapPoint (hillRealGapCenter q.val q.property.1 q.property.2 k)
      (hillRealGapHalfLength q.val q.property.1 q.property.2 k) (realCosineArcAnchor θ:ℂ)=
      (hillRealLabels q.val q.property.1 q.property.2 (2*(k:ℕ)-1):ℂ) := by
    have hg := (hillRealGapContour_geometry q.val q.property.1 q.property.2 k k.pos).2.2.1
    unfold realCosineArcAnchor
    split <;> simp only [cosineGapPoint,ofReal_neg,Complex.cos_neg,Complex.cos_pi,mul_neg_one]
      <;> exact (ofReal_sub _ _).symm.trans (congrArg (fun x : ℝ => (x:ℂ)) hg)
  rw [hpoint]
  have him := (hillMiuraDiracPair_real u (k:ℕ)).1
  have hp := hillMiura_positive_gap_left_pos u (k:ℕ) (by exact_mod_cast k.pos)
  change 0<(hillMiuraDiracLeft u.val (k:ℕ)).re at hp
  have hz : ((hillMiuraDiracLeft u.val (k:ℕ)).re:ℂ)=hillMiuraDiracLeft u.val (k:ℕ) :=
    Complex.ext rfl him.symm
  have hsq : (hillRealLabels q.val q.property.1 q.property.2 (2*(k:ℕ)-1):ℂ)=
      (hillMiuraDiracLeft u.val (k:ℕ))^2-((c^2:ℝ):ℂ) := by
    rw [hl,ofReal_sub,ofReal_pow,hz]
  rw [positiveRealEnergyLift_eq_of_sq (c^2) _ _ him hp.le hsq]
  change hillMiuraDiracLeft u.val (k:ℕ)=
    canonicalPeriodicLeft (by simp) (by norm_num)
      (periodOnePotential (sourcePhase (hillMiuraDiagonal u.val))) (periodOnePotential_mem _) (k:ℕ)
  rw [(canonicalPeriodicEndpoints_sourcePhase (by simp) (by norm_num) (hillMiuraDiagonal u.val)).1]
  rfl

theorem original_cosine_lift_terminal (k : ℕ+)
    (hgap : hillRealGapHalfLength q.val q.property.1 q.property.2 k≠0) :
    positiveRealEnergyLift (c^2)
      (cosineGapPoint (hillRealGapCenter q.val q.property.1 q.property.2 k)
        (hillRealGapHalfLength q.val q.property.1 q.property.2 k)
        (hillDirichletSelectedRealAngle q.val q.property.1 q.property.2 k k.pos hgap:ℂ))=
      canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet
        (P.dirichletSource (hillOriginalHminusSource q.val)) (k:ℕ) := by
  let u : PeriodOneRealL2 := ⟨P.miura.lift (hillOriginalHminusSource q.val),
    hreal _ hq.1 (hillOriginalHminusSource_real q.val q.property.2)⟩
  rw [(hillDirichletSelectedRealAngle_spec q.val q.property.1 q.property.2 k k.pos hgap).2.1]
  have him := hillMiuraDiracDirichlet_im_eq_zero u (k:ℕ)
  have hmem := hillMiuraDiracDirichlet_mem_gap u (k:ℕ)
  have hp := hillMiura_positive_gap_left_pos u (k:ℕ) (by exact_mod_cast k.pos)
  change 0<(hillMiuraDiracLeft u.val (k:ℕ)).re at hp
  have hpos : 0≤(hillMiuraDiracDirichlet u.val (k:ℕ)).re := (hp.trans_le hmem.1).le
  have he : (hillDirichletEnergy q.val q.property.1 q.property.2 k k.pos:ℂ)=
      (hillMiuraDiracDirichlet u.val (k:ℕ))^2-((c^2:ℝ):ℂ) := by
    rw [← P.dirichletEnergy_eq_original q hq hreal houtside c hshift k]
    change _^2-P.miura.energyShift=_
    rw [hshift,ofReal_pow]
  rw [positiveRealEnergyLift_eq_of_sq (c^2) _ _ him hpos he]
  exact P.dirichletFrequency_eq_sourcePhase (k:ℕ) (hillOriginalHminusSource q.val)

/-- The constructed positive lift has the ACTUAL canonically labelled
ordinary-source left and Dirichlet endpoints, with no high cutoff. -/
def originalCosineFrequencyPath (k : ℕ+)
    (hgap : hillRealGapHalfLength q.val q.property.1 q.property.2 k≠0) :
    Path (canonicalPeriodicLeft (by simp) (by norm_num)
      (periodOnePotential (P.dirichletSource (hillOriginalHminusSource q.val)))
        (periodOnePotential_mem _) (k:ℕ))
      (canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet
        (P.dirichletSource (hillOriginalHminusSource q.val)) (k:ℕ)) :=
  (hillPhysicalCosineFrequencyPath q.val q.property.1 q.property.2 k
    (realCosineArcAnchor (hillDirichletSelectedRealAngle q.val q.property.1 q.property.2 k k.pos hgap))
    (hillDirichletSelectedRealAngle q.val q.property.1 q.property.2 k k.pos hgap) (c^2)).cast
      (P.original_cosine_lift_left q hq hreal houtside c hshift k _).symm
      (P.original_cosine_lift_terminal q hq hreal houtside c hshift k hgap).symm

theorem contDiffOn_originalCosineFrequencyPath (k : ℕ+)
    (hgap : hillRealGapHalfLength q.val q.property.1 q.property.2 k≠0) :
    ContDiffOn ℝ 1 (P.originalCosineFrequencyPath q hq hreal houtside c hshift k hgap).extend
      (Icc 0 1) :=
  contDiffOn_hillPhysicalCosineFrequencyPath q.val q.property.1 q.property.2 k k.pos _ _ (c^2)
    (P.original_gap_left_shift_pos q hq hreal houtside c hshift k)

/-- At the actual chart shift, the canonically endpoint-labelled source
path squares to the ORIGINAL signed physical cosine energy path. -/
theorem originalCosineFrequencyPath_squared (k : ℕ+)
    (hgap : hillRealGapHalfLength q.val q.property.1 q.property.2 k≠0) (t : ℝ) :
    ((P.originalCosineFrequencyPath q hq hreal houtside c hshift k hgap).extend t)^2-
      P.miura.energyShift=
      (hillPhysicalCosineEnergyPath q.val q.property.1 q.property.2 k
        (realCosineArcAnchor (hillDirichletSelectedRealAngle q.val q.property.1 q.property.2 k k.pos hgap))
        (hillDirichletSelectedRealAngle q.val q.property.1 q.property.2 k k.pos hgap)).extend t := by
  change ((hillPhysicalCosineFrequencyPath q.val q.property.1 q.property.2 k _ _ (c^2)).extend t)^2-
    P.miura.energyShift=_
  rw [hshift,← ofReal_pow]
  exact hillPhysicalCosineFrequencyPath_squared q.val q.property.1 q.property.2 k k.pos _ _ (c^2)
    (P.original_gap_left_shift_pos q hq hreal houtside c hshift k) t

end NLS.KdV.HillHminusPsiChart
