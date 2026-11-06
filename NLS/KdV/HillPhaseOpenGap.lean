import NLS.KdV.HillPhaseSquareEndpoints

noncomputable section
set_option autoImplicit false
open Set Complex NLS.ZakharovShabat
open scoped ComplexConjugate
namespace NLS.KdV.HillHminusPsiChart

/-- A source in the actual open eta domain has an ORIGINAL physical
open gap. Squaring cannot collapse a positive frequency gap. -/
theorem original_gap_open_of_sourceFullPhaseDomain (P : HillHminusPsiChart)
    (q : RealPeriodOneHillPotential)
    (n : ℕ+)
    (ha : hillOriginalHminusSource q.val∈P.sourceFullPhaseDomain n)
    (hreal : ∀ a∈P.miura.domain, IsRealPeriodOneHminusOne a → ∀ k : ℤ,
      P.miura.lift a (-k)=conj (P.miura.lift a k))
    (houtside : hillHminusRadicand (hillOriginalHminusSource q.val) (-P.miura.energyShift)≠0)
    (c : ℝ) (hshift : P.miura.energyShift=(c:ℂ)^2) :
    hillRealGapHalfLength q.val q.property.1 q.property.2 n≠0 := by
  let u : PeriodOneRealL2 := ⟨P.miura.lift (hillOriginalHminusSource q.val),
    hreal _ ha.1.1 (hillOriginalHminusSource_real q.val q.property.2)⟩
  have he := P.original_labels_eq_squared_miuraDirac q ha.1 hreal houtside c hshift
  have hl : hillRealLabels q.val q.property.1 q.property.2 (2*(n:ℕ)-1)=
      (hillMiuraDiracLeft u.val (n:ℕ)).re^2-c^2 := by
    simpa only [hillMiuraSquaredLabels,hillMiuraPositiveFrequencies_left _ _ n.pos] using congrFun he (2*(n:ℕ)-1)
  have hu : hillRealLabels q.val q.property.1 q.property.2 (2*(n:ℕ))=
      (hillMiuraDiracRight u.val (n:ℕ)).re^2-c^2 := by
    simpa only [hillMiuraSquaredLabels,hillMiuraPositiveFrequencies_right _ _ n.pos] using congrFun he (2*(n:ℕ))
  intro hc
  dsimp only [hillRealGapHalfLength] at hc
  rw [hl,hu] at hc
  have hp := hillMiura_positive_gap_left_pos u (n:ℕ) (by exact_mod_cast n.pos)
  change 0<(hillMiuraDiracLeft u.val (n:ℕ)).re at hp
  have horder := hillMiuraDiracDirichlet_mem_gap u (n:ℕ)
  have hRLr : (hillMiuraDiracRight u.val (n:ℕ)).re=(hillMiuraDiracLeft u.val (n:ℕ)).re := by
    nlinarith [horder.1,horder.2]
  have hpair := hillMiuraDiracPair_real u (n:ℕ)
  have hRL : hillMiuraDiracRight u.val (n:ℕ)=hillMiuraDiracLeft u.val (n:ℕ) :=
    Complex.ext hRLr (hpair.2.trans hpair.1.symm)
  apply ha.2.2
  change canonicalPeriodicRight (by simp) (by norm_num)
      (periodOnePotential (sourcePhase (hillMiuraDiagonal u.val))) (periodOnePotential_mem _) (n:ℕ)-
    canonicalPeriodicLeft (by simp) (by norm_num)
      (periodOnePotential (sourcePhase (hillMiuraDiagonal u.val))) (periodOnePotential_mem _) (n:ℕ)=0
  obtain ⟨hleft,hright⟩ := canonicalPeriodicEndpoints_sourcePhase (by simp) (by norm_num) (hillMiuraDiagonal u.val)
  rw [hleft,hright]
  change hillMiuraDiracRight u.val (n:ℕ)-hillMiuraDiracLeft u.val (n:ℕ)=0
  rw [hRL,sub_self]

end NLS.KdV.HillHminusPsiChart
