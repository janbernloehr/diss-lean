import NLS.KdV.HillFullPhaseSquare
import NLS.KdV.HillHminusNativeSourceFactors
import NLS.ZakharovShabat.SourceGapWeightedEtaSquare

/-! # Exact frequency-to-energy normalization at every original gap -/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.ZakharovShabat
open scoped ComplexConjugate
namespace NLS.KdV.HillHminusPsiChart
variable (P : HillHminusPsiChart) (q : RealPeriodOneHillPotential)
  (hq : hillOriginalHminusSource q.val∈P.source)
  (hreal : ∀ a∈P.miura.domain, IsRealPeriodOneHminusOne a → ∀ k : ℤ,
    P.miura.lift a (-k)=conj (P.miura.lift a k))
  (houtside : hillHminusRadicand (hillOriginalHminusSource q.val) (-P.miura.energyShift)≠0)
  (c : ℝ) (hshift : P.miura.energyShift=(c : ℂ)^2)
include hq hreal houtside hshift

/-- Full frequency gap times frequency midpoint equals HALF the original
energy gap. This includes the first gap, repeated endpoints and means. -/
theorem source_midpoint_mul_gap_eq_original_halfLength (n : ℕ+) :
    canonicalPeriodicMidpoint (by norm_num) (by norm_num)
      (periodOnePotential (P.dirichletSource (hillOriginalHminusSource q.val)))
      (periodOnePotential_mem _) (n : ℕ)*
    canonicalPeriodicGap (by norm_num) (by norm_num)
      (periodOnePotential (P.dirichletSource (hillOriginalHminusSource q.val)))
      (periodOnePotential_mem _) (n : ℕ)=
      (hillRealGapHalfLength q.val q.property.1 q.property.2 n : ℂ) := by
  let u : PeriodOneRealL2 := ⟨P.miura.lift (hillOriginalHminusSource q.val),
    hreal _ hq.1 (hillOriginalHminusSource_real q.val q.property.2)⟩
  have he := P.original_labels_eq_squared_miuraDirac q hq hreal houtside c hshift
  have hl : hillRealLabels q.val q.property.1 q.property.2 (2*(n : ℕ)-1)=
      (hillMiuraDiracLeft u.val (n : ℕ)).re^2-c^2 := by
    simpa only [hillMiuraSquaredLabels,hillMiuraPositiveFrequencies_left _ _ n.pos] using
      congrFun he (2*(n : ℕ)-1)
  have hr : hillRealLabels q.val q.property.1 q.property.2 (2*(n : ℕ))=
      (hillMiuraDiracRight u.val (n : ℕ)).re^2-c^2 := by
    simpa only [hillMiuraSquaredLabels,hillMiuraPositiveFrequencies_right _ _ n.pos] using
      congrFun he (2*(n : ℕ))
  have hrealpair := hillMiuraDiracPair_real u (n : ℕ)
  have hzl : ((hillMiuraDiracLeft u.val (n : ℕ)).re : ℂ)=hillMiuraDiracLeft u.val (n : ℕ) :=
    Complex.ext rfl hrealpair.1.symm
  have hzr : ((hillMiuraDiracRight u.val (n : ℕ)).re : ℂ)=hillMiuraDiracRight u.val (n : ℕ) :=
    Complex.ext rfl hrealpair.2.symm
  dsimp only [canonicalPeriodicMidpoint,canonicalPeriodicGap,dirichletSource]
  rw [(canonicalPeriodicEndpoints_sourcePhase (by norm_num) (by norm_num)
      (hillMiuraDiagonal u.val)).1,
    (canonicalPeriodicEndpoints_sourcePhase (by norm_num) (by norm_num)
      (hillMiuraDiagonal u.val)).2]
  change (hillMiuraDiracLeft u.val (n : ℕ)+hillMiuraDiracRight u.val (n : ℕ))/2*
    (hillMiuraDiracRight u.val (n : ℕ)-hillMiuraDiracLeft u.val (n : ℕ))=_
  dsimp only [hillRealGapHalfLength]
  rw [hr,hl,ofReal_div,ofReal_sub,ofReal_sub,ofReal_sub,ofReal_pow,ofReal_pow,
    ofReal_pow,hzl,hzr]
  norm_num only [ofReal_ofNat]
  ring

/-- A noncollapsed physical gap has a noncollapsed actual source gap. -/
theorem source_gap_ne_zero_of_original_halfLength_ne_zero (n : ℕ+)
    (hgap : hillRealGapHalfLength q.val q.property.1 q.property.2 n≠0) :
    canonicalPeriodicGap (by norm_num) (by norm_num)
      (periodOnePotential (P.dirichletSource (hillOriginalHminusSource q.val)))
      (periodOnePotential_mem _) (n : ℕ)≠0 := by
  intro hz
  have he := P.source_midpoint_mul_gap_eq_original_halfLength q hq hreal houtside c hshift n
  rw [hz,mul_zero] at he
  exact hgap (ofReal_eq_zero.mp he.symm)

omit houtside hshift in
/-- Positive labels keep the frequency midpoint away from the quadratic origin. -/
theorem source_midpoint_ne_zero (n : ℕ+) :
    canonicalPeriodicMidpoint (by norm_num) (by norm_num)
      (periodOnePotential (P.dirichletSource (hillOriginalHminusSource q.val)))
      (periodOnePotential_mem _) (n : ℕ)≠0 := by
  let u : PeriodOneRealL2 := ⟨P.miura.lift (hillOriginalHminusSource q.val),
    hreal _ hq.1 (hillOriginalHminusSource_real q.val q.property.2)⟩
  have hl := hillMiura_positive_gap_left_pos u (n : ℕ) (by exact_mod_cast n.pos)
  have ho := hillMiuraDiracPair_ordered u.val (n : ℕ)
  intro hz
  dsimp only [canonicalPeriodicMidpoint,dirichletSource] at hz
  rw [(canonicalPeriodicEndpoints_sourcePhase (by norm_num) (by norm_num)
      (hillMiuraDiagonal u.val)).1,
    (canonicalPeriodicEndpoints_sourcePhase (by norm_num) (by norm_num)
      (hillMiuraDiagonal u.val)).2] at hz
  change (hillMiuraDiracLeft u.val (n : ℕ)+hillMiuraDiracRight u.val (n : ℕ))/2=0 at hz
  have hh := congrArg Complex.re hz
  norm_num only [Complex.div_ofNat_re,Complex.add_re,Complex.zero_re] at hh
  change 0<(hillMiuraDiracLeft u.val (n : ℕ)).re at hl
  linarith

theorem source_gap_eq_zero_of_original_halfLength_zero (n : ℕ+)
    (hgap : hillRealGapHalfLength q.val q.property.1 q.property.2 n=0) :
    canonicalPeriodicGap (by norm_num) (by norm_num)
      (periodOnePotential (P.dirichletSource (hillOriginalHminusSource q.val)))
      (periodOnePotential_mem _) (n : ℕ)=0 := by
  have he := P.source_midpoint_mul_gap_eq_original_halfLength q hq hreal houtside c hshift n
  rw [hgap,ofReal_zero] at he
  exact (mul_eq_zero.mp he).resolve_left
    (P.source_midpoint_ne_zero q hq hreal n)

end NLS.KdV.HillHminusPsiChart
