import NLS.KdV.HillFullPhaseSquare
import NLS.KdV.HillRegularTerminalDensity

noncomputable section
set_option autoImplicit false
open Set Complex Metric Filter Topology NLS.ZakharovShabat
open scoped ComplexConjugate
namespace NLS.KdV

/-- The ORIGINAL full phase factor is continuous at every open own gap,
including periodic Dirichlet terminals with zero sheet. -/
theorem continuousAt_hillOriginalFullPhaseFactor_open (n : ℕ+) (q : RealPeriodOneHillPotential)
    (hgap : hillRealGapHalfLength q.val q.property.1 q.property.2 n≠0) :
    ContinuousAt (hillOriginalFullPhaseFactor n) q := by
  have h0q : SpectralWeight.one.toCoeff (0:WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0 := by
    simpa only [map_zero] using (Coeff.paritySubspace 0).zero_mem
  have h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0:WeightedCoeff SpectralWeight.one.toWeight 2)) := by
    intro k
    simp
  exact (continuousAt_hillDirichletCirclePhase_open q.val q.property.1 q.property.2 n n.pos hgap).mul
    (Complex.continuous_exp.continuousAt.comp
      (continuousAt_const.mul (continuous_hillSummedRegularAbelianCorrection h0q h0r n n.pos).continuousAt))

namespace HillHminusPsiChart
variable (P : HillHminusPsiChart) (q : RealPeriodOneHillPotential)
  (hq : hillOriginalHminusSource q.val∈P.source)
  (hreal : ∀ a∈P.miura.domain, IsRealPeriodOneHminusOne a → ∀ k : ℤ,
    P.miura.lift a (-k)=conj (P.miura.lift a k))
  (houtside : hillHminusRadicand (hillOriginalHminusSource q.val) (-P.miura.energyShift)≠0)
  (c : ℝ) (hshift : P.miura.energyShift=(c:ℂ)^2)
include hq hreal houtside hshift

/-- Original and source own gaps are simultaneously open, with the
actual positive label and without a nonzero-terminal-sheet hypothesis. -/
theorem original_open_mem_sourceFullPhaseDomain (n : ℕ+)
    (hgap : hillRealGapHalfLength q.val q.property.1 q.property.2 n≠0) :
    hillOriginalHminusSource q.val∈P.sourceFullPhaseDomain n := by
  have ha := P.mem_sourceBetaDomain_of_real (hillOriginalHminusSource q.val) hq
    (hreal _ hq.1 (hillOriginalHminusSource_real q.val q.property.2))
  refine ⟨hq,ha.2,?_⟩
  intro hc
  let u := P.miura.lift (hillOriginalHminusSource q.val)
  have he := P.original_labels_eq_squared_miuraDirac q hq hreal houtside c hshift
  have hl : hillRealLabels q.val q.property.1 q.property.2 (2*(n:ℕ)-1)=
      (hillMiuraDiracLeft u (n:ℕ)).re^2-c^2 := by
    simpa only [hillMiuraSquaredLabels,hillMiuraPositiveFrequencies_left _ _ n.pos] using congrFun he (2*(n:ℕ)-1)
  have hu : hillRealLabels q.val q.property.1 q.property.2 (2*(n:ℕ))=
      (hillMiuraDiracRight u (n:ℕ)).re^2-c^2 := by
    simpa only [hillMiuraSquaredLabels,hillMiuraPositiveFrequencies_right _ _ n.pos] using congrFun he (2*(n:ℕ))
  change canonicalPeriodicRight (by simp) (by norm_num)
      (periodOnePotential (sourcePhase (hillMiuraDiagonal u))) (periodOnePotential_mem _) (n:ℕ)-
    canonicalPeriodicLeft (by simp) (by norm_num)
      (periodOnePotential (sourcePhase (hillMiuraDiagonal u))) (periodOnePotential_mem _) (n:ℕ)=0 at hc
  obtain ⟨hleft,hright⟩ := canonicalPeriodicEndpoints_sourcePhase (by simp) (by norm_num) (hillMiuraDiagonal u)
  rw [hleft,hright] at hc
  have hRL : hillMiuraDiracRight u (n:ℕ)=hillMiuraDiracLeft u (n:ℕ) := sub_eq_zero.mp hc
  apply hgap
  dsimp only [hillRealGapHalfLength]
  rw [hl,hu,hRL]
  ring

end HillHminusPsiChart
namespace HillHminusPsiChart

/-- The SQUARE of the COMPLETE ORIGINAL phase equals the actual
analytic source candidate at EVERY original open own gap, including
zero-sheet periodic terminals. Regular terminal density closes the
endpoint case using the original continuous physical phase. -/
theorem originalFullPhaseFactor_sq_eq_source_open (P : HillHminusPsiChart)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num)
      P.family.originalDomain P.family.domain P.family.roots)
    (hreal : ∀ a∈P.miura.domain, IsRealPeriodOneHminusOne a → ∀ k : ℤ,
      P.miura.lift a (-k)=conj (P.miura.lift a k))
    (houtside : ∀ a∈P.miura.domain, hillHminusRadicand a (-P.miura.energyShift)≠0)
    (c : ℝ) (hshift : P.miura.energyShift=(c:ℂ)^2)
    (n : ℕ+) (q : RealPeriodOneHillPotential) (hq : hillOriginalHminusSource q.val∈P.source)
    (hgap : hillRealGapHalfLength q.val q.property.1 q.property.2 n≠0) :
    hillOriginalFullPhaseFactor n q^2=P.sourceFullPhaseSquare n (hillOriginalHminusSource q.val) := by
  let V : Set RealPeriodOneHillPotential := {p | hillOriginalHminusSource p.val∈P.sourceFullPhaseDomain n ∧
    hillRealGapHalfLength p.val p.property.1 p.property.2 n≠0}
  have hV : IsOpen V := ((P.sourceFullPhaseDomain_open H n).preimage
    (hillOriginalHminusSource.continuous.comp continuous_subtype_val)).inter
      (isOpen_compl_singleton.preimage (continuous_hillRealGapHalfLength n))
  have hqD := P.original_open_mem_sourceFullPhaseDomain q hq hreal (houtside _ hq.1) c hshift n hgap
  have hqV : q∈V := ⟨hqD,hgap⟩
  have hc : ContinuousAt (fun p : RealPeriodOneHillPotential =>
      hillOriginalFullPhaseFactor n p^2-P.sourceFullPhaseSquare n (hillOriginalHminusSource p.val)) q :=
    ((continuousAt_hillOriginalFullPhaseFactor_open n q hgap).pow 2).sub
      (((P.analytic_sourceFullPhaseSquare H n _ hqD).continuousAt).comp
        (f := fun p : RealPeriodOneHillPotential => hillOriginalHminusSource p.val)
        (hillOriginalHminusSource.continuous.comp continuous_subtype_val).continuousAt)
  apply sub_eq_zero.mp
  apply hc.continuousWithinAt.eq_const_of_mem_closure
    ((dense_hillDirichletSheetRoot_ne_zero n n.pos).open_subset_closure_inter hV hqV)
  intro p hp
  have hpP := hp.1.1.1
  exact sub_eq_zero.mpr (P.originalFullPhaseFactor_sq_eq_source p hpP hreal (houtside _ hpP.1) c hshift H n hp.1.2 hp.2)

end HillHminusPsiChart
end NLS.KdV
