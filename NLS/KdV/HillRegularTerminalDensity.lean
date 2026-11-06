import NLS.KdV.HillNormingSourceVariations
import NLS.KdV.HillRealSourceCompleteness
import NLS.KdV.HillDirichletSheetRoot
import Mathlib.Topology.Baire.Lemmas

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



/-- The physical terminal sheet vanishes exactly when its real log-norming coordinate does. -/
theorem hillDirichletSheetRoot_ne_zero_iff_logMultiplier
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n) :
    hillDirichletSheetRoot (SpectralWeight.one.toCoeff q.val)
      (hillDirichletEnergy q.val q.property.1 q.property.2 n hn)≠0 ↔
        hillDirichletLogMultiplier q.val q.property.1 q.property.2 n hn≠0 := by
  rw [hillDirichletSheetRoot_at_dirichlet_eq_norming q.val q.property.1 q.property.2 n hn,ofReal_ne_zero]
  have hc : (-1 : ℝ)^n*2≠0 := mul_ne_zero (pow_ne_zero n (by norm_num)) (by norm_num)
  rw [mul_ne_zero_iff,and_iff_right hc,Real.sinh_ne_zero]

/-- Each physical nonzero-terminal-sheet locus is open. -/
theorem isOpen_hillDirichletSheetRoot_ne_zero (n : ℕ) (hn : 1≤n) :
    IsOpen {q : RealPeriodOneHillPotential | hillDirichletSheetRoot (SpectralWeight.one.toCoeff q.val)
      (hillDirichletEnergy q.val q.property.1 q.property.2 n hn)≠0} := by
  have he : {q : RealPeriodOneHillPotential | hillDirichletSheetRoot (SpectralWeight.one.toCoeff q.val)
      (hillDirichletEnergy q.val q.property.1 q.property.2 n hn)≠0}=
      {q : RealPeriodOneHillPotential | hillDirichletLogMultiplier q.val q.property.1 q.property.2 n hn≠0} := by
    ext q
    exact hillDirichletSheetRoot_ne_zero_iff_logMultiplier q n hn
  rw [he]
  exact isOpen_ne.preimage (continuous_hillDirichletLogMultiplier n hn)

/-- The nonzero log-norming set is dense, even around closed physical gaps.
A zero germ would contradict the actual nonzero Dirichlet-source derivative. -/
theorem dense_hillDirichletLogMultiplier_ne_zero (n : ℕ) (hn : 1≤n) :
    Dense {q : RealPeriodOneHillPotential | hillDirichletLogMultiplier q.val q.property.1 q.property.2 n hn≠0} := by
  apply dense_iff_inter_open.mpr
  intro U hU hUne
  by_contra hempty
  obtain ⟨q,hqU⟩ := hUne
  have hzero (p : RealPeriodOneHillPotential) (hp : p∈U) :
      hillDirichletLogMultiplier p.val p.property.1 p.property.2 n hn=0 := by
    by_contra hne
    exact hempty ⟨p,hp,hne⟩
  obtain ⟨F,hF,hFreal,hFD⟩ := exists_hillLogNorming_dirichletSource_variations q n hn
  have heq : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      F (SpectralWeight.one.toCoeff p.val)=(fun _ : Coeff 2 => (0 : ℂ)) (SpectralWeight.one.toCoeff p.val) := by
    filter_upwards [hFreal,hU.mem_nhds hqU] with p hpF hpU
    rw [hpF,hzero p hpU,ofReal_zero]
  have hd := hillPhysicalCoefficientGerm_fderiv_eq_of_eventuallyEq q.val q.property.1 q.property.2
    F (fun _ : Coeff 2 => (0 : ℂ)) hF analyticAt_const heq
    (hillDirichletHamiltonianSource q n hn) (hillDirichletHamiltonianSource_mem_even q n hn)
  rw [hFD n hn] at hd
  norm_num at hd

/-- Each physical nonzero-terminal-sheet locus is dense. -/
theorem dense_hillDirichletSheetRoot_ne_zero (n : ℕ) (hn : 1≤n) :
    Dense {q : RealPeriodOneHillPotential | hillDirichletSheetRoot (SpectralWeight.one.toCoeff q.val)
      (hillDirichletEnergy q.val q.property.1 q.property.2 n hn)≠0} := by
  have he : {q : RealPeriodOneHillPotential | hillDirichletSheetRoot (SpectralWeight.one.toCoeff q.val)
      (hillDirichletEnergy q.val q.property.1 q.property.2 n hn)≠0}=
      {q : RealPeriodOneHillPotential | hillDirichletLogMultiplier q.val q.property.1 q.property.2 n hn≠0} := by
    ext q
    exact hillDirichletSheetRoot_ne_zero_iff_logMultiplier q n hn
  rw [he]
  exact dense_hillDirichletLogMultiplier_ne_zero n hn

/-- The actual locus where every positive physical Dirichlet terminal sheet is nonzero. -/
def hillRegularTerminalLocus : Set RealPeriodOneHillPotential :=
  {q | ∀ j : ℕ, hillDirichletSheetRoot (SpectralWeight.one.toCoeff q.val)
    (hillDirichletEnergy q.val q.property.1 q.property.2 (j+1) (by omega))≠0}

/-- All terminal sheets are simultaneously regular on a dense physical source locus.
The countable intersection uses completeness of the original real Hilbert source space. -/
theorem dense_hillRegularTerminalLocus : Dense hillRegularTerminalLocus := by
  let : CompleteSpace RealPeriodOneHillPotential := completeSpace_realPeriodOneHillPotential
  simp only [hillRegularTerminalLocus,Set.ofPred_forall]
  exact dense_iInter_of_isOpen_nat (fun j => isOpen_hillDirichletSheetRoot_ne_zero (j+1) (by omega))
    (fun j => dense_hillDirichletSheetRoot_ne_zero (j+1) (by omega))

end NLS.KdV
