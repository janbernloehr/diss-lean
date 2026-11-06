import NLS.KdV.HillGlobalDifferentialReality
import NLS.KdV.HillDirichletLabels

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat NLS.FunctionalAnalysis
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



/-- The actual normalized numerator never vanishes at its own Dirichlet label:
all of its retained roots lie in strictly separated other physical gaps. -/
theorem hillAbelianSelectedGlobalPsi_own_dirichlet_ne_zero
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n) :
    hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n hn
      (hillDirichletEnergy q.val q.property.1 q.property.2 n hn)≠0 := by
  intro hz
  obtain ⟨j,hjn,hj⟩ := (hillAbelianSelectedGlobalPsi_zero_iff q.val q.property.1 q.property.2 n hn _).mp hz
  have hμ := hillDirichletEnergy_mem_gap q.val q.property.1 q.property.2 n hn
  have hσ := (hillAbelianSelectedGlobalRoots q.val q.property.1 q.property.2 n hn).property j
  have he := Complex.ofReal_injective hj
  have hsep (a b : ℕ) (hab : a<b) :
      hillRealLabels q.val q.property.1 q.property.2 (2*a)<
        hillRealLabels q.val q.property.1 q.property.2 (2*b-1) :=
    (hillRealLabels_band_strict q.val q.property.1 q.property.2 a).trans_le
      (monotone_hillRealLabels q.val q.property.1 q.property.2 (by omega))
  rcases lt_or_gt_of_ne hjn with hlt | hgt
  · have h := (hσ.2.trans_lt (hsep (j+1) n hlt)).trans_le hμ.1
    exact (ne_of_lt h) he
  · have h := (hμ.2.trans_lt (hsep n (j+1) hgt)).trans_le hσ.1
    exact (ne_of_lt h) he.symm

end NLS.KdV
