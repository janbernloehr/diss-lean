import NLS.KdV.HillHminusOneMiuraAllLabels
import NLS.KdV.HillHminusOutsideMiuraChart
import NLS.KdV.HillHminusPhysicalPeriodicLabels
import NLS.KdV.HillHminusOneCanonicalFreeLabels
import NLS.SequenceSpaces.PositiveEnergyMidpoints
import NLS.ZakharovShabat.SourceMidpointSequenceAnalytic
import NLS.ZakharovShabat.SourceHilbertSquaredGapAnalytic

/-! # Actual rough symmetric energy midpoints in one native Hilbert map

The symmetric frequency midpoint and squared gap are analytic through
collisions. Their shifted squares recover the actual energy midpoint at
every real source and every positive index on one complex neighborhood.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal
namespace NLS.KdV
open NLS.ZakharovShabat

def hillHminusGapMidpoint (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (n : ℕ+) : ℝ :=
  (hillHminusRealLabels q hr (2*(n : ℕ)-1)+hillHminusRealLabels q hr (2*(n : ℕ)))/2

theorem hillHminusGapMidpoint_zero_potential (hr : IsRealPeriodOneHminusOne 0) (n : ℕ+) :
    hillHminusGapMidpoint 0 hr n = freeHillValue (n : ℕ) := by
  simp only [hillHminusGapMidpoint,hillHminusRealLabels_zero]
  have hl : (2*(n : ℕ)-1+1)/2 = (n : ℕ) := by have hp := n.property; omega
  have hu : (2*(n : ℕ)+1)/2 = (n : ℕ) := by omega
  rw [hl,hu]
  ring

theorem hillHminusGapMidpoint_eq_physical (p : RealPeriodOneHillPotential) (n : ℕ+) :
    hillHminusGapMidpoint (hillPhysicalHminusEmbedding p).val
        (hillPhysicalHminusEmbedding p).property n =
      (hillRealLabels p.val p.property.1 p.property.2 (2*(n : ℕ)-1)+
        hillRealLabels p.val p.property.1 p.property.2 (2*(n : ℕ)))/2 := by
  simp only [hillHminusGapMidpoint,hillHminusRealLabels_eq_physical]

theorem exists_hillHminus_native_gap_midpoint_sequence
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) :
    ∃ V : Set PeriodOneHminusOne, ∃ T : PeriodOneHminusOne → Coeff 2,
      IsOpen V ∧ q ∈ V ∧ AnalyticOnNhd ℂ T V ∧
      (∀ p ∈ V, ∀ hp : IsRealPeriodOneHminusOne p, ∀ n : ℕ+,
        T p (n : ℤ) = ((hillHminusGapMidpoint p hp n : ℂ)-
          ((Real.pi : ℂ)*(n : ℕ))^2)/(n : ℂ)) ∧
      ∀ p : PeriodOneHminusOne, ∀ j : ℤ, j ≤ 0 → T p j = 0 := by
  obtain ⟨C,c,hcpos,hc,hqC,hreal,houtside⟩ := exists_hillHminus_outside_real_Miura_chart q hr
  let F : PeriodOneHminusOne → CoeffPair 2 := C.criticalSource
  have hF : AnalyticOnNhd ℂ F C.domain := C.analyticOnNhd_criticalSource
  have hFreal : IsRealType (CoeffPair.toMax 2 (F q)) :=
    hillMiuraDiagonal_isRealType _ (hreal q hqC hr)
  obtain ⟨W,hW,hrealW,hτ⟩ := exists_sourcePeriodicMidpointDisplacement_analytic_common_domain
    (by simp : (2 : ENNReal) ≠ ⊤) (by norm_num)
  obtain ⟨G,hG,hrealG,hg⟩ := exists_sourceHilbertSquaredGap_analytic_common_domain
  let V := C.domain ∩ F ⁻¹' (W ∩ G)
  have hV : IsOpen V := hF.continuousOn.isOpen_inter_preimage C.domain_open (hW.inter hG)
  let d : PeriodOneHminusOne → Coeff 2 := fun p =>
    sourcePeriodicMidpointDisplacement (by simp) (by norm_num) (F p)
  let g : PeriodOneHminusOne → Coeff 1 := fun p => sourceHilbertSquaredGap (F p)
  let T : PeriodOneHminusOne → Coeff 2 := fun p => Coeff.positiveEnergyMidpoints c (d p) (g p)
  have hd : AnalyticOnNhd ℂ d V := fun p hp => (hτ (F p) hp.2.1).comp (hF p hp.1)
  have hga : AnalyticOnNhd ℂ g V := fun p hp => (hg (F p) hp.2.2).comp (hF p hp.1)
  refine ⟨V,T,hV,⟨hqC,hrealW hFreal,hrealG hFreal⟩,?_,?_,?_⟩
  · intro p hp
    exact (Coeff.analyticOnNhd_positiveEnergyMidpoints c (d p,g p) (mem_univ _)).comp
      (f := fun r => (d r,g r)) ((hd p hp).prod (hga p hp))
  · intro p hp hpr n
    let u : PeriodOneRealL2 :=
      ⟨C.lift p,(periodOneL2Conjugation_fixed_iff _).mp (hreal p hp.1 hpr)⟩
    have hi : periodOneMiura u.val = p+periodOneL2Inclusion (lp.single 2 0 ((c^2 : ℝ) : ℂ)) := by
      simpa only [hc,ofReal_pow] using C.image p hp.1
    have hout : hillHminusRadicand p (-((c^2 : ℝ) : ℂ)) ≠ 0 := by
      simpa only [hc,ofReal_pow] using houtside p hp.1
    have hlabels := hillHminusLabels_pair_eq_squared_miuraDirac p hpr u (c^2) hi hout
      (n : ℕ) n.property
    have hpair := hillMiuraDiracPair_real u (n : ℕ)
    have hL : (hillHminusRealLabels p hpr (2*(n : ℕ)-1) : ℂ) =
        (hillMiuraDiracLeft u.val (n : ℕ))^2-(c : ℂ)^2 := by
      rw [hlabels.1,ofReal_sub,ofReal_pow,ofReal_pow]
      rw [show ((hillMiuraDiracLeft u.val (n : ℕ)).re : ℂ) =
        hillMiuraDiracLeft u.val (n : ℕ) from Complex.ext rfl hpair.1.symm]
    have hR : (hillHminusRealLabels p hpr (2*(n : ℕ)) : ℂ) =
        (hillMiuraDiracRight u.val (n : ℕ))^2-(c : ℂ)^2 := by
      rw [hlabels.2,ofReal_sub,ofReal_pow,ofReal_pow]
      rw [show ((hillMiuraDiracRight u.val (n : ℕ)).re : ℂ) =
        hillMiuraDiracRight u.val (n : ℕ) from Complex.ext rfl hpair.2.symm]
    have hτval : (Real.pi : ℂ)*(n : ℕ)+d p (n : ℤ) =
        (hillMiuraDiracLeft u.val (n : ℕ)+hillMiuraDiracRight u.val (n : ℕ))/2 := by
      simp only [d,sourcePeriodicMidpointDisplacement_apply,canonicalPeriodicMidpoint,
        F,HillHminusMiuraChart.criticalSource,hillMiuraDiracLeft,hillMiuraDiracRight,u,
        Int.cast_natCast]
      ring
    have hgval : g p (n : ℤ) =
        (hillMiuraDiracRight u.val (n : ℕ)-hillMiuraDiracLeft u.val (n : ℕ))^2 := by
      simp only [g,sourceHilbertSquaredGap_apply,canonicalPeriodicGap,F,
        HillHminusMiuraChart.criticalSource,hillMiuraDiracLeft,hillMiuraDiracRight,u]
    change Coeff.positiveEnergyMidpoints c (d p) (g p) (n : ℤ) = _
    rw [Coeff.positiveEnergyMidpoints_positive,hτval,hgval,
      hillHminusGapMidpoint,ofReal_div,ofReal_add,ofReal_ofNat,hL,hR]
    ring
  · intro p j hj
    exact Coeff.positiveEnergyMidpoints_nonpositive c (d p) (g p) j hj

end NLS.KdV
