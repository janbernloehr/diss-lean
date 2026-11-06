import NLS.KdV.HillHminusGapMidpointSequence
import NLS.SequenceSpaces.PositiveEnergyGapSquares

/-! # Actual rough normalized energy gap squares as a native ell1 map

The symmetric frequency formula squares the sum and difference of the
actual positive Dirac endpoints. Full periodic multiplicities fix the
energy labels even when gaps collapse.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal
namespace NLS.KdV
open NLS.ZakharovShabat

theorem exists_hillHminus_native_gap_square_sequence
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) :
    ∃ V : Set PeriodOneHminusOne, ∃ G : PeriodOneHminusOne → Coeff 1,
      IsOpen V ∧ q ∈ V ∧ AnalyticOnNhd ℂ G V ∧
      (∀ p ∈ V, ∀ hp : IsRealPeriodOneHminusOne p, ∀ n : ℕ+,
        G p (n : ℤ) = (((hillHminusRealLabels p hp (2*(n : ℕ)) : ℂ)-
          (hillHminusRealLabels p hp (2*(n : ℕ)-1) : ℂ))/(n : ℂ))^2) ∧
      ∀ p : PeriodOneHminusOne, ∀ j : ℤ, j ≤ 0 → G p j = 0 := by
  obtain ⟨C,c,_,hc,hqC,hreal,houtside⟩ := exists_hillHminus_outside_real_Miura_chart q hr
  let F : PeriodOneHminusOne → CoeffPair 2 := C.criticalSource
  have hF : AnalyticOnNhd ℂ F C.domain := C.analyticOnNhd_criticalSource
  have hFreal : IsRealType (CoeffPair.toMax 2 (F q)) :=
    hillMiuraDiagonal_isRealType _ (hreal q hqC hr)
  obtain ⟨W,hW,hrealW,hτ⟩ := exists_sourcePeriodicMidpointDisplacement_analytic_common_domain
    (by simp : (2 : ENNReal) ≠ ⊤) (by norm_num)
  obtain ⟨U,hU,hrealU,hg⟩ := exists_sourceHilbertSquaredGap_analytic_common_domain
  let V := C.domain ∩ F ⁻¹' (W ∩ U)
  have hV : IsOpen V := hF.continuousOn.isOpen_inter_preimage C.domain_open (hW.inter hU)
  let d : PeriodOneHminusOne → Coeff 2 := fun p =>
    sourcePeriodicMidpointDisplacement (by simp) (by norm_num) (F p)
  let g : PeriodOneHminusOne → Coeff 1 := fun p => sourceHilbertSquaredGap (F p)
  let G : PeriodOneHminusOne → Coeff 1 := fun p => Coeff.positiveEnergyGapSquares (d p) (g p)
  have hd : AnalyticOnNhd ℂ d V := fun p hp => (hτ (F p) hp.2.1).comp (hF p hp.1)
  have hga : AnalyticOnNhd ℂ g V := fun p hp => (hg (F p) hp.2.2).comp (hF p hp.1)
  refine ⟨V,G,hV,⟨hqC,hrealW hFreal,hrealU hFreal⟩,?_,?_,?_⟩
  · intro p hp
    exact (Coeff.analyticOnNhd_positiveEnergyGapSquares (d p,g p) (mem_univ _)).comp
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
    change Coeff.positiveEnergyGapSquares (d p) (g p) (n : ℤ) = _
    rw [Coeff.positiveEnergyGapSquares_positive,hgval,hL,hR]
    have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast n.ne_zero
    have hs : 2*(Real.pi : ℂ)+2*d p (n : ℤ)/(n : ℂ) =
        (hillMiuraDiracLeft u.val (n : ℕ)+hillMiuraDiracRight u.val (n : ℕ))/(n : ℂ) := by
      field_simp [hn0]
      linear_combination 2*hτval
    rw [hs]
    ring
  · intro p j hj
    exact Coeff.positiveEnergyGapSquares_nonpositive (d p) (g p) j hj

end NLS.KdV
