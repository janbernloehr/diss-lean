import NLS.KdV.HminusOneDirichletRealLabels
import NLS.KdV.HillHminusOneMiuraAllLabels
import NLS.KdV.HillMiuraPositiveGaps
import NLS.KdV.HillHminusOneMiuraOutsideShift

/-! # Every original Dirichlet label belongs to its original periodic gap

The complete real Dirichlet sequence and the complete Hill sequence use
the SAME positive Miura frequency index. Positivity permits squaring at
ALL indices, not only above a high cutoff. The result retains every low
gap and every collapsed pair on the full real H-minus-one domain.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
namespace NLS.KdV

theorem hillHminusDirichletLabels_mem_gap
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) (n : ℕ+) :
    hillHminusLabels q hq (2*(n : ℕ)-1) ≤ hillHminusDirichletLabels q hq n ∧
      hillHminusDirichletLabels q hq n ≤ hillHminusLabels q hq (2*(n : ℕ)) := by
  obtain ⟨d,_,_,u,hi,houtside⟩ := exists_real_periodOneMiura_shift_outside_spectrum q hq 0
  have hi' : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 ((d^2 : ℝ) : ℂ)) := by
    simpa only [ofReal_pow] using hi
  have hc : -((d^2 : ℝ) : ℂ) ∉ singularHillSpectrum (periodOneOriginal q) := by
    simpa only [ofReal_pow] using houtside
  obtain ⟨hl,hr⟩ := hillHminusLabels_pair_eq_squared_miuraDirac q hq u (d^2) hi' hc (n : ℕ) n.pos
  have hμ := congrFun (hillHminusDirichletLabels_eq_miura q hq u (d^2) hi') n
  have hpos := hillMiura_positive_gap_left_pos u (n : ℕ) (by exact_mod_cast n.pos)
  have hgap := hillMiuraDiracDirichlet_mem_gap u (n : ℕ)
  change 0 < (hillMiuraDiracLeft u.val (n : ℕ)).re at hpos
  have hμ' : hillHminusDirichletLabels q hq n =
      (hillMiuraDiracDirichlet u.val (n : ℕ)).re^2-d^2 := by
    rw [hμ]
    simp only [hillMiuraDirichletEnergy,sub_re,ofReal_re,pow_two,mul_re,
      hillMiuraDiracDirichlet_im_eq_zero,mul_zero,sub_zero]
  rw [hl,hr,hμ']
  constructor
  · exact sub_le_sub_right (pow_le_pow_left₀ hpos.le hgap.1 2) _
  · exact sub_le_sub_right (pow_le_pow_left₀ (hpos.trans_le hgap.1).le hgap.2 2) _

theorem norm_hillHminusDirichletLabels_sub_midpoint_le_half_gap
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) (n : ℕ+) :
    ‖((hillHminusDirichletLabels q hq n : ℝ) : ℂ)-
      (((hillHminusLabels q hq (2*(n : ℕ)-1)+hillHminusLabels q hq (2*(n : ℕ)))/2 : ℝ) : ℂ)‖ ≤
      ‖((hillHminusLabels q hq (2*(n : ℕ))-hillHminusLabels q hq (2*(n : ℕ)-1) : ℝ) : ℂ)‖/2 := by
  obtain ⟨hl,hr⟩ := hillHminusDirichletLabels_mem_gap q hq n
  have hgap : 0 ≤ hillHminusLabels q hq (2*(n : ℕ))-hillHminusLabels q hq (2*(n : ℕ)-1) := by linarith
  rw [← ofReal_sub,Complex.norm_real,Real.norm_eq_abs,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hgap]
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem hillHminusDirichletLabels_eq_endpoint_of_gap_zero
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) (n : ℕ+)
    (hgap : hillHminusLabels q hq (2*(n : ℕ))-hillHminusLabels q hq (2*(n : ℕ)-1) = 0) :
    hillHminusDirichletLabels q hq n = hillHminusLabels q hq (2*(n : ℕ)-1) := by
  obtain ⟨hl,hr⟩ := hillHminusDirichletLabels_mem_gap q hq n
  linarith

end NLS.KdV
