import NLS.KdV.HillHminusOneCanonicalRealActions
import NLS.ZakharovShabat.SourceArcoshClosedGap

/-! # Continuous nonnegative canonical Hill gap profiles

The actual positive Miura interval parametrizes the WHOLE original Hill
gap. Its closed-gap arcosh data transfer to the original discriminant,
with the original parity and both endpoint values retained.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal
namespace NLS.KdV
open NLS.ZakharovShabat NLS.RealAnalysis

theorem hillHminus_parity_signed_trace (n : ℕ) (D : ℂ) :
    (if (n : ℤ)%2 = 0 then D else -D)/2 = (-1 : ℂ)^n*D/2 := by
  have hparity : ((n : ℤ)%2 = 0) ↔ n%2 = 0 := by omega
  simp only [hparity,neg_one_pow_eq_ite,Nat.even_iff]
  split_ifs <;> ring

theorem hillHminusRealGapProfile_canonical_gap_spec
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) (n : ℕ+) :
    let l := hillHminusLabels q hq (2*(n : ℕ)-1)
    let r := hillHminusLabels q hq (2*(n : ℕ))
    ContinuousOn (hillHminusRealGapProfile q (n : ℕ)) (Icc l r) ∧
      hillHminusRealGapProfile q (n : ℕ) l = 0 ∧
      hillHminusRealGapProfile q (n : ℕ) r = 0 ∧
      ∀ E ∈ Icc l r, 0 ≤ hillHminusRealGapProfile q (n : ℕ) E ∧
        cosh (hillHminusRealGapProfile q (n : ℕ) E : ℂ) =
          (-1 : ℂ)^(n : ℕ)*hillHminusDiscriminant q E/2 := by
  obtain ⟨d,_,_,u,himage,houtside⟩ := exists_real_periodOneMiura_shift_outside_spectrum q hq 0
  let c : ℝ := d^2
  have hi : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 (c : ℂ)) := by
    simpa only [c,ofReal_pow] using himage
  have hc : -(c : ℂ) ∉ singularHillSpectrum (periodOneOriginal q) := by
    simpa only [c,ofReal_pow] using houtside
  let a : ℝ := (hillMiuraDiracLeft u.val (n : ℕ)).re
  let b : ℝ := (hillMiuraDiracRight u.val (n : ℕ)).re
  let F : ℝ → ℝ := sourceRealGapArcoshProfile (by simp) (hillMiuraDiagonal u.val) (n : ℕ)
  let G : ℝ → ℝ := hillHminusRealGapProfile q (n : ℕ)
  have ha : 0 < a := hillMiura_positive_gap_left_pos u (n : ℕ) (by exact_mod_cast n.pos)
  have hab : a ≤ b := hillMiuraDiracPair_ordered u.val (n : ℕ)
  have hF := sourceRealGapArcoshProfile_spec (by simp) (by norm_num)
    (hillMiuraDiagonal u.val) (hillMiuraRealSource u).property (n : ℕ)
  have hpull (x : ℝ) : G (x^2-c) = F x :=
    (hillHminusRealGapProfile_miura q u.val c hi (n : ℕ) x).symm
  have hcont : ContinuousOn G (Icc (a^2-c) (b^2-c)) :=
    continuousOn_of_quadratic_pullback a b c ha.le hab F G hF.1 (fun x _ => hpull x)
  obtain ⟨hl,hr⟩ := hillHminusLabels_pair_eq_squared_miuraDirac q hq u c hi hc (n : ℕ) n.pos
  change hillHminusLabels q hq (2*(n : ℕ)-1) = a^2-c at hl
  change hillHminusLabels q hq (2*(n : ℕ)) = b^2-c at hr
  dsimp only
  rw [hl,hr]
  refine ⟨hcont,?_,?_,?_⟩
  · exact (hpull a).trans hF.2.1
  · exact (hpull b).trans hF.2.2.1
  · intro E hE
    let z : ℝ := Real.sqrt (E+c)
    obtain ⟨hz,he⟩ := sqrt_add_mem_of_mem_squared_interval a b c E ha.le hab hE
    have hdata := sourceRealGapArcoshProfile_closed_properties (by simp) (by norm_num)
      (hillMiuraDiagonal u.val) (hillMiuraRealSource u).property (n : ℕ) z hz
    change 0 ≤ F z ∧ cosh (F z : ℂ) = _ at hdata
    have hp : G E = F z := by rw [← he]; exact hpull z
    refine ⟨by change 0 ≤ G E; rw [hp]; exact hdata.1,?_⟩
    change cosh (G E : ℂ) = _
    rw [hp,hdata.2,hillHminus_parity_signed_trace]
    have ht := hillHminusDiscriminant_shifted_miura_square q u.val (c : ℂ) (z : ℂ) hi
    have henergy : (z : ℂ)^2-(c : ℂ) = (E : ℂ) := by
      rw [← ofReal_pow,← ofReal_sub]
      exact congrArg Complex.ofReal he
    rw [henergy] at ht
    rw [ht]

end NLS.KdV
