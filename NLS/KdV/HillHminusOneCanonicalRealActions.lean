import NLS.KdV.HillHminusOneMiuraOutsideShift
import NLS.KdV.HillHminusOneMiuraCanonicalGaps
import NLS.ZakharovShabat.SourceRealHigherActionIntegral
import NLS.RealAnalysis.QuadraticIntegralPullback

/-! # Canonical real Hill actions and independence of the Miura representation

The original Hill discriminant and original canonical endpoints define
a literal two-over-pi arcosh gap integral. The exact real quadratic
change of variable identifies EVERY positive-index Miura action with
this same expression, including collapsed low gaps. Consequently its
value is independent of both the lift and the energy shift.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex MeasureTheory
open scoped ENNReal
namespace NLS.KdV
open NLS.ZakharovShabat NLS.RealAnalysis

def hillHminusRealGapProfile (q : PeriodOneHminusOne) (n : ℕ) (E : ℝ) : ℝ :=
  Real.arcosh ((if (n : ℤ)%2 = 0 then (hillHminusDiscriminant q E).re
    else -(hillHminusDiscriminant q E).re)/2)

def hillHminusCanonicalRealAction (q : PeriodOneHminusOne)
    (hq : IsRealPeriodOneHminusOne q) (n : ℕ+) : ℂ :=
  ((2/Real.pi * ∫ E in hillHminusLabels q hq (2*(n : ℕ)-1)..hillHminusLabels q hq (2*(n : ℕ)),
    hillHminusRealGapProfile q (n : ℕ) E : ℝ) : ℂ)

theorem hillHminusRealGapProfile_miura
    (q : PeriodOneHminusOne) (u : Coeff 2) (c : ℝ)
    (himage : periodOneMiura u = q+periodOneL2Inclusion (lp.single 2 0 (c : ℂ)))
    (n : ℕ) (x : ℝ) :
    sourceRealGapArcoshProfile (by simp) (hillMiuraDiagonal u) (n : ℤ) x =
      hillHminusRealGapProfile q n (x^2-c) := by
  have ht := congrArg Complex.re
    (hillHminusDiscriminant_shifted_miura_square q u (c : ℂ) (x : ℂ) himage)
  have he : (((x^2-c : ℝ) : ℂ)) = (x : ℂ)^2-(c : ℂ) := by push_cast; rfl
  dsimp only [sourceRealGapArcoshProfile,realGapHalfDiscriminant,hillHminusRealGapProfile]
  rw [he,ht]

theorem hillHminusMiuraIndexedAction_eq_canonicalRealAction
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q)
    (u : PeriodOneRealL2) (c : ℝ)
    (himage : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 (c : ℂ)))
    (hc : -(c : ℂ) ∉ singularHillSpectrum (periodOneOriginal q)) (n : ℕ+) :
    hillHminusMiuraIndexedAction u.val (n : ℕ) = hillHminusCanonicalRealAction q hq n := by
  let l : ℝ := (hillMiuraDiracLeft u.val (n : ℕ)).re
  let r : ℝ := (hillMiuraDiracRight u.val (n : ℕ)).re
  let F : ℝ → ℝ := sourceRealGapArcoshProfile (by simp) (hillMiuraDiagonal u.val) (n : ℕ)
  let g : ℝ → ℝ := hillHminusRealGapProfile q (n : ℕ)
  have hl : 0 < l := hillMiura_positive_gap_left_pos u (n : ℕ) (by exact_mod_cast n.pos)
  have hlr : l ≤ r := hillMiuraDiracPair_ordered u.val (n : ℕ)
  have hF : ContinuousOn F (Icc l r) :=
    (sourceRealGapArcoshProfile_spec (by simp) (by norm_num)
      (hillMiuraDiagonal u.val) (hillMiuraRealSource u).property (n : ℕ)).1
  have hpull (x : ℝ) : g (x^2-c) = F x :=
    (hillHminusRealGapProfile_miura q u.val c himage (n : ℕ) x).symm
  have hg : ContinuousOn g (Icc (l^2-c) (r^2-c)) :=
    continuousOn_of_quadratic_pullback l r c hl.le hlr F g hF (fun x _ => hpull x)
  have hi := integral_quadratic_shift l r c hl.le hlr g hg
  have hif : (∫ x in l..r, x*g (x^2-c)) = ∫ x in l..r, x*F x := by
    apply intervalIntegral.integral_congr
    intro x _
    change x*g (x^2-c) = x*F x
    rw [hpull x]
  rw [hif] at hi
  have hA := sourceIndexedHigherAction_eq_gapIntegral (by simp) (by norm_num)
    (hillMiuraRealSource u) (n : ℕ) 1
  change sourceIndexedHigherAction _ _ (n : ℕ) 1 (hillMiuraDiagonal u.val) =
    ((2/Real.pi * ∫ x in l..r, x^1*F x : ℝ) : ℂ) at hA
  simp only [pow_one] at hA
  obtain ⟨hleft,hright⟩ := hillHminusLabels_pair_eq_squared_miuraDirac q hq u c himage hc (n : ℕ) n.pos
  change hillHminusLabels q hq (2*(n : ℕ)-1) = l^2-c at hleft
  change hillHminusLabels q hq (2*(n : ℕ)) = r^2-c at hright
  unfold hillHminusMiuraIndexedAction hillHminusCanonicalRealAction
  rw [hA,hleft,hright]
  change 2*((2/Real.pi * ∫ x in l..r, x*F x : ℝ) : ℂ) =
    ((2/Real.pi * ∫ E in (l^2-c)..(r^2-c), g E : ℝ) : ℂ)
  rw [hi]
  push_cast
  ring

theorem hillHminusMiuraIndexedAction_independent
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q)
    (u v : PeriodOneRealL2) (c d : ℝ)
    (hu : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 (c : ℂ)))
    (hv : periodOneMiura v.val = q+periodOneL2Inclusion (lp.single 2 0 (d : ℂ)))
    (hc : -(c : ℂ) ∉ singularHillSpectrum (periodOneOriginal q))
    (hd : -(d : ℂ) ∉ singularHillSpectrum (periodOneOriginal q)) (n : ℕ+) :
    hillHminusMiuraIndexedAction u.val (n : ℕ) = hillHminusMiuraIndexedAction v.val (n : ℕ) :=
  (hillHminusMiuraIndexedAction_eq_canonicalRealAction q hq u c hu hc n).trans
    (hillHminusMiuraIndexedAction_eq_canonicalRealAction q hq v d hv hd n).symm

theorem hillHminusCanonicalRealAction_properties
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) (n : ℕ+) :
    0 ≤ (hillHminusCanonicalRealAction q hq n).re ∧
      (hillHminusCanonicalRealAction q hq n).im = 0 ∧
      (hillHminusCanonicalRealAction q hq n = 0 ↔
        ((hillHminusLabels q hq (2*(n : ℕ))-hillHminusLabels q hq (2*(n : ℕ)-1) : ℝ) : ℂ) = 0) := by
  obtain ⟨c,_,_,u,himage,houtside⟩ := exists_real_periodOneMiura_shift_outside_spectrum q hq 0
  have hi : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 ((c^2 : ℝ) : ℂ)) := by
    simpa only [ofReal_pow] using himage
  have hc : -((c^2 : ℝ) : ℂ) ∉ singularHillSpectrum (periodOneOriginal q) := by
    simpa only [ofReal_pow] using houtside
  rw [← hillHminusMiuraIndexedAction_eq_canonicalRealAction q hq u (c^2) hi hc n]
  have hs := hillHminusMiuraIndexedAction_positive_index_spec u (n : ℕ) (by exact_mod_cast n.pos)
  exact ⟨hs.1,hs.2.1,hillHminusMiuraIndexedAction_eq_zero_iff_Hill_gap q hq u (c^2) hi hc (n : ℕ) n.pos⟩

end NLS.KdV
