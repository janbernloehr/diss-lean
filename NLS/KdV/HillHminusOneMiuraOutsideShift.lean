import NLS.KdV.HillHminusOneMiuraAllLabels
import NLS.KdV.SingularHillSemibounded
import NLS.SequenceSpaces.PeriodOneMiuraRealNeighborhood

/-! # Miura energy shifts below the full spectrum on one complex neighborhood

The actual full-domain form bound chooses an outside-spectrum shift,
uniformly for all complex sources in a norm neighborhood. The analytic
Miura lift preserves every nearby real source and retains its exact
unit-period distributional equation.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
open scoped ENNReal ComplexConjugate
namespace NLS.KdV

theorem neg_shift_not_mem_singularHillSpectrum_of_norm_bound
    (a : PeriodOneHminusOne) (B c : ℝ) (ha : ‖a‖ ≤ B)
    (hc : singularHillLowerBoundConstant B < c) :
    -(c : ℂ) ∉ singularHillSpectrum (periodOneOriginal a) := by
  intro hs
  obtain ⟨f,hf0,hf⟩ := (mem_singularHillSpectrum_iff (periodOneOriginal a) (-(c : ℂ))).mp hs
  have hb := singularHill_eigenvalue_re_lower_bound_of_norm_le B (periodOneOriginal a)
    ((norm_periodOneOriginal_le a).trans ha) (-(c : ℂ)) f hf0 hf
  simp only [neg_re,ofReal_re] at hb
  linarith

theorem exists_periodOneMiura_energyChart_outside_spectrum (q : PeriodOneHminusOne) (A : ℝ) :
    ∃ c : ℝ, 0 < c ∧ A < c ∧
      ∃ V : Set PeriodOneHminusOne, IsOpen V ∧ q ∈ V ∧
        ∃ u : PeriodOneHminusOne → Coeff 2, AnalyticOnNhd ℂ u V ∧
          (∀ a ∈ V, IsRealPeriodOneHminusOne a → ∀ k : ℤ, u a (-k) = conj (u a k)) ∧
          (∀ a ∈ V, periodOneMiura (u a) =
            a+periodOneL2Inclusion (lp.single 2 0 ((c : ℂ)^2))) ∧
          ∀ a ∈ V, -((c : ℂ)^2) ∉ singularHillSpectrum (periodOneOriginal a) := by
  let B : ℝ := ‖q‖+1
  let C : ℝ := singularHillLowerBoundConstant B
  obtain ⟨c,hc,hbig,U,hU,hqU,u,hu,hreal,himage⟩ :=
    exists_real_preserving_periodOneMiura_energyChart q (max A (C+1))
  have hAc : A < c := (le_max_left _ _).trans_lt hbig
  have hC : 0 ≤ C := singularHillLowerBoundConstant_nonneg B
  have hCc : C+1 < c := (le_max_right _ _).trans_lt hbig
  have hshift : C < c^2 := by nlinarith
  let V : Set PeriodOneHminusOne := U ∩ ball q 1
  have hqV : q ∈ V := ⟨hqU,by simp⟩
  refine ⟨c,hc,hAc,V,hU.inter isOpen_ball,hqV,u,hu.mono inter_subset_left,?_,?_,?_⟩
  · intro a ha har k
    exact hreal a ha.1 har k
  · intro a ha
    exact himage a ha.1
  · intro a ha
    have hnorm : ‖a‖ ≤ B := by
      have hdist : ‖a-q‖ < 1 := by simpa only [mem_ball,dist_eq_norm] using ha.2
      have ht := norm_le_norm_sub_add a q
      dsimp [B]
      linarith
    have hnot := neg_shift_not_mem_singularHillSpectrum_of_norm_bound a B (c^2) hnorm hshift
    simpa only [ofReal_pow] using hnot

/-- Every real H-minus-one source has a real Miura representation with
arbitrarily large shift and zero frequency excluded from the full spectrum. -/
theorem exists_real_periodOneMiura_shift_outside_spectrum
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) (A : ℝ) :
    ∃ c : ℝ, 0 < c ∧ A < c ∧ ∃ u : PeriodOneRealL2,
      periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 ((c : ℂ)^2)) ∧
      -((c : ℂ)^2) ∉ singularHillSpectrum (periodOneOriginal q) := by
  obtain ⟨c,hc,hAc,V,_,hqV,u,_,hreal,himage,houtside⟩ :=
    exists_periodOneMiura_energyChart_outside_spectrum q A
  exact ⟨c,hc,hAc,⟨u q,hreal q hqV hq⟩,himage q hqV,houtside q hqV⟩

end NLS.KdV
