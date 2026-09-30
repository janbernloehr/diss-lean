import NLS.SequenceSpaces.UniformHolderSums
import NLS.SequenceSpaces.CoefficientDecay
import NLS.SequenceSpaces.Translation

/-!
# Decay of shifted Hölder sums

A finite-exponent coefficient sequence can be approximated in norm by
a finite truncation. Against a translated conjugate sequence, its
finite head vanishes coordinatewise and its remaining sum is uniformly
small by Hölder. This also applies to sums dominated by two such
majorants, without requiring any sign or phase agreement.
-/

noncomputable section
open Filter Topology
open scoped ENNReal
namespace NLS.Coeff
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- Finite-exponent coordinates vanish along the cofinite integer
filter, equivalently as the absolute index tends to infinity. -/
theorem tendsto_norm_apply_cofinite (hp : p ≠ ⊤) (a : Coeff p) :
    Tendsto (fun m : ℤ => ‖a m‖) cofinite (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := exists_cutoff_norm_apply_lt hp a hε
  have hlarge : ∀ᶠ m : ℤ in cofinite, N ≤ m.natAbs := by
    apply Filter.eventually_cofinite.mpr
    apply (Finset.Icc (-(N : ℤ)) N).finite_toSet.subset
    intro m hm
    simp only [Set.mem_ofPred_eq, not_le] at hm
    simp only [Finset.mem_coe, Finset.mem_Icc]
    constructor <;> omega
  filter_upwards [hlarge] with m hm
  simpa only [dist_eq_norm, sub_zero, Real.norm_of_nonneg (norm_nonneg _)] using hN m hm

omit [Fact (1 ≤ p)] in
/-- A finite head and the norm of the coefficient remainder bound
the full absolute pairing with every translated conjugate sequence. -/
theorem tsum_norm_mul_shift_le_head_add_tail
    (hc : p.toReal.HolderConjugate q.toReal)
    (a : Coeff p) (b : Coeff q) (s : Finset ℤ) (n : ℤ) :
    (∑' m : ℤ, ‖a m‖ * ‖shift n b m‖) ≤
      (∑ m ∈ s, ‖a m‖ * ‖shift n b m‖) + ‖a - truncate s a‖ * ‖b‖ := by
  classical
  have ha := lp.tsum_mul_le_mul_norm hc a (shift n b)
  have hhead := lp.tsum_mul_le_mul_norm hc (truncate s a) (shift n b)
  have htail := lp.tsum_mul_le_mul_norm hc (a - truncate s a) (shift n b)
  have hpoint (m : ℤ) : ‖a m‖ * ‖shift n b m‖ ≤
      ‖truncate s a m‖ * ‖shift n b m‖ +
        ‖(a - truncate s a) m‖ * ‖shift n b m‖ := by
    have he : a m = truncate s a m + (a - truncate s a) m := by
      simp only [lp.coeFn_sub, Pi.sub_apply]
      abel
    have hnorm : ‖a m‖ ≤ ‖truncate s a m‖ + ‖(a - truncate s a) m‖ := by
      conv_lhs => rw [he]
      exact norm_add_le _ _
    simpa only [add_mul] using mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)
  have hfin : (∑' m : ℤ, ‖truncate s a m‖ * ‖shift n b m‖) =
      ∑ m ∈ s, ‖a m‖ * ‖shift n b m‖ := by
    rw [tsum_eq_sum (s := s) (fun m hm => by simp [truncate_apply, hm])]
    apply Finset.sum_congr rfl
    intro m hm
    rw [truncate_apply, if_pos hm]
  calc
    _ ≤ ∑' m : ℤ, (‖truncate s a m‖ * ‖shift n b m‖ +
        ‖(a - truncate s a) m‖ * ‖shift n b m‖) :=
      ha.1.tsum_le_tsum hpoint (hhead.1.add htail.1)
    _ = (∑ m ∈ s, ‖a m‖ * ‖shift n b m‖) +
        ∑' m : ℤ, ‖(a - truncate s a) m‖ * ‖shift n b m‖ := by
      rw [hhead.1.tsum_add htail.1, hfin]
    _ ≤ _ := add_le_add le_rfl (by simpa only [norm_shift] using htail.2)

/-- Absolute Hölder pairings with translated finite-exponent
sequences vanish in both directions of the integer lattice. -/
theorem tendsto_tsum_norm_mul_shift_zero
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hc : p.toReal.HolderConjugate q.toReal)
    (a : Coeff p) (b : Coeff q) :
    Tendsto (fun n : ℤ => ∑' m : ℤ, ‖a m‖ * ‖shift n b m‖) cofinite (𝓝 0) := by
  classical
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ := ε / (2 * (‖b‖ + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨s,hs⟩ := Metric.tendsto_atTop.mp (tendsto_truncate hp a) δ hδ
  have htail : ‖a - truncate s a‖ < δ := by
    simpa only [dist_eq_norm, norm_sub_rev] using hs s le_rfl
  have hsmall : ‖a - truncate s a‖ * ‖b‖ < ε / 2 := by
    have he : δ * (‖b‖ + 1) = ε / 2 := by
      dsimp [δ]
      field_simp
    have hle : ‖a - truncate s a‖ * ‖b‖ ≤
        ‖a - truncate s a‖ * (‖b‖ + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
    exact hle.trans_lt (by nlinarith)
  have hb := tendsto_norm_apply_cofinite hq b
  have hterm (m : ℤ) : Tendsto (fun n : ℤ => ‖a m‖ * ‖shift n b m‖)
      cofinite (𝓝 0) := by
    simpa only [shift_apply, Equiv.subLeft_apply, Function.comp_apply, mul_zero] using
      (tendsto_const_nhds (x := ‖a m‖)).mul
        (hb.comp (Equiv.subLeft m).injective.tendsto_cofinite)
  have hhead : Tendsto (fun n : ℤ => ∑ m ∈ s, ‖a m‖ * ‖shift n b m‖)
      cofinite (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum s (fun m _ => hterm m)
  filter_upwards [hhead.eventually_lt_const (half_pos hε)] with n hn
  have hbound := tsum_norm_mul_shift_le_head_add_tail hc a b s n
  have hnonneg : 0 ≤ ∑' m : ℤ, ‖a m‖ * ‖shift n b m‖ :=
    tsum_nonneg (fun m => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  rw [dist_eq_norm, sub_zero, Real.norm_of_nonneg hnonneg]
  linarith

/-- Any double-indexed series below two shifted Hölder majorants
has a vanishing complete absolute sum. -/
theorem tendsto_tsum_norm_of_two_shift_holder_bounds
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hc : p.toReal.HolderConjugate q.toReal)
    (a d : Coeff p) (b : Coeff q) (u : ℤ → ℤ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hu : ∀ n m, ‖u n m‖ ≤ C * (‖a m‖ + ‖d m‖) * ‖shift n b m‖) :
    Tendsto (fun n : ℤ => ∑' m : ℤ, ‖u n m‖) cofinite (𝓝 0) := by
  have hbound (n : ℤ) : (∑' m : ℤ, ‖u n m‖) ≤
      C * ((∑' m : ℤ, ‖a m‖ * ‖shift n b m‖) +
        (∑' m : ℤ, ‖d m‖ * ‖shift n b m‖)) := by
    have ha := lp.tsum_mul_le_mul_norm hc a (shift n b)
    have hd := lp.tsum_mul_le_mul_norm hc d (shift n b)
    have hs : Summable (fun m => C * (‖a m‖ * ‖shift n b m‖ +
        ‖d m‖ * ‖shift n b m‖)) := (ha.1.add hd.1).mul_left C
    have hdom (m : ℤ) : ‖u n m‖ ≤ C *
        (‖a m‖ * ‖shift n b m‖ + ‖d m‖ * ‖shift n b m‖) := by
      convert hu n m using 1
      ring
    have habs := (summable_norm_of_two_holder_bounds hc a d (shift n b) (u n) C hC
      (hu n)).1
    calc
      _ ≤ ∑' m : ℤ, C * (‖a m‖ * ‖shift n b m‖ + ‖d m‖ * ‖shift n b m‖) :=
        habs.tsum_le_tsum hdom hs
      _ = _ := by rw [tsum_mul_left, ha.1.tsum_add hd.1]
  have hlim : Tendsto (fun n : ℤ => C *
      ((∑' m : ℤ, ‖a m‖ * ‖shift n b m‖) +
        (∑' m : ℤ, ‖d m‖ * ‖shift n b m‖))) cofinite (𝓝 0) := by
    simpa only [add_zero, mul_zero] using tendsto_const_nhds.mul
      ((tendsto_tsum_norm_mul_shift_zero hp hq hc a b).add
        (tendsto_tsum_norm_mul_shift_zero hp hq hc d b))
  exact squeeze_zero (fun n => tsum_nonneg (fun m => norm_nonneg _)) hbound hlim

/-- The same majorants force the actual complex series sum to vanish. -/
theorem tendsto_tsum_of_two_shift_holder_bounds
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hc : p.toReal.HolderConjugate q.toReal)
    (a d : Coeff p) (b : Coeff q) (u : ℤ → ℤ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hu : ∀ n m, ‖u n m‖ ≤ C * (‖a m‖ + ‖d m‖) * ‖shift n b m‖) :
    Tendsto (fun n : ℤ => ∑' m : ℤ, u n m) cofinite (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _) _
    (tendsto_tsum_norm_of_two_shift_holder_bounds hp hq hc a d b u C hC hu)
  intro n
  exact norm_tsum_le_tsum_norm
    (summable_norm_of_two_holder_bounds hc a d (shift n b) (u n) C hC (hu n)).1

end NLS.Coeff
