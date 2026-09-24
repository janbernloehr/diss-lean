import NLS.ZakharovShabat.SourceStandardRootOmittedPrefactorSign

/-!
# Parity of finite omitted-root products

The symmetric cutoff has one negative zero-mode prefactor and one
negative pair for each positive integer smaller than the selected
absolute index. Every subsequent pair is positive.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

private theorem signed_prod_range_pos (f : ℕ → ℝ) (r N : ℕ)
    (hN : r ≤ N) (hneg : ∀ j < r, f j < 0)
    (hpos : ∀ j, r ≤ j → 0 < f j) :
    0 < (-1:ℝ)^r * ∏ j ∈ Finset.range N, f j := by
  have hprefix : ∀ q : ℕ, (∀ j < q, f j < 0) →
      0 < (-1:ℝ)^q * ∏ j ∈ Finset.range q, f j := by
    intro q
    induction q with
    | zero => simp
    | succ q ih =>
      intro hq
      have hprev := ih (fun j hj => hq j (Nat.lt_succ_of_lt hj))
      have hlast : 0 < -f q := neg_pos.mpr (hq q (Nat.lt_succ_self q))
      rw [Finset.prod_range_succ, pow_succ]
      calc
        (-1:ℝ)^q * (-1) * ((∏ j ∈ Finset.range q, f j) * f q) =
            ((-1:ℝ)^q * ∏ j ∈ Finset.range q, f j) * (-f q) := by ring
        _ > 0 := mul_pos hprev hlast
  induction N, hN using Nat.le_induction with
  | base => exact hprefix r hneg
  | succ N hNr ih =>
    rw [Finset.prod_range_succ]
    calc
      (-1:ℝ)^r * ((∏ j ∈ Finset.range N, f j) * f N) =
          ((-1:ℝ)^r * ∏ j ∈ Finset.range N, f j) * f N := by ring
      _ > 0 := mul_pos ih (hpos N hNr)

/-- For a nonzero selected index and any cutoff reaching it, the real
part of the finite omitted product has sign `(-1)^|n|`. -/
theorem sourceStandardRootOmittedPartialProduct_signed_re_pos
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    {n : ℤ} (hn : n ≠ 0) (N : ℕ) (hN : n.natAbs ≤ N) {x : ℝ}
    (hx : x ∈ Ioo
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re) :
    0 < (-1:ℝ)^n.natAbs *
      (sourceStandardRootOmittedPartialProduct hp hp1 n N ((x:ℂ),ψ)).re := by
  let a : ℂ := sourceStandardRoot hp hp1 ψ 0 (x:ℂ) /
    singleSpectralDenominator n
  let f (j : ℕ) : ℂ := sourceStandardRootOmittedPairedFactor
    hp hp1 ψ (x:ℂ) n j
  have ha : a = (a.re:ℂ) := by
    have hr := sourceStandardRoot_im_eq_zero_off_selected_realGap
      hp hp1 ψ hreal (Ne.symm hn) hx
    have hd : (singleSpectralDenominator n).im = 0 := by
      unfold singleSpectralDenominator
      split_ifs <;> simp
    apply Complex.ext
    · rfl
    · simp [a, Complex.div_im, hr, hd]
  have hf (j : ℕ) : f j = ((f j).re:ℂ) :=
    sourceStandardRootOmittedPairedFactor_eq_ofReal_on_realGap
      hp hp1 ψ hreal n j hx
  have hprod : (∏ j ∈ Finset.range N, f j) =
      ((∏ j ∈ Finset.range N, (f j).re):ℂ) := by
    calc
      _ = ∏ j ∈ Finset.range N, ((f j).re:ℂ) :=
        Finset.prod_congr rfl (fun j _ => hf j)
      _ = ((∏ j ∈ Finset.range N, (f j).re):ℂ) := by rfl
  have hrewrite :
      (sourceStandardRootOmittedPartialProduct hp hp1 n N ((x:ℂ),ψ)).re =
        a.re * ∏ j ∈ Finset.range N, (f j).re := by
    rw [sourceStandardRootOmittedPartialProduct_eq_paired]
    simp only [if_neg hn]
    change (a * ∏ j ∈ Finset.range N, f j).re = _
    rw [ha,hprod]
    norm_cast
  obtain ⟨r, hr⟩ : ∃ r : ℕ, n.natAbs = r+1 := by
    have hq : n.natAbs ≠ 0 := by simpa using hn
    exact ⟨n.natAbs - 1, by omega⟩
  have haNeg : a.re < 0 := by
    simpa [a,hn] using sourceStandardRootOmittedPrefactor_re_neg_on_nonzeroGap
      hp hp1 ψ hreal hn hx
  have hpair : 0 < (-1:ℝ)^r * ∏ j ∈ Finset.range N, (f j).re := by
    apply signed_prod_range_pos (fun j => (f j).re) r N (by omega)
    · intro j hj
      exact sourceStandardRootOmittedPairedFactor_re_neg_of_lt_natAbs
        hp hp1 ψ hreal n j (by omega) hx
    · intro j hj
      exact sourceStandardRootOmittedPairedFactor_re_pos_of_natAbs_le
        hp hp1 ψ hreal n j (by omega) hx
  rw [hrewrite, hr, pow_succ]
  have hmul : 0 < ((-1:ℝ)^r * ∏ j ∈ Finset.range N, (f j).re) * (-a.re) :=
    mul_pos hpair (neg_pos.mpr haNeg)
  convert hmul using 1; ring

end NLS.ZakharovShabat
