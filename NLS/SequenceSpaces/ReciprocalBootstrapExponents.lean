import NLS.SequenceSpaces.YoungExponents

/-! # Exponent choices for reciprocal-row bootstrapping

A strict gain below the reciprocal Hölder exponent admits a reciprocal
Young kernel with exponent above one. If the product exponent is below
one, it is first embedded into ℓ¹. A finite clipped arithmetic progression
of reciprocal exponents reaches every prescribed exponent above one.
-/
noncomputable section
set_option autoImplicit false
open scoped ENNReal
namespace NLS

/-- Every strict reciprocal gain is realized by a quasi-Hölder product,
a Banach embedding and a Young kernel strictly above exponent one. -/
theorem exists_reciprocal_bootstrap_exponents
    {p q t : ℝ≥0∞} (hp0 : 0 < p) (hq0 : 0 < q) (hp : p ≠ ⊤)
    (ht1 : 1 < t) (ht : t ≠ ⊤) (hgain : t⁻¹ < p⁻¹+q⁻¹) :
    ∃ r R v : ℝ≥0∞, 0 < r ∧ 1 ≤ R ∧ R ≠ ⊤ ∧ r ≤ R ∧
      1 < v ∧ v ≠ ⊤ ∧ p.HolderTriple q r ∧ YoungRelation R v t := by
  let r := (p⁻¹+q⁻¹)⁻¹
  have hr0 : 0 < r := ENNReal.inv_pos.mpr
    (ENNReal.add_ne_top.mpr ⟨ENNReal.inv_ne_top.mpr hp0.ne',ENNReal.inv_ne_top.mpr hq0.ne'⟩)
  have hr : r ≠ ⊤ := ENNReal.inv_ne_top.mpr
    (ne_of_gt ((ENNReal.inv_pos.mpr hp).trans_le (le_self_add : p⁻¹ ≤ p⁻¹+q⁻¹)))
  have hH : p.HolderTriple q r := ENNReal.HolderTriple.of p q
  have hri : r⁻¹ = p⁻¹+q⁻¹ := inv_inv _
  by_cases hr1 : r ≤ 1
  · refine ⟨r,1,t,hr0,le_rfl,by simp,hr1,ht1,ht,hH,?_⟩
    simp only [YoungRelation,inv_one,add_comm]
  · have hr1' : 1 < r := lt_of_not_ge hr1
    have hri1 : r⁻¹ < 1 := ENNReal.inv_lt_one.mpr hr1'
    have hle : r⁻¹ ≤ 1+t⁻¹ := hri1.le.trans le_self_add
    let d := 1+t⁻¹-r⁻¹
    have hd0 : 0 < d := tsub_pos_iff_lt.mpr (hri1.trans_le le_self_add)
    have hd1 : d < 1 := by
      apply ENNReal.sub_lt_of_lt_add hle
      have ht : t⁻¹ < r⁻¹ := hgain.trans_eq hri.symm
      exact ENNReal.add_lt_add_left (by simp) ht
    refine ⟨r,r,d⁻¹,hr0,hr1'.le,hr,le_rfl,
      ENNReal.one_lt_inv.mpr hd1,ENNReal.inv_ne_top.mpr hd0.ne',hH,?_⟩
    change 1+t⁻¹ = r⁻¹+(d⁻¹)⁻¹
    simpa only [d,r,inv_inv] using (add_tsub_cancel_of_le hle).symm

/-- Repeated positive increments, clipped at the target, reach that target
in finitely many steps. This is the termination argument for exponent improvement. -/
theorem mem_of_clipped_increment {S : Set ℝ} (a b d : ℝ) (hab : a ≤ b) (hd : 0 < d)
    (ha : a ∈ S) (hstep : ∀ x ∈ S, a ≤ x → x < b → min b (x+d) ∈ S) : b ∈ S := by
  obtain ⟨N,hN⟩ := exists_nat_gt ((b-a)/d)
  have hreach : b ≤ a+(N:ℝ)*d := by
    have h := (div_lt_iff₀ hd).mp hN
    linarith
  have hind (n : ℕ) : min b (a+(n:ℝ)*d) ∈ S := by
    induction n with
    | zero => simpa only [Nat.cast_zero,zero_mul,add_zero,min_eq_right hab] using ha
    | succ n ih =>
      by_cases hn : b ≤ a+(n:ℝ)*d
      · have hb : b ∈ S := by simpa only [min_eq_left hn] using ih
        have hs : b ≤ a+((n+1:ℕ):ℝ)*d := by push_cast; nlinarith
        simpa only [min_eq_left hs] using hb
      · have hn' : a+(n:ℝ)*d < b := lt_of_not_ge hn
        have hx : a+(n:ℝ)*d ∈ S := by simpa only [min_eq_right hn'.le] using ih
        have h := hstep _ hx (by nlinarith [(Nat.cast_nonneg n : (0:ℝ)≤n)]) hn'
        convert h using 1
        congr 1
        push_cast
        ring
  simpa only [min_eq_left hreach] using hind N

end NLS
