import NLS.Dynamics.HamiltonianPhaseFlow
import NLS.SequenceSpaces.PairNorm

/-! # Exact phase-increment estimates in the finite-p pair norm

The physical phases have a common absolute time-increment factor. A finite
head keeps that factor exactly, while the complementary tail has coefficient
2^p. The pair estimate uses the sum of both component energies, and gives
the two-epsilon bound used in Section 22.
-/
noncomputable section
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The scalar time increment is controlled by the actual time difference. -/
theorem norm_phaseFlow_sub_apply (ω : ℤ → ℝ) (t s : ℝ) (a : Coeff p) (n : ℤ) :
    ‖phaseFlow ω t a n - phaseFlow ω s a n‖ =
      ‖Complex.exp ((((t-s)*ω n : ℝ) : ℂ)*Complex.I)-1‖*‖a n‖ := by
  have he : Complex.exp (((t*ω n : ℝ) : ℂ)*Complex.I) =
      Complex.exp (((s*ω n : ℝ) : ℂ)*Complex.I)*
        Complex.exp ((((t-s)*ω n : ℝ) : ℂ)*Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [phaseFlow_apply,phaseFlow_apply,he]
  calc
    _ = ‖Complex.exp (((s*ω n : ℝ) : ℂ)*Complex.I)*
          ((Complex.exp ((((t-s)*ω n : ℝ) : ℂ)*Complex.I)-1)*a n)‖ := by
      congr 1
      ring
    _ = _ := by
      rw [norm_mul,Complex.norm_exp_ofReal_mul_I,one_mul,norm_mul]

/-- Every scalar phase difference has the universal amplitude bound. -/
theorem norm_phaseFlow_sub_apply_le (ω : ℤ → ℝ) (t s : ℝ) (a : Coeff p) (n : ℤ) :
    ‖phaseFlow ω t a n - phaseFlow ω s a n‖ ≤ 2*‖a n‖ := by
  rw [norm_phaseFlow_sub_apply]
  have he : ‖Complex.exp ((((t-s)*ω n : ℝ) : ℂ)*Complex.I)-1‖ ≤ 2 := by
    simpa only [Complex.norm_exp_ofReal_mul_I,norm_one,one_add_one_eq_two] using
      norm_sub_le (Complex.exp ((((t-s)*ω n : ℝ) : ℂ)*Complex.I)) (1 : ℂ)
  exact mul_le_mul_of_nonneg_right he (norm_nonneg _)

/-- A finite head retains the exact phase increment; the complementary tail
has the universal factor two raised to the sequence exponent. -/
theorem norm_phaseFlow_sub_rpow_le (hp : p ≠ ⊤)
    (ω : ℤ → ℝ) (t s : ℝ) (a : Coeff p) (S : Finset ℤ) :
    ‖phaseFlow ω t a - phaseFlow ω s a‖ ^ p.toReal ≤
      (∑ n ∈ S, ‖Complex.exp ((((t-s)*ω n : ℝ) : ℂ)*Complex.I)-1‖ ^ p.toReal *
        ‖a n‖ ^ p.toReal) +
      (2 : ℝ) ^ p.toReal * ∑' n : {n : ℤ // n ∉ S}, ‖a n.val‖ ^ p.toReal := by
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos
    (ne_of_gt (zero_lt_one.trans_le (show 1 ≤ p from Fact.out))) hp
  let g : Coeff p := phaseFlow ω t a - phaseFlow ω s a
  have hg := g.property.summable hp0
  have ha := a.property.summable hp0
  have hb (n : ℤ) : ‖g n‖ ^ p.toReal ≤ (2 : ℝ) ^ p.toReal * ‖a n‖ ^ p.toReal := by
    rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (norm_nonneg _)]
    exact Real.rpow_le_rpow (norm_nonneg _) (norm_phaseFlow_sub_apply_le ω t s a n) hp0.le
  change ‖g‖ ^ p.toReal ≤ _
  rw [lp.norm_rpow_eq_tsum hp0, ← hg.sum_add_tsum_subtype_compl S]
  apply add_le_add
  · apply le_of_eq
    apply Finset.sum_congr rfl
    intro n _
    change ‖phaseFlow ω t a n - phaseFlow ω s a n‖ ^ p.toReal = _
    rw [norm_phaseFlow_sub_apply,Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
  · calc
      _ ≤ ∑' n : {n : ℤ // n ∉ S}, (2 : ℝ) ^ p.toReal * ‖a n.val‖ ^ p.toReal :=
        (hg.subtype (fun n => n ∉ S)).tsum_le_tsum (fun n => hb n.val)
          ((ha.subtype (fun n => n ∉ S)).mul_left ((2 : ℝ) ^ p.toReal))
      _ = _ := by rw [tsum_mul_left]

end NLS.Coeff

namespace NLS.Birkhoff
open scoped ComplexConjugate
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Reversing the phase orientation leaves the increment norm unchanged. -/
theorem norm_phase_increment_neg (x : ℝ) :
    ‖Complex.exp ((-x : ℂ)*Complex.I)-1‖ =
      ‖Complex.exp ((x : ℂ)*Complex.I)-1‖ := by
  have he : Complex.exp ((-x : ℂ)*Complex.I) =
      conj (Complex.exp ((x : ℂ)*Complex.I)) := by
    rw [← Complex.exp_conj]
    congr 1
    simp
  calc
    _ = ‖conj (Complex.exp ((x : ℂ)*Complex.I)-1)‖ := by rw [map_sub,map_one,he]
    _ = _ := Complex.norm_conj _

/-- The two physical coordinates have the same absolute time-increment factor. -/
theorem norm_hamiltonianPhaseFlow_sub_apply (ω : ℤ → ℝ) (t s : ℝ)
    (z : Coeff p × Coeff p) (n : ℤ) :
    ‖(hamiltonianPhaseFlow ω t z).1 n-(hamiltonianPhaseFlow ω s z).1 n‖ =
      ‖Complex.exp ((((t-s)*ω n : ℝ) : ℂ)*Complex.I)-1‖*‖z.1 n‖ ∧
    ‖(hamiltonianPhaseFlow ω t z).2 n-(hamiltonianPhaseFlow ω s z).2 n‖ =
      ‖Complex.exp ((((t-s)*ω n : ℝ) : ℂ)*Complex.I)-1‖*‖z.2 n‖ := by
  constructor
  · change ‖Coeff.phaseFlow ω (-t) z.1 n-Coeff.phaseFlow ω (-s) z.1 n‖ = _
    rw [Coeff.norm_phaseFlow_sub_apply]
    have he : (-t-(-s))*ω n = -((t-s)*ω n) := by ring
    rw [he,Complex.ofReal_neg,norm_phase_increment_neg]
  · change ‖Coeff.phaseFlow ω (-(-t)) z.2 n-Coeff.phaseFlow ω (-(-s)) z.2 n‖ = _
    rw [neg_neg,neg_neg,Coeff.norm_phaseFlow_sub_apply]

/-- The displayed Section 22 estimate in the component-sum pair norm,
with both physical phase signs and any finite head of signed indices. -/
theorem norm_hamiltonianPhaseFlow_sub_rpow_le (hp : p ≠ ⊤)
    (ω : ℤ → ℝ) (t s : ℝ) (z : Coeff p × Coeff p) (S : Finset ℤ) :
    ‖(CoeffPair.toMax p).symm (hamiltonianPhaseFlow ω t z-hamiltonianPhaseFlow ω s z)‖ ^ p.toReal ≤
      (∑ n ∈ S, ‖Complex.exp ((((t-s)*ω n : ℝ) : ℂ)*Complex.I)-1‖ ^ p.toReal *
        (‖z.1 n‖ ^ p.toReal+‖z.2 n‖ ^ p.toReal)) +
      (2 : ℝ) ^ p.toReal * ∑' n : {n : ℤ // n ∉ S},
        (‖z.1 n.val‖ ^ p.toReal+‖z.2 n.val‖ ^ p.toReal) := by
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos
    (ne_of_gt (zero_lt_one.trans_le (show 1 ≤ p from Fact.out))) hp
  have h₁ := Coeff.norm_phaseFlow_sub_rpow_le hp ω (-t) (-s) z.1 S
  have h₂ := Coeff.norm_phaseFlow_sub_rpow_le hp ω t s z.2 S
  have hn (n : ℤ) : ‖Complex.exp ((((-t-(-s))*ω n : ℝ) : ℂ)*Complex.I)-1‖ =
      ‖Complex.exp ((((t-s)*ω n : ℝ) : ℂ)*Complex.I)-1‖ := by
    have he : (-t-(-s))*ω n = -((t-s)*ω n) := by ring
    rw [he,Complex.ofReal_neg,norm_phase_increment_neg]
  simp_rw [hn] at h₁
  rw [norm_withLp_prod_rpow hp]
  change ‖Coeff.phaseFlow ω (-t) z.1-Coeff.phaseFlow ω (-s) z.1‖ ^ p.toReal +
    ‖Coeff.phaseFlow ω (-(-t)) z.2-Coeff.phaseFlow ω (-(-s)) z.2‖ ^ p.toReal ≤ _
  rw [neg_neg,neg_neg]
  have ha : Summable (fun n : {n : ℤ // n ∉ S} => ‖z.1 n.val‖ ^ p.toReal) :=
    (z.1.property.summable hp0).subtype (fun n => n ∉ S)
  have hb : Summable (fun n : {n : ℤ // n ∉ S} => ‖z.2 n.val‖ ^ p.toReal) :=
    (z.2.property.summable hp0).subtype (fun n => n ∉ S)
  rw [ha.tsum_add hb]
  simp only [mul_add,Finset.sum_add_distrib]
  linarith

/-- The source's two small-energy conditions give the stated two-epsilon bound. -/
theorem norm_hamiltonianPhaseFlow_sub_le_of_head_tail (hp : p ≠ ⊤)
    (ω : ℤ → ℝ) (t s : ℝ) (z : Coeff p × Coeff p) (S : Finset ℤ)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hhead : (∑ n ∈ S, ‖Complex.exp ((((t-s)*ω n : ℝ) : ℂ)*Complex.I)-1‖ ^ p.toReal *
      (‖z.1 n‖ ^ p.toReal+‖z.2 n‖ ^ p.toReal)) ≤ ε ^ p.toReal)
    (htail : (2 : ℝ) ^ p.toReal * ∑' n : {n : ℤ // n ∉ S},
      (‖z.1 n.val‖ ^ p.toReal+‖z.2 n.val‖ ^ p.toReal) ≤ ε ^ p.toReal) :
    ‖(CoeffPair.toMax p).symm (hamiltonianPhaseFlow ω t z-hamiltonianPhaseFlow ω s z)‖ ≤ 2*ε := by
  have hp1 : 1 ≤ p.toReal := by
    simpa only [ENNReal.toReal_one] using
      (ENNReal.toReal_le_toReal ENNReal.one_ne_top hp).mpr (show 1 ≤ p from Fact.out)
  have hp0 : 0 < p.toReal := zero_lt_one.trans_le hp1
  have htwo : (2 : ℝ) ≤ (2 : ℝ) ^ p.toReal := by
    calc
      _ = (2 : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) hp1
  apply (Real.rpow_le_rpow_iff (norm_nonneg _) (mul_nonneg (by norm_num) hε) hp0).mp
  calc
    _ ≤ _ := norm_hamiltonianPhaseFlow_sub_rpow_le hp ω t s z S
    _ ≤ ε ^ p.toReal+ε ^ p.toReal := add_le_add hhead htail
    _ = 2*ε ^ p.toReal := by ring
    _ ≤ (2 : ℝ) ^ p.toReal*ε ^ p.toReal :=
      mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hε _)
    _ = (2*ε) ^ p.toReal := (Real.mul_rpow (by norm_num) hε).symm

end NLS.Birkhoff
