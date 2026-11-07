import NLS.SequenceSpaces.UniformShiftedHolderDecay
import NLS.SequenceSpaces.PuncturedLattice
import NLS.SequenceSpaces.HolderEmbedding
import NLS.SequenceSpaces.PositiveScalarExtension

/-! A fixed positive power of gap-index decay forces uniform decay of
the complete reciprocal moment rows. The diagonal term is retained. -/
noncomputable section
open Set Filter Topology NLS.LpSequence
open scoped ENNReal
namespace NLS.Coeff

def reciprocalMomentLattice (q : ℝ≥0∞) [Fact (1 ≤ q)] (hq : 1 < q) : Coeff q :=
  puncturedLattice q hq+lp.single q 0 1

theorem norm_reciprocalMomentLattice (q : ℝ≥0∞) [Fact (1 ≤ q)] (hq : 1 < q) (k : ℤ) :
    ‖reciprocalMomentLattice q hq k‖=if k=0 then 1 else 1/|(k:ℝ)| := by
  by_cases hk : k=0
  · subst k
    simp [reciprocalMomentLattice,puncturedLattice_apply,lp.single_apply]
  · simp only [reciprocalMomentLattice,lp.coeFn_add,Pi.add_apply,puncturedLattice_apply,
      if_neg hk,lp.single_apply,Pi.single_eq_of_ne hk,add_zero,norm_inv,Complex.norm_intCast,one_div]

def positiveMomentKernel (n m : ℕ+) : ℝ :=
  if m=n then 1 else 1/|((n:ℕ):ℝ)-(m:ℕ)|+1/((n:ℕ)+(m:ℕ):ℝ)

theorem positiveMomentKernel_le_shifted (q : ℝ≥0∞) [Fact (1 ≤ q)] (hq : 1 < q) (n m : ℕ+) :
    positiveMomentKernel n m ≤
      ‖shift (n:ℤ) (reciprocalMomentLattice q hq) (m:ℤ)‖+
        ‖shift (-(n:ℤ)) (reciprocalMomentLattice q hq) (m:ℤ)‖ := by
  rw [shift_apply,shift_apply,norm_reciprocalMomentLattice,norm_reciprocalMomentLattice]
  have hsum : (m:ℤ)- -(n:ℤ)≠0 := by have := m.pos; have := n.pos; omega
  rw [if_neg hsum]
  by_cases hmn : m=n
  · subst m
    simp only [positiveMomentKernel,ite_true,sub_self]
    exact le_add_of_nonneg_right (by positivity)
  · have hdiff : (m:ℤ)-(n:ℤ)≠0 := by
      intro he
      exact hmn (Subtype.ext (Int.ofNat.inj (sub_eq_zero.mp he)))
    rw [positiveMomentKernel,if_neg hmn,if_neg hdiff]
    simp only [Int.cast_sub,Int.cast_add,Int.cast_natCast,sub_neg_eq_add]
    rw [abs_of_nonneg (by positivity : (0:ℝ)≤(m:ℕ)+(n:ℕ)),abs_sub_comm]
    exact le_of_eq (by ring)

/-- One vanishing bound works for EVERY complex row with the prescribed
positive power and reciprocal-kernel majorant. In particular, no uniform
convergence hypothesis for the varying rows is needed. -/
theorem exists_uniform_polynomial_moment_row_decay (δ : ℝ) (hδ : 0 < δ)
    (C : ℝ) (hC : 0 ≤ C) :
    ∃ B : ℤ → ℝ, (∀ n, 0 ≤ B n) ∧ Tendsto B cofinite (𝓝 0) ∧
      ∀ u : ℕ+ → ℂ, ∀ n : ℕ+,
        (∀ m, ‖u m‖ ≤ C/(1+(m:ℝ))^δ*positiveMomentKernel n m) →
        Summable (fun m => ‖u m‖) ∧ ‖∑' m, u m‖ ≤ B (n:ℤ) := by
  let t : ℝ := 2/δ+2
  have ht : 1<t := by dsimp only [t]; have hp := div_pos (by norm_num : (0:ℝ)<2) hδ; linarith
  let p : ℝ≥0∞ := ENNReal.ofReal t
  have hp : p≠⊤ := ENNReal.ofReal_ne_top
  have hp1 : 1<p := ENNReal.one_lt_ofReal.mpr ht
  let : Fact (1 ≤ p) := ⟨hp1.le⟩
  have hpr : p.toReal=t := ENNReal.toReal_ofReal (by linarith)
  have hpR : 0<p.toReal := by rw [hpr]; linarith
  have hδp : 1<δ*p.toReal := by
    rw [hpr]
    have he : δ*(2/δ)=2 := mul_div_cancel₀ _ hδ.ne'
    dsimp only [t]
    nlinarith
  have hq1 : 1<p.conjExponent :=
    (ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top
  have hq : p.conjExponent≠⊤ :=
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt p.conjExponent p).mpr hp1).ne
  let : Fact (1 ≤ p.conjExponent) := ⟨hq1.le⟩
  let a : Coeff p := ⟨fun k => (Weight.sobolev δ k:ℂ)⁻¹,Weight.inverse_sobolev_memlp hpR hδp⟩
  let b := reciprocalMomentLattice p.conjExponent hq1
  have ha (m : ℕ+) : ‖a (m:ℤ)‖=1/(1+(m:ℝ))^δ := by
    change ‖(Weight.sobolev δ (m:ℤ):ℂ)⁻¹‖=_
    rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ((Weight.sobolev δ).positive _)]
    simp only [Weight.sobolev_apply,Int.cast_natCast,abs_of_nonneg (by positivity : (0:ℝ)≤m),one_div]
  obtain ⟨B,hB,hlim,hbound⟩ := exists_uniform_two_shift_holder_decay hp hq
    (ENNReal.HolderConjugate.toReal_of_ne_top hp hq) a b C hC
  refine ⟨B,hB,hlim,?_⟩
  intro u n hu
  have hmaj (k : ℤ) : ‖positiveScalarExtension u k‖ ≤
      C*‖a k‖*(‖shift (n:ℤ) b k‖+‖shift (-(n:ℤ)) b k‖) := by
    by_cases hk : k ∈ range positiveEmbedding
    · obtain ⟨m,rfl⟩ := hk
      change ‖positiveScalarExtension u (m:ℤ)‖ ≤
        C*‖a (m:ℤ)‖*(‖shift (n:ℤ) b (m:ℤ)‖+‖shift (-(n:ℤ)) b (m:ℤ)‖)
      rw [positiveScalarExtension_apply]
      apply (hu m).trans
      rw [ha,div_eq_mul_inv,one_div]
      exact mul_le_mul_of_nonneg_left (positiveMomentKernel_le_shifted p.conjExponent hq1 n m) (by positivity)
    · rw [positiveScalarExtension_zero_of_not_mem_range u k hk,norm_zero]
      positivity
  obtain ⟨hs,hb⟩ := hbound (positiveScalarExtension u) (n:ℤ) hmaj
  have hsu := hs.comp_injective positiveEmbedding.injective
  change Summable (fun m : ℕ+ => ‖positiveScalarExtension u (m:ℤ)‖) at hsu
  refine ⟨?_,?_⟩
  · simpa only [Function.comp_def,positiveScalarExtension_apply] using hsu
  · simpa only [tsum_positiveScalarExtension] using hb

end NLS.Coeff
