import NLS.SequenceSpaces.PuncturedLattice
import NLS.SequenceSpaces.UniformHolderTails
import NLS.SequenceSpaces.ConvolutionMajorants
import NLS.SequenceSpaces.FiniteExponentTail

/-! # Uniform decay of reciprocal rows near a summable reference sequence -/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS

/-- Separate a reciprocal row into an ℓ² perturbation and an ℓ¹ reference row. -/
theorem reciprocal_row_le_perturbation_convolution (a a₀ : Coeff 2) (b : Coeff 1)
    (hb : ∀ m : ℤ, a₀ m = b m) (n : ℤ) (s : Finset ℤ) (hs : ∀ m ∈ s, m ≠ n) :
    (∑ m ∈ s, ‖a m‖/|((m-n:ℤ):ℝ)|) ≤
      ‖a-a₀‖*‖Coeff.puncturedLattice 2 (by norm_num)‖+
      ‖Coeff.convolution (Coeff.magnitude (Coeff.puncturedLattice 2 (by norm_num)))
        (Coeff.magnitude b) n‖ := by
  let k := Coeff.puncturedLattice 2 (by norm_num)
  have hk (m : ℤ) (hm : m ≠ n) : ‖k (n-m)‖ = |((m-n:ℤ):ℝ)|⁻¹ := by
    simp only [k,Coeff.puncturedLattice_apply,if_neg (sub_ne_zero.mpr hm.symm),
      norm_inv,Complex.norm_intCast]
    rw [show n-m = -(m-n) by ring,Int.cast_neg,abs_neg]
  have hsum : Summable (fun m : ℤ => ‖k (n-m)‖*‖b m‖) := by
    apply (((lp.memℓp b).norm.summable_of_one).mul_left ‖k‖).of_nonneg_of_le
    · intro m; positivity
    · intro m
      exact mul_le_mul_of_nonneg_right (lp.norm_apply_le_norm (by norm_num) k (n-m)) (norm_nonneg _)
  have hbase : (∑ m ∈ s, ‖a₀ m‖/|((m-n:ℤ):ℝ)|) ≤
      ‖Coeff.convolution (Coeff.magnitude k) (Coeff.magnitude b) n‖ := by
    rw [Coeff.norm_magnitude_convolution_apply]
    have h := hsum.sum_le_tsum s (fun m _ => by positivity)
    calc
      _ = ∑ m ∈ s, ‖k (n-m)‖*‖b m‖ := by
        apply Finset.sum_congr rfl
        intro m hm
        rw [hb m,hk m (hs m hm),div_eq_mul_inv,mul_comm]
      _ ≤ _ := h
  have hdiff : (∑ m ∈ s, ‖(a-a₀) m‖/|((m-n:ℤ):ℝ)|) ≤ ‖a-a₀‖*‖k‖ := by
    have h := Coeff.sum_norm_holderProduct_le (a-a₀) (Coeff.shift n k) s
    rw [Coeff.norm_shift] at h
    calc
      _ = ∑ m ∈ s, ‖(a-a₀) m*Coeff.shift n k m‖ := by
        apply Finset.sum_congr rfl
        intro m hm
        simp only [norm_mul,Coeff.shift_apply,k,Coeff.puncturedLattice_apply,
          if_neg (sub_ne_zero.mpr (hs m hm)),norm_inv,Complex.norm_intCast,div_eq_mul_inv]
      _ ≤ _ := h
  have hsplit : (∑ m ∈ s, ‖a m‖/|((m-n:ℤ):ℝ)|) ≤
      (∑ m ∈ s, ‖(a-a₀) m‖/|((m-n:ℤ):ℝ)|)+
      (∑ m ∈ s, ‖a₀ m‖/|((m-n:ℤ):ℝ)|) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro m _
    have h := norm_add_le ((a-a₀) m) (a₀ m)
    change ‖(a m-a₀ m)+a₀ m‖ ≤ _ at h
    rw [sub_add_cancel] at h
    simpa only [add_div] using div_le_div_of_nonneg_right h (abs_nonneg (((m-n:ℤ):ℝ)))
  exact hsplit.trans (add_le_add hdiff hbase)

/-- Norm continuity at an ℓ¹ reference makes all distant finite reciprocal rows small
on one open neighborhood, uniformly in the finite summation set. -/
theorem exists_uniform_reciprocal_rows_of_continuousAt {X : Type*} [TopologicalSpace X]
    (a : X → Coeff 2) (x : X) (ha : ContinuousAt a x) (b : Coeff 1)
    (hb : ∀ m : ℤ, a x m = b m) (ε : ℝ) (hε : 0 < ε) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ ∃ K : ℕ,
      ∀ y ∈ U, ∀ n : ℤ, K ≤ n.natAbs → ∀ s : Finset ℤ,
        (∀ m ∈ s, m ≠ n) → (∑ m ∈ s, ‖a y m‖/|((m-n:ℤ):ℝ)|) ≤ ε := by
  let k := Coeff.puncturedLattice 2 (by norm_num)
  let B := Coeff.convolution (Coeff.magnitude k) (Coeff.magnitude b)
  let δ := ε/(2*(‖k‖+1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hsmall : ∀ᶠ y in 𝓝 x, ‖a y-a x‖ < δ :=
    (ha.sub continuousAt_const).norm.eventually (gt_mem_nhds (by simpa using hδ))
  obtain ⟨U,hUsub,hU,hxU⟩ := mem_nhds_iff.mp hsmall
  obtain ⟨K,hK⟩ := Coeff.exists_natAbs_norm_lt (by norm_num : 0 < (2:ℝ≥0∞).toReal) B
    (show 0 < ε/2 by positivity)
  refine ⟨U,hU,hxU,K,?_⟩
  intro y hy n hn s hs
  have h := reciprocal_row_le_perturbation_convolution (a y) (a x) b hb n s hs
  have hd := mul_le_mul_of_nonneg_right (hUsub hy).le (norm_nonneg k)
  have he : δ*(2*(‖k‖+1)) = ε := div_mul_cancel₀ _ (by positivity)
  have ht := hK n hn
  change (∑ m ∈ s, ‖a y m‖/|((m-n:ℤ):ℝ)|) ≤ ‖a y-a x‖*‖k‖+‖B n‖ at h
  nlinarith

end NLS
