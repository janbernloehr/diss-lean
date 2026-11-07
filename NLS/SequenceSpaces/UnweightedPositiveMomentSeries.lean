import NLS.SequenceSpaces.BoundedPositiveMomentSeries
import NLS.SequenceSpaces.WeightedRawDomination
import NLS.SequenceSpaces.PositiveScalarExtension

/-! An input derivative upgrades the entire positive moment series to
unweighted lp for every p > 1, by the reciprocal convolution majorant. -/
noncomputable section
open Set Complex NLS.LpSequence
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

private theorem exists_of_norm_le (a : Coeff p) (f : ℤ → ℂ)
    (C : ℝ) (hC : 0 ≤ C) (hf : ∀ k, ‖f k‖ ≤ C*‖a k‖) :
    ∃ b : Coeff p, (∀ k, b k = f k) ∧ ‖b‖ ≤ C*‖a‖ := by
  have hmem : Memℓp f p := ((lp.memℓp a).norm.const_mul C).mono (by
    intro k
    simpa only [norm_mul,Real.norm_eq_abs,abs_of_nonneg hC] using hf k)
  let b : Coeff p := ⟨f,hmem⟩
  have h : ‖b‖ ≤ ‖(C:ℂ) • a‖ := by
    apply lp.norm_mono (ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out))
    intro k
    simpa only [lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,norm_mul,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonneg hC] using hf k
  exact ⟨b,fun _ => rfl,by simpa only [norm_smul,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg hC] using h⟩

theorem exists_unweighted_positive_moment_series (hp : 1 < p)
    (H : Coeff 2) (g : ℕ+ → ℝ) (hg : ∀ m, 0 ≤ g m)
    (hH : ∀ m : ℕ+, (1+(m:ℝ))*g m ≤ ‖H ((m:ℕ):ℤ)‖)
    (u : ℕ+ → ℕ+ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hu : ∀ n m : ℕ+, ‖u n m‖ ≤ B*(g m)^2*
      (if m=n then 1 else 1/|((n:ℕ):ℝ)-(m:ℕ)|+1/((n:ℕ)+(m:ℕ):ℝ))) :
    ∃ b : Coeff p,
      (∀ k, b k = positiveScalarExtension (fun n => ∑' m : ℕ+, ((m:ℕ):ℂ)*u n m) k) ∧
      ‖b‖ ≤ (2*B)*(1+3*‖puncturedLattice p hp‖)*‖H‖^2 := by
  let b := squaredGapMagnitude H
  let κ := puncturedLattice p hp
  let j : ℕ+ → ℤ := fun m => ((m:ℕ):ℤ)
  have hj : Function.Injective j := by intro a c h; exact PNat.coe_injective (Int.ofNat.inj h)
  have hb (k : ℤ) : ‖b k‖=‖H k‖^2 := by
    rw [show b k=(‖H k‖^2:ℝ) from squaredGapMagnitude_apply H k,
      Complex.norm_real,Real.norm_of_nonneg (sq_nonneg _)]
  have hw (m : ℕ+) : (m:ℝ)*(g m)^2 ≤ ‖b (j m)‖ := by
    rw [hb]
    calc
      _ ≤ (1+(m:ℝ))^2*(g m)^2 := mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg (m:ℝ)]) (sq_nonneg _)
      _ = ((1+(m:ℝ))*g m)^2 := by ring
      _ ≤ _ := pow_le_pow_left₀ (mul_nonneg (by positivity) (hg m)) (hH m) 2
  have hbZ : Summable (fun k : ℤ => ‖b k‖) := (lp.memℓp b).norm.summable_of_one
  have hrow (n : ℕ+) : ‖∑' m : ℕ+, ((m:ℕ):ℂ)*u n m‖ ≤
      (2*B)*‖squaredGapMomentMajorant hp H (j n)‖ := by
    have hs := (norm_positive_moment_series_le_of_Hilbert_majorant H g hg hH u B hB hu n).1
    have hcZ : Summable (fun k : ℤ => ‖κ (j n-k)‖*‖b k‖) := by
      apply (hbZ.mul_left ‖κ‖).of_nonneg_of_le (fun _ => by positivity)
      intro k
      exact mul_le_mul_of_nonneg_right (lp.norm_apply_le_norm (ne_of_gt (zero_lt_one.trans hp)) κ _) (norm_nonneg _)
    have hcP : Summable (fun m : ℕ+ => ‖κ (j n-j m)‖*‖b (j m)‖) := hcZ.comp_injective hj
    let d : ℕ+ → ℝ := fun m => if m=n then ‖b (j n)‖ else 0
    have hd : Summable d := summable_of_ne_finset_zero (s := {n}) (by
      intro m hm
      have hmn : m ≠ n := by simpa only [Finset.mem_singleton] using hm
      exact if_neg hmn)
    have hdSum : (∑' m : ℕ+, d m)=‖b (j n)‖ := by
      rw [tsum_eq_single n (by intro m hm; simp [d,hm])]
      simp only [d,if_pos rfl]
    have hpoint (m : ℕ+) : ‖((m:ℕ):ℂ)*u n m‖ ≤
        (2*B)*(d m+‖κ (j n-j m)‖*‖b (j m)‖) := by
      rw [norm_mul,Complex.norm_natCast]
      by_cases hmn : m=n
      · subst m
        have h := hu n n
        rw [if_pos rfl,mul_one] at h
        have hv := (mul_le_mul_of_nonneg_left h (by positivity : (0:ℝ) ≤ (n:ℝ))).trans
          (by calc
            (n:ℝ)*(B*(g n)^2) = B*((n:ℝ)*(g n)^2) := by ring
            _ ≤ B*‖b (j n)‖ := mul_le_mul_of_nonneg_left (hw n) hB)
        rw [show d n=‖b (j n)‖ from if_pos rfl]
        nlinarith [mul_nonneg hB (norm_nonneg (b (j n))),
          mul_nonneg hB (mul_nonneg (norm_nonneg (κ (j n-j n))) (norm_nonneg (b (j n))))]
      · have hnm : ((n:ℕ):ℝ) ≠ (m:ℕ) := by
          intro he
          exact hmn (PNat.coe_injective (by exact_mod_cast he.symm))
        have hdiv : 1/((n:ℕ)+(m:ℕ):ℝ) ≤ 1/|((n:ℕ):ℝ)-(m:ℕ)| := by
          apply one_div_le_one_div_of_le (abs_pos.mpr (sub_ne_zero.mpr hnm))
          exact abs_le.mpr ⟨by linarith [show (0:ℝ) ≤ (n:ℕ) by positivity],
            by linarith [show (0:ℝ) ≤ (m:ℕ) by positivity]⟩
        have hk := norm_puncturedLattice_positive_difference hp n m hmn
        rw [show d m=0 from if_neg hmn,zero_add,hk]
        have h := hu n m
        rw [if_neg hmn] at h
        calc
          _ ≤ (m:ℝ)*(B*(g m)^2*(2/|((n:ℕ):ℝ)-(m:ℕ)|)) :=
            mul_le_mul_of_nonneg_left (h.trans (mul_le_mul_of_nonneg_left (by calc
              1/|((n:ℕ):ℝ)-(m:ℕ)|+1/((n:ℕ)+(m:ℕ):ℝ) ≤
                1/|((n:ℕ):ℝ)-(m:ℕ)|+1/|((n:ℕ):ℝ)-(m:ℕ)| := add_le_add le_rfl hdiv
              _ = 2/|((n:ℕ):ℝ)-(m:ℕ)| := by ring) (by positivity))) (by positivity)
          _ = (2*B)*((m:ℝ)*(g m)^2)*(1/|((n:ℕ):ℝ)-(m:ℕ)|) := by ring
          _ ≤ (2*B)*‖b (j m)‖*(1/|((n:ℕ):ℝ)-(m:ℕ)|) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hw m) (by positivity)) (by positivity)
          _ = _ := by ring
    have hcSum : (∑' m : ℕ+, ‖κ (j n-j m)‖*‖b (j m)‖) ≤
        ‖convolution (magnitude κ) (magnitude b) (j n)‖ := by
      rw [norm_magnitude_convolution_apply]
      exact tsum_comp_le_tsum_of_inj hcZ (fun _ => by positivity) hj
    calc
      _ ≤ ∑' m : ℕ+, ‖((m:ℕ):ℂ)*u n m‖ := norm_tsum_le_tsum_norm hs
      _ ≤ ∑' m : ℕ+, (2*B)*(d m+‖κ (j n-j m)‖*‖b (j m)‖) :=
        hs.tsum_le_tsum hpoint ((hd.add hcP).mul_left (2*B))
      _ = (2*B)*(‖b (j n)‖+∑' m : ℕ+, ‖κ (j n-j m)‖*‖b (j m)‖) := by
        rw [tsum_mul_left,hd.tsum_add hcP,hdSum]
      _ ≤ (2*B)*(‖b (j n)‖+‖convolution (magnitude κ) (magnitude b) (j n)‖) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl hcSum) (by positivity)
      _ ≤ _ := by
        rw [norm_squaredGapMomentMajorant_apply]
        exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity)) (by positivity)
  obtain ⟨a,ha,hn⟩ := exists_of_norm_le (squaredGapMomentMajorant hp H)
    (positiveScalarExtension (fun n => ∑' m : ℕ+, ((m:ℕ):ℂ)*u n m)) (2*B) (by positivity) (by
      intro k
      by_cases hk : k ∈ range positiveEmbedding
      · obtain ⟨n,rfl⟩ := hk
        change ‖positiveScalarExtension _ ((n:ℕ):ℤ)‖ ≤ _
        rw [positiveScalarExtension_apply]
        exact hrow n
      · rw [positiveScalarExtension_zero_of_not_mem_range _ k hk,norm_zero]
        positivity)
  refine ⟨a,ha,hn.trans ?_⟩
  calc
    _ ≤ (2*B)*((1+3*‖puncturedLattice p hp‖)*‖H‖^2) :=
      mul_le_mul_of_nonneg_left (norm_squaredGapMomentMajorant_le hp H) (by positivity)
    _ = _ := by ring
end NLS.Coeff
