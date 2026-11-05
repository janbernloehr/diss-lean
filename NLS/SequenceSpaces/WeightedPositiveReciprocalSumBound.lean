import NLS.SequenceSpaces.PositiveReciprocalSumBound

/-! One source index weight transfers to the output of the full
positive reciprocal sum. The translated deleted kernel plus twice
the fixed deleted kernel has a uniform Hilbert norm bound. -/
noncomputable section
open Set NLS.LpSequence
open scoped ENNReal Classical
namespace NLS.Coeff

theorem weighted_positive_reciprocal_kernel_le (n m : ℕ+) (hmn : m ≠ n) :
    (1+(n:ℝ))*(1/|(n:ℝ)-(m:ℝ)|+1/((n:ℝ)+(m:ℝ))) ≤
      (1+(m:ℝ))*(1/|(n:ℝ)-(m:ℝ)|+2/(m:ℝ)) := by
  have hm : (0:ℝ) < (m:ℝ) := by exact_mod_cast m.pos
  have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr m.ne_zero
  have hn : (0:ℝ) < (n:ℝ) := by exact_mod_cast n.pos
  have hne : (n:ℝ) ≠ (m:ℝ) := by exact_mod_cast hmn.symm
  have hd : 0 < |(n:ℝ)-(m:ℝ)| := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hdiff : 1+(n:ℝ) ≤ 1+(m:ℝ)+|(n:ℝ)-(m:ℝ)| := by
    linarith [le_abs_self ((n:ℝ)-(m:ℝ))]
  have hfirst : (1+(n:ℝ))/|(n:ℝ)-(m:ℝ)| ≤ (1+(m:ℝ))/|(n:ℝ)-(m:ℝ)|+1 := by
    apply (div_le_iff₀ hd).mpr
    rw [add_mul,div_mul_cancel₀ _ hd.ne']
    linarith
  have hsecond : (1+(n:ℝ))/((n:ℝ)+(m:ℝ)) ≤ 1 :=
    (div_le_iff₀ (add_pos hn hm)).mpr (by linarith)
  have htwo : 2 ≤ (1+(m:ℝ))*2/(m:ℝ) :=
    (le_div_iff₀ hm).mpr (by nlinarith)
  calc
    _ = (1+(n:ℝ))/|(n:ℝ)-(m:ℝ)|+(1+(n:ℝ))/((n:ℝ)+(m:ℝ)) := by ring
    _ ≤ (1+(m:ℝ))/|(n:ℝ)-(m:ℝ)|+2 := by linarith
    _ ≤ (1+(m:ℝ))/|(n:ℝ)-(m:ℝ)|+(1+(m:ℝ))*2/(m:ℝ) := by linarith
    _ = _ := by ring

theorem weighted_norm_positive_sum_le_of_reciprocal_bound
    (a d : Coeff 2) (g : ℕ+ → ℝ) (hg : ∀ m, 0 ≤ g m)
    (hw : ∀ m : ℕ+, (1+(m:ℝ))*g m ≤ ‖a ((m:ℕ):ℤ)‖+‖d ((m:ℕ):ℤ)‖)
    (n : ℕ+) (u : ℕ+ → ℂ) (hdiag : u n = 0) (C : ℝ) (hC : 0 ≤ C)
    (hu : ∀ m : ℕ+, m ≠ n → ‖u m‖ ≤ C*g m*
      (1/|(n:ℝ)-(m:ℝ)|+1/((n:ℝ)+(m:ℝ)))) :
    Summable (fun m => ‖u m‖) ∧
      (1+(n:ℝ))*(∑' m, ‖u m‖) ≤ C*(‖a‖+‖d‖)*(3*‖puncturedLattice 2 (by norm_num)‖) ∧
      (1+(n:ℝ))*‖∑' m, u m‖ ≤ C*(‖a‖+‖d‖)*(3*‖puncturedLattice 2 (by norm_num)‖) := by
  let κ := puncturedLattice 2 (by norm_num : 1 < (2:ℝ≥0∞))
  let b := shift ((n:ℕ):ℤ) κ
  let B := Coeff.magnitude b+(2:ℂ) • Coeff.magnitude κ
  let v : ℕ+ → ℂ := fun m => ((1+(n:ℝ):ℝ):ℂ)*u m
  have hn : (1:ℝ) ≤ 1+(n:ℝ) := by linarith [show (0:ℝ) ≤ (n:ℝ) by positivity]
  have hv (m : ℕ+) : ‖v m‖ = (1+(n:ℝ))*‖u m‖ := by
    simp only [v,norm_mul,Complex.norm_real,Real.norm_of_nonneg (by positivity : 0 ≤ 1+(n:ℝ))]
  have hBk (k : ℤ) : ‖B k‖ = ‖b k‖+2*‖κ k‖ := by
    change ‖(‖b k‖:ℂ)+2*(‖κ k‖:ℂ)‖ = _
    have he : (‖b k‖:ℂ)+2*(‖κ k‖:ℂ) = ((‖b k‖+2*‖κ k‖:ℝ):ℂ) := by push_cast; rfl
    rw [he,Complex.norm_real,Real.norm_of_nonneg (by positivity)]
  have hB : ‖B‖ ≤ 3*‖κ‖ := by
    apply (norm_add_le _ _).trans_eq
    simp only [norm_smul,Complex.norm_ofNat,Coeff.norm_magnitude,b,norm_shift]
    ring
  have hkernel (m : ℕ+) (hmn : m ≠ n) : ‖B ((m:ℕ):ℤ)‖ =
      1/|(n:ℝ)-(m:ℝ)|+2/(m:ℝ) := by
    rw [hBk]
    have hpos : ((m:ℕ):ℤ) ≠ ((n:ℕ):ℤ) := by exact_mod_cast hmn
    have hm0 : ((m:ℕ):ℤ) ≠ 0 := by exact_mod_cast m.ne_zero
    have hmκ : ‖κ ((m:ℕ):ℤ)‖ = 1/(m:ℝ) := by
      simp only [κ,puncturedLattice_apply,if_neg hm0,Int.cast_natCast,norm_inv,Complex.norm_natCast,one_div]
    rw [hmκ]
    simp only [b,κ,norm_shift_puncturedLattice_apply,if_neg hpos,Int.cast_sub,Int.cast_natCast]
    rw [abs_sub_comm]
    simp only [div_eq_mul_inv,one_mul]
  have hp (m : ℕ+) : ‖v m‖ ≤ C*(‖a ((m:ℕ):ℤ)‖+‖d ((m:ℕ):ℤ)‖)*‖B ((m:ℕ):ℤ)‖ := by
    by_cases hmn : m = n
    · subst m
      rw [hv,hdiag,norm_zero,mul_zero]
      positivity
    · rw [hv,hkernel m hmn]
      calc
        _ ≤ (1+(n:ℝ))*(C*g m*(1/|(n:ℝ)-(m:ℝ)|+1/((n:ℝ)+(m:ℝ)))) :=
          mul_le_mul_of_nonneg_left (hu m hmn) (by positivity)
        _ = C*g m*((1+(n:ℝ))*(1/|(n:ℝ)-(m:ℝ)|+1/((n:ℝ)+(m:ℝ)))) := by ring
        _ ≤ C*g m*((1+(m:ℝ))*(1/|(n:ℝ)-(m:ℝ)|+2/(m:ℝ))) :=
          mul_le_mul_of_nonneg_left (weighted_positive_reciprocal_kernel_le n m hmn) (mul_nonneg hC (hg m))
        _ = C*((1+(m:ℝ))*g m)*(1/|(n:ℝ)-(m:ℝ)|+2/(m:ℝ)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hw m) hC) (by positivity)
  have hpoint (k : ℤ) : ‖positiveScalarExtension v k‖ ≤ C*(‖a k‖+‖d k‖)*‖B k‖ := by
    by_cases hk : k ∈ range positiveEmbedding
    · obtain ⟨m,rfl⟩ := hk
      change ‖positiveScalarExtension v ((m:ℕ):ℤ)‖ ≤ C*(‖a ((m:ℕ):ℤ)‖+‖d ((m:ℕ):ℤ)‖)*‖B ((m:ℕ):ℤ)‖
      rw [positiveScalarExtension_apply]
      exact hp m
    · rw [positiveScalarExtension_zero_of_not_mem_range v k hk,norm_zero]
      positivity
  have hc : (2:ℝ≥0∞).toReal.HolderConjugate (2:ℝ≥0∞).toReal := Real.HolderConjugate.two_two
  obtain ⟨hsZ,hbound⟩ := summable_norm_of_two_holder_bounds hc
    a d B (positiveScalarExtension v) C hC hpoint
  have hsV := hsZ.comp_injective positiveEmbedding.injective
  change Summable (fun m : ℕ+ => ‖positiveScalarExtension v ((m:ℕ):ℤ)‖) at hsV
  simp only [positiveScalarExtension_apply] at hsV
  have hs : Summable (fun m => ‖u m‖) := hsV.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => by
    rw [hv]; nlinarith [norm_nonneg (u m)])
  have he := positiveEmbedding.injective.tsum_eq (f := fun k => ‖positiveScalarExtension v k‖) (by
    intro k hk
    by_contra hn
    exact hk (by
      change ‖positiveScalarExtension v k‖ = 0
      rw [positiveScalarExtension_zero_of_not_mem_range v k hn,norm_zero]))
  change (∑' m : ℕ+, ‖positiveScalarExtension v ((m:ℕ):ℤ)‖) = _ at he
  simp only [positiveScalarExtension_apply] at he
  have htotal : (1+(n:ℝ))*(∑' m, ‖u m‖) ≤ C*(‖a‖+‖d‖)*(3*‖κ‖) := by
    rw [← tsum_mul_left]
    simp_rw [← hv]
    rw [he]
    exact hbound.trans (mul_le_mul_of_nonneg_left hB (mul_nonneg hC (by positivity)))
  exact ⟨hs,htotal,(mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hs) (by positivity)).trans htotal⟩

end NLS.Coeff
