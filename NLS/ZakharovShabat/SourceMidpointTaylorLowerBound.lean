import NLS.ZakharovShabat.SourceRemark10_9LatticeTerm

/-!
# Positive Taylor terms detect actual squared gaps

At real potentials the linear Taylor sum at a free center is nonnegative
real. A small midpoint displacement gives a uniform lower bound for its
neighboring gap contribution. This uses the actual spectral midpoint.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

private theorem real_complex_sq (z : ℂ) (hz : z.im = 0) : z^2 = ((‖z‖^2 : ℝ):ℂ) := by
  rw [Complex.sq_norm,Complex.normSq_apply,hz]
  apply Complex.ext <;> simp only [pow_two,mul_re,mul_im,ofReal_re,ofReal_im,
    hz,mul_zero,zero_mul,add_zero,sub_zero]

/-- The nonnegative Taylor summand at the selected free center. -/
def sourceMidpointTaylorRealTerm (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n m : ℤ) : ℝ :=
  if m = n then 0 else ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖^2 /
    (8*‖sourceStandardRootMidpoint hp hp1 ψ m-(Real.pi : ℂ)*n‖^2)

theorem sourceMidpointTaylorRealTerm_nonneg (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n m : ℤ) : 0 ≤ sourceMidpointTaylorRealTerm hp hp1 ψ n m := by
  unfold sourceMidpointTaylorRealTerm
  split_ifs <;> positivity

theorem sourceMidpointQuotientLinearTerm_eq_realSum
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p ψ)) (n : ℤ) :
    sourceMidpointQuotientLinearTerm hp hp1 ψ n ((Real.pi : ℂ)*n) =
      ((∑' m,sourceMidpointTaylorRealTerm hp hp1 ψ n m : ℝ):ℂ) := by
  rw [sourceMidpointQuotientLinearTerm_eq,Complex.ofReal_tsum]
  apply tsum_congr
  intro m
  by_cases hm : m = n
  · simp [sourceMidpointTaylorRealTerm,hm]
  obtain ⟨hl,hr⟩ := canonicalPeriodicEndpoints_im_eq_zero_of_realType hp hp1 _
    (periodOnePotential_mem ψ) (isRealType_periodOnePotential ψ hreal) m
  have hg : (sourcePeriodicGapDisplacement hp hp1 ψ m).im = 0 := by
    simp only [sourcePeriodicGapDisplacement_apply,canonicalPeriodicGap,sub_im,hl,hr,sub_self]
  have ht : (sourceStandardRootMidpoint hp hp1 ψ m).im = 0 := by
    simp only [sourceStandardRootMidpoint,canonicalPeriodicMidpoint,div_ofNat_im,add_im,
      hl,hr,add_zero,zero_div]
  have hd : (sourceStandardRootMidpoint hp hp1 ψ m-(Real.pi : ℂ)*n).im = 0 := by
    simp only [sub_im,mul_im,ht,ofReal_im,intCast_im,zero_mul,mul_zero,add_zero,sub_zero]
  simp only [if_neg hm,sourceMidpointTaylorRealTerm]
  rw [← sourcePeriodicGapDisplacement_apply]
  change (sourcePeriodicGapDisplacement hp hp1 ψ m)^2 /
    (8*(sourceStandardRootMidpoint hp hp1 ψ m-(Real.pi : ℂ)*n)^2) = _
  simp only [real_complex_sq _ hg,real_complex_sq _ hd,Complex.ofReal_div,
    Complex.ofReal_mul,Complex.ofReal_ofNat]

theorem sourceMidpointTaylorRealTerm_le_row
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    (hsmall : ‖sourcePeriodicMidpointDisplacement hp hp1 ψ‖ ≤ 1) (n m : ℤ) :
    sourceMidpointTaylorRealTerm hp hp1 ψ n m ≤ sourceSquaredGapReciprocalTerm hp hp1 ψ n m/8 := by
  by_cases hm : m = n
  · simp [sourceMidpointTaylorRealTerm,sourceSquaredGapReciprocalTerm,hm]
  have hd : 0 < |((m-n : ℤ) : ℝ)| := abs_pos.mpr (by exact_mod_cast sub_ne_zero.mpr hm)
  have hsep := sourceMidpoint_freeCenter_separation hp hp1 ψ hsmall m n hm
  have hs := pow_le_pow_left₀ hd.le hsep 2
  simp only [sourceMidpointTaylorRealTerm,sourceSquaredGapReciprocalTerm,if_neg hm,
    Real.rpow_neg (abs_nonneg _),Real.rpow_ofNat]
  calc
    _ ≤ ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖^2/(8*|((m-n : ℤ) : ℝ)|^2) :=
      div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by nlinarith)
    _ = _ := by ring

theorem summable_sourceMidpointTaylorRealTerm
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    (hsmall : ‖sourcePeriodicMidpointDisplacement hp hp1 ψ‖ ≤ 1) (n : ℤ) :
    Summable (sourceMidpointTaylorRealTerm hp hp1 ψ n) :=
  Summable.of_nonneg_of_le (sourceMidpointTaylorRealTerm_nonneg hp hp1 ψ n)
    (sourceMidpointTaylorRealTerm_le_row hp hp1 ψ hsmall n)
    ((((exists_sourceSquaredGapPhysicalRows hp hp1 ψ).choose_spec.1 n).1).div_const 8)

/-- The exact Taylor sum controls every neighboring squared gap. -/
theorem squared_sourceGap_le_neighbor_linearTerm
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p ψ))
    (hsmall : ‖sourcePeriodicMidpointDisplacement hp hp1 ψ‖ ≤ 1) (m : ℤ) :
    ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖^2 ≤
      (8*(Real.pi+1)^2)*‖sourceMidpointQuotientLinearTerm hp hp1 ψ (m+1) ((Real.pi : ℂ)*((m+1 : ℤ) : ℂ))‖ := by
  have hcoord := (lp.norm_apply_le_norm (zero_lt_one.trans hp1).ne'
    (sourcePeriodicMidpointDisplacement hp hp1 ψ) m).trans hsmall
  have hdisp : ‖sourceStandardRootMidpoint hp hp1 ψ m-(Real.pi : ℂ)*m‖ ≤ 1 := by
    simpa only [sourcePeriodicMidpointDisplacement_apply,sourceStandardRootMidpoint] using hcoord
  have htri := norm_add_le (sourceStandardRootMidpoint hp hp1 ψ m-(Real.pi : ℂ)*m)
    ((Real.pi : ℂ)*m-(Real.pi : ℂ)*((m+1 : ℤ) : ℂ))
  rw [sub_add_sub_cancel] at htri
  have hfree : ‖(Real.pi : ℂ)*m-(Real.pi : ℂ)*((m+1 : ℤ) : ℂ)‖ = Real.pi := by
    convert norm_free_center_sub m (m+1) using 1
    norm_num
  rw [hfree] at htri
  have hb : ‖sourceStandardRootMidpoint hp hp1 ψ m-(Real.pi : ℂ)*((m+1 : ℤ) : ℂ)‖ ≤ Real.pi+1 := by linarith
  have hsep := sourceMidpoint_freeCenter_separation hp hp1 ψ hsmall m (m+1) (by omega)
  have hpos : 0 < ‖sourceStandardRootMidpoint hp hp1 ψ m-(Real.pi : ℂ)*((m+1 : ℤ) : ℂ)‖ := by
    have hd : |((m-(m+1) : ℤ) : ℝ)| = 1 := by norm_num
    rw [hd] at hsep
    linarith
  have hs := summable_sourceMidpointTaylorRealTerm hp hp1 ψ hsmall (m+1)
  have hle := hs.le_tsum m (fun j _ => sourceMidpointTaylorRealTerm_nonneg hp hp1 ψ (m+1) j)
  have hn : 0 ≤ ∑' j,sourceMidpointTaylorRealTerm hp hp1 ψ (m+1) j :=
    tsum_nonneg (sourceMidpointTaylorRealTerm_nonneg hp hp1 ψ (m+1))
  rw [sourceMidpointQuotientLinearTerm_eq_realSum hp hp1 ψ hreal,Complex.norm_real,
    Real.norm_of_nonneg hn]
  have hsquare := pow_le_pow_left₀ (norm_nonneg _) hb 2
  have hterm : sourceMidpointTaylorRealTerm hp hp1 ψ (m+1) m =
      ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖^2 /
        (8*‖sourceStandardRootMidpoint hp hp1 ψ m-(Real.pi : ℂ)*((m+1 : ℤ) : ℂ)‖^2) := by
    simp only [sourceMidpointTaylorRealTerm,if_neg (show m ≠ m+1 by omega)]
  rw [hterm] at hle
  have he := (div_le_iff₀ (by positivity :
    0 < 8*‖sourceStandardRootMidpoint hp hp1 ψ m-(Real.pi : ℂ)*((m+1 : ℤ) : ℂ)‖^2)).mp hle
  nlinarith

end NLS.ZakharovShabat
