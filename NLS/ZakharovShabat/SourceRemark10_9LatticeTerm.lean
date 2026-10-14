import NLS.ZakharovShabat.SourceMidpointQuotientTaylorGeometry
import NLS.ZakharovShabat.SourcePsiNearFreeGapGeometry

/-!
# Comparing the printed lattice term with the exact Taylor term

For real sources the signed integer-lattice sum in Remark 10.9 is
exactly the nonnegative physical squared-gap row. Near the free source,
the exact Taylor term at `nπ` has norm at most one eighth of that row.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The signed sum printed in Remark 10.9, with its stated normalization. -/
def sourceRemark10_9LatticeTerm (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) : ℂ :=
  ∑' m : ℤ, if m = n then 0 else
    (sourcePeriodicGapDisplacement hp hp1 ψ m)^2 / (((m-n : ℤ) : ℂ)^2)

theorem sourceRemark10_9LatticeTerm_eq_physicalRow
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p ψ)) (n : ℤ) :
    sourceRemark10_9LatticeTerm hp hp1 ψ n =
      ((∑' m : ℤ, sourceSquaredGapReciprocalTerm hp hp1 ψ n m : ℝ) : ℂ) := by
  rw [sourceRemark10_9LatticeTerm,Complex.ofReal_tsum]
  apply tsum_congr
  intro m
  by_cases hm : m = n
  · simp [sourceSquaredGapReciprocalTerm,hm]
  obtain ⟨hl,hr⟩ := canonicalPeriodicEndpoints_im_eq_zero_of_realType hp hp1 _
    (periodOnePotential_mem ψ) (isRealType_periodOnePotential ψ hreal) m
  have hi : (sourcePeriodicGapDisplacement hp hp1 ψ m).im = 0 := by
    simp only [sourcePeriodicGapDisplacement_apply,canonicalPeriodicGap,sub_im,hl,hr,sub_self]
  have hs : (sourcePeriodicGapDisplacement hp hp1 ψ m)^2 =
      ((‖sourcePeriodicGapDisplacement hp hp1 ψ m‖^2 : ℝ) : ℂ) := by
    rw [Complex.sq_norm,Complex.normSq_apply,hi]
    apply Complex.ext <;> simp only [pow_two,mul_re,mul_im,ofReal_re,ofReal_im,
      hi,mul_zero,zero_mul,add_zero,sub_zero]
  simp only [sourceSquaredGapReciprocalTerm,if_neg hm,hs,
    Real.rpow_neg (abs_nonneg _),Real.rpow_ofNat,sq_abs,
    Complex.ofReal_mul,Complex.ofReal_inv,Complex.ofReal_pow,Complex.ofReal_intCast,
    div_eq_mul_inv]

/-- A unit bound on the midpoint displacement retains at least unit
lattice separation from every other free center. -/
theorem sourceMidpoint_freeCenter_separation
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    (hsmall : ‖sourcePeriodicMidpointDisplacement hp hp1 ψ‖ ≤ 1)
    (m n : ℤ) (hmn : m ≠ n) :
    |((m-n : ℤ) : ℝ)| ≤
      ‖sourceStandardRootMidpoint hp hp1 ψ m - (Real.pi : ℂ)*n‖ := by
  have hcoord := (lp.norm_apply_le_norm (zero_lt_one.trans hp1).ne'
    (sourcePeriodicMidpointDisplacement hp hp1 ψ) m).trans hsmall
  have hdisp : ‖sourceStandardRootMidpoint hp hp1 ψ m - (Real.pi : ℂ)*m‖ ≤ 1 := by
    simpa only [sourcePeriodicMidpointDisplacement_apply,sourceStandardRootMidpoint] using hcoord
  have hd : (1 : ℝ) ≤ |((m-n : ℤ) : ℝ)| := by
    exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hmn)
  have htri := norm_add_le ((Real.pi : ℂ)*m-sourceStandardRootMidpoint hp hp1 ψ m)
    (sourceStandardRootMidpoint hp hp1 ψ m-(Real.pi : ℂ)*n)
  rw [sub_add_sub_cancel,norm_free_center_sub,norm_sub_rev] at htri
  nlinarith [Real.two_le_pi]

/-- At a free center, the exact linear term is at most one eighth of
the absolute lattice row on the same original source neighborhood. -/
theorem norm_sourceMidpointQuotientLinearTerm_freeCenter_le
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    (hsmall : ‖sourcePeriodicMidpointDisplacement hp hp1 ψ‖ ≤ 1) (n : ℤ) :
    ‖sourceMidpointQuotientLinearTerm hp hp1 ψ n ((Real.pi : ℂ)*n)‖ ≤
      (∑' m : ℤ, sourceSquaredGapReciprocalTerm hp hp1 ψ n m)/8 := by
  let f : ℤ → ℂ := fun m => if m = n then 0 else
    (sourcePeriodicGapDisplacement hp hp1 ψ m)^2 /
      (8*(sourceStandardRootMidpoint hp hp1 ψ m-(Real.pi : ℂ)*n)^2)
  have he : sourceMidpointQuotientLinearTerm hp hp1 ψ n ((Real.pi : ℂ)*n) = ∑' m, f m := by
    simpa only [f,sourceStandardRootMidpoint,sourcePeriodicGapDisplacement_apply] using
      sourceMidpointQuotientLinearTerm_eq hp hp1 ψ n ((Real.pi : ℂ)*n)
  have hpoint (m : ℤ) : ‖f m‖ ≤ sourceSquaredGapReciprocalTerm hp hp1 ψ n m/8 := by
    by_cases hm : m = n
    · simp [f,sourceSquaredGapReciprocalTerm,hm]
    have hd : 0 < |((m-n : ℤ) : ℝ)| := abs_pos.mpr (by exact_mod_cast sub_ne_zero.mpr hm)
    have hsep := sourceMidpoint_freeCenter_separation hp hp1 ψ hsmall m n hm
    have hs := pow_le_pow_left₀ hd.le hsep 2
    simp only [f,sourceSquaredGapReciprocalTerm,if_neg hm,norm_div,norm_mul,norm_pow,
      Complex.norm_ofNat,Real.rpow_neg (abs_nonneg _),Real.rpow_ofNat]
    calc
      _ ≤ ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖^2 / (8*|((m-n : ℤ) : ℝ)|^2) :=
        div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by nlinarith)
      _ = _ := by ring
  have hrow := ((exists_sourceSquaredGapPhysicalRows hp hp1 ψ).choose_spec.1 n).1
  have hsum := Summable.of_nonneg_of_le (fun m => norm_nonneg (f m)) hpoint (hrow.div_const 8)
  rw [he]
  exact (norm_tsum_le_tsum_norm hsum).trans ((hsum.tsum_le_tsum hpoint
    (hrow.div_const 8)).trans_eq (tsum_div_const))

end NLS.ZakharovShabat
