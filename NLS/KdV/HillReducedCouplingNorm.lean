import NLS.KdV.PseudomeasureRootSeparation

/-! Actual full two-mode matrix and its norm at a genuine determinant zero,
with original complex couplings and no reality or diagonalizability premise. -/
noncomputable section
open scoped ENNReal
namespace NLS.KdV

/-- The ACTUAL reduced family has the literal common-diagonal source matrix. -/
theorem endpointReducedFamily_apply_common_diagonal
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2) (n : ℕ) (hn : 1 ≤ n) (z : ℂ)
    (hz : z ∈ reducedHillStrip n) (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2) (u : ℂ × ℂ) :
    endpointReducedFamily r hr hr1 n (q,z) u =
      ((z-(freeHillValue n:ℂ)-endpointDiagonal r hr hr1 n (q,z))*u.1-
        endpointUpperCoupling r hr hr1 n (q,z)*u.2,
       (z-(freeHillValue n:ℂ)-endpointDiagonal r hr hr1 n (q,z))*u.2-
        endpointLowerCoupling r hr hr1 n (q,z)*u.1) := by
  let E := endpointEffectiveFamily r hr hr1 n (q,z)
  have hsplit : E u=u.1 • E (1,0)+u.2 • E (0,1) := by
    rw [← map_smul,← map_smul,← map_add]
    congr 1
    ext <;> simp
  have hd : (E (0,1)).val (-(n:ℤ))=endpointDiagonal r hr hr1 n (q,z) := by
    dsimp [E,endpointDiagonal]
    rw [endpointEffectiveFamily_eq r hr hr1 n hn (q,z) hz hs]
    exact (endpointHillEffectivePotential_diagonals_eq r hr hr1 n hn z hz q hs).symm
  have hfirst : (E u).val (n:ℤ)=endpointDiagonal r hr hr1 n (q,z)*u.1+
      endpointUpperCoupling r hr hr1 n (q,z)*u.2 := by
    rw [hsplit]
    change u.1*(E (1,0)).val (n:ℤ)+u.2*(E (0,1)).val (n:ℤ)=_
    dsimp only [E,endpointDiagonal,endpointUpperCoupling]
    ring
  have hsecond : (E u).val (-(n:ℤ))=endpointDiagonal r hr hr1 n (q,z)*u.2+
      endpointLowerCoupling r hr hr1 n (q,z)*u.1 := by
    rw [hsplit]
    change u.1*(E (1,0)).val (-(n:ℤ))+u.2*(E (0,1)).val (-(n:ℤ))=_
    rw [hd]
    dsimp only [E,endpointLowerCoupling]
    ring
  change ((z-(freeHillValue n:ℂ))*u.1-(E u).val (n:ℤ),
    (z-(freeHillValue n:ℂ))*u.2-(E u).val (-(n:ℤ)))=_
  rw [hfirst,hsecond]
  apply Prod.ext <;> dsimp only <;> ring

/-- At an ACTUAL reduced determinant zero, the full max-pair matrix norm
is bounded by TWICE the sum of the ACTUAL two complex coupling norms. -/
theorem norm_endpointReducedFamily_apply_le_couplings
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2) (n : ℕ) (hn : 1 ≤ n) (z : ℂ)
    (hz : z ∈ reducedHillStrip n) (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2)
    (hdet : endpointReducedDeterminant r hr hr1 n (q,z)=0) (u : ℂ × ℂ) :
    ‖endpointReducedFamily r hr hr1 n (q,z) u‖ ≤
      2*(‖endpointUpperCoupling r hr hr1 n (q,z)‖+‖endpointLowerCoupling r hr hr1 n (q,z)‖)*‖u‖ := by
  let d := z-(freeHillValue n:ℂ)-endpointDiagonal r hr hr1 n (q,z)
  let b := endpointUpperCoupling r hr hr1 n (q,z)
  let c := endpointLowerCoupling r hr hr1 n (q,z)
  have he : d^2=b*c := by
    rw [endpointReducedDeterminant_factorization r hr hr1 n hn q hs z hz] at hdet
    exact sub_eq_zero.mp hdet
  have hsq : ‖d‖^2=‖b‖*‖c‖ := by
    have h := congrArg norm he
    simpa only [norm_pow,norm_mul] using h
  have hd : ‖d‖ ≤ ‖b‖+‖c‖ := by
    nlinarith [sq_nonneg (‖b‖-‖c‖),norm_nonneg d,norm_nonneg b,norm_nonneg c]
  have hrow (x y e : ℂ) (hx : ‖x‖ ≤ ‖u‖) (hy : ‖y‖ ≤ ‖u‖) (he : ‖e‖ ≤ ‖b‖+‖c‖) :
      ‖d*x-e*y‖ ≤ 2*(‖b‖+‖c‖)*‖u‖ := by
    calc
      _ ≤ ‖d*x‖+‖e*y‖ := norm_sub_le _ _
      _ = ‖d‖*‖x‖+‖e‖*‖y‖ := by rw [norm_mul,norm_mul]
      _ ≤ (‖b‖+‖c‖)*‖u‖+(‖b‖+‖c‖)*‖u‖ :=
        add_le_add (mul_le_mul hd hx (norm_nonneg x) (by positivity))
          (mul_le_mul he hy (norm_nonneg y) (by positivity))
      _ = _ := by ring
  rw [endpointReducedFamily_apply_common_diagonal r hr hr1 n hn z hz q hs,Prod.norm_def]
  exact max_le (hrow u.1 u.2 b (norm_fst_le u) (norm_snd_le u) (by linarith [norm_nonneg c]))
    (hrow u.2 u.1 c (norm_snd_le u) (norm_fst_le u) (by linarith [norm_nonneg b]))

end NLS.KdV
