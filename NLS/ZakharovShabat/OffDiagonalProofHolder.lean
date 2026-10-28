import NLS.ZakharovShabat.OffDiagonalProofPowerSums
import NLS.ZakharovShabat.OffDiagonalHolder
import NLS.SequenceSpaces.WeightedFourierTail

/-! # The literal regional weighted Holder step (1.16)

The three positive regional sums cover the full weighted majorant, allowing
the overlap of the far sets. The weak near region retains the outer potential tail.
-/
noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- The exact positive weighted regional test in normalized reciprocal coordinates. -/
def offDiagonalProofTest (hq : 1 < q) (i : OffDiagonalProofRegion) (w : SpectralWeight)
    (d a f : WeightedCoeff w.toWeight p) (n : ℤ) (j k : ℤ) : ℝ :=
  ‖w.doubleOuterCoeffs n d j * WeightedCoeff.weightEquiv w.toWeight p a (2*n-j-k) *
    offDiagonalProofRightKernel hq i n k * offDiagonalProofLeftKernel hq i n j * w.doubleInputCoeffs n f k‖

/-- Each positive regional test is jointly summable. -/
theorem summable_offDiagonalProofTest [p.HolderConjugate q] (hq : 1 < q)
    (i : OffDiagonalProofRegion) (w : SpectralWeight) (d a f : WeightedCoeff w.toWeight p) (n : ℤ) :
    Summable (fun jk : ℤ × ℤ => offDiagonalProofTest hq i w d a f n jk.1 jk.2) :=
  Coeff.summable_iteratedRowTest_prod _ _ _ _ _ _

/-- Two Holder inequalities give exactly the actual regional row norm. -/
theorem offDiagonalProofTest_holder [p.HolderConjugate q] (hq : 1 < q)
    (i : OffDiagonalProofRegion) (w : SpectralWeight) (d a f : WeightedCoeff w.toWeight p) (n : ℤ) :
    (∑' jk : ℤ × ℤ, offDiagonalProofTest hq i w d a f n jk.1 jk.2) ≤
      ‖d‖*w.shiftedNorm n f*‖offDiagonalProofRow hq i (WeightedCoeff.weightEquiv w.toWeight p a) n‖ := by
  rw [(summable_offDiagonalProofTest hq i w d a f n).tsum_prod]
  simpa only [w.norm_doubleOuterCoeffs,w.norm_doubleInputCoeffs,offDiagonalProofTest,offDiagonalProofRow] using
    Coeff.tsum_norm_iteratedRowTest_le (WeightedCoeff.weightEquiv w.toWeight p a)
      (w.doubleOuterCoeffs n d) (w.doubleInputCoeffs n f)
      (offDiagonalProofLeftKernel hq i n) (offDiagonalProofRightKernel hq i n) (2*n)

omit [Fact (1 ≤ q)] in
/-- The near test is unchanged when the actual outer potential is replaced by its full tail. -/
theorem offDiagonalProofNearTest_eq_tail (hq : 1 < q) (w : SpectralWeight)
    (d a f : WeightedCoeff w.toWeight p) (N : ℕ) (n : ℤ) (hn : N ≤ n.natAbs) (j k : ℤ) :
    offDiagonalProofTest hq .near w d a f n j k =
      offDiagonalProofTest hq .near w (WeightedCoeff.fourierTail w.toWeight N d) a f n j k := by
  by_cases hj : j.natAbs < offDiagonalProofCutoff n
  · by_cases hk : k.natAbs < offDiagonalProofCutoff n
    · have h := (offDiagonalProofNear_tail_indices N n j k hn hj hk).1
      simp only [offDiagonalProofTest,SpectralWeight.doubleOuterCoeffs_apply,WeightedCoeff.fourierTail_apply,if_pos h]
    · simp [offDiagonalProofTest,offDiagonalProofRightKernel_apply,OffDiagonalProofRegion.right,hk]
  · simp [offDiagonalProofTest,offDiagonalProofLeftKernel_apply,OffDiagonalProofRegion.left,hj]

/-- The second factor in (1.16) improves to the actual full-cutoff outer-potential tail on near indices. -/
theorem offDiagonalProofNearTest_holder [p.HolderConjugate q] (hq : 1 < q) (w : SpectralWeight)
    (d a f : WeightedCoeff w.toWeight p) (N : ℕ) (n : ℤ) (hn : N ≤ n.natAbs) :
    (∑' jk : ℤ × ℤ, offDiagonalProofTest hq .near w d a f n jk.1 jk.2) ≤
      ‖WeightedCoeff.fourierTail w.toWeight N d‖*w.shiftedNorm n f*
        ‖offDiagonalProofRow hq .near (WeightedCoeff.weightEquiv w.toWeight p a) n‖ := by
  simp only [offDiagonalProofNearTest_eq_tail hq w d a f N n hn]
  exact offDiagonalProofTest_holder hq .near w _ a f n

/-- Physical-coordinate form of the positive sum printed in (1.16). -/
def offDiagonalProofWeightedTerm (i : OffDiagonalProofRegion) (w : SpectralWeight)
    (d a f : WeightedCoeff w.toWeight p) (n l k : ℤ) : ℝ :=
  if i.contains n l k then
    (w (n+l)*‖d.val (n+l)‖)*(w (l+k)*‖a.val (l+k)‖)/|((n-l : ℤ):ℝ)|/|((n-k : ℤ):ℝ)| *
      (w (n+k)*‖f.val k‖) else 0

omit [Fact (1 ≤ q)] in
/-- The physical weighted summand is exactly the two-index Holder test, including the resonant exclusions. -/
theorem offDiagonalProofWeightedTerm_eq (hq : 1 < q) (i : OffDiagonalProofRegion) (w : SpectralWeight)
    (d a f : WeightedCoeff w.toWeight p) (n l k : ℤ) :
    offDiagonalProofWeightedTerm i w d a f n l k = offDiagonalProofTest hq i w d a f n (n-l) (n-k) := by
  simp only [offDiagonalProofTest,SpectralWeight.doubleOuterCoeffs_apply,
    SpectralWeight.doubleInputCoeffs_apply,WeightedCoeff.weightEquiv_apply,
    show 2*n-(n-l) = n+l by ring,show 2*n-(n-k) = n+k by ring,
    show n+l-(n-k) = l+k by ring,sub_sub_cancel,
    offDiagonalProofLeftKernel_apply,offDiagonalProofRightKernel_apply]
  by_cases hl : l = n
  · subst l
    simp [offDiagonalProofWeightedTerm,OffDiagonalProofRegion.contains]
  by_cases hk : k = n
  · subst k
    simp [offDiagonalProofWeightedTerm,OffDiagonalProofRegion.contains]
  by_cases hL : i.left n (n-l) <;> by_cases hK : i.right n (n-k)
  all_goals simp only [offDiagonalProofWeightedTerm,OffDiagonalProofRegion.contains,ne_eq,hl,hk,hL,hK,
    not_false_eq_true,if_true,if_false,and_false,and_true,mul_zero,zero_mul,norm_zero]
  simp only [norm_mul,Complex.norm_real,Real.norm_of_nonneg (w.positive _).le,
    norm_puncturedLattice_eq_inv_abs,div_eq_mul_inv]
  ring

/-- Absolute joint convergence justifies either order of the physical regional sum. -/
theorem summable_offDiagonalProofWeightedTerm [p.HolderConjugate q] (hq : 1 < q)
    (i : OffDiagonalProofRegion) (w : SpectralWeight) (d a f : WeightedCoeff w.toWeight p) (n : ℤ) :
    Summable (fun lk : ℤ × ℤ => offDiagonalProofWeightedTerm i w d a f n lk.1 lk.2) := by
  have hs := ((Equiv.subLeft n).prodCongr (Equiv.subLeft n)).summable_iff.mpr
    (summable_offDiagonalProofTest hq i w d a f n)
  exact hs.congr (fun lk => (offDiagonalProofWeightedTerm_eq hq i w d a f n lk.1 lk.2).symm)

/-- The two physical summations give the same actual positive regional test. -/
theorem offDiagonalProofWeightedSum_eq [p.HolderConjugate q] (hq : 1 < q)
    (i : OffDiagonalProofRegion) (w : SpectralWeight) (d a f : WeightedCoeff w.toWeight p) (n : ℤ) :
    (∑' l : ℤ, ∑' k : ℤ, offDiagonalProofWeightedTerm i w d a f n l k) =
      ∑' jk : ℤ × ℤ, offDiagonalProofTest hq i w d a f n jk.1 jk.2 := by
  rw [(summable_offDiagonalProofTest hq i w d a f n).tsum_prod]
  conv_rhs => rw [← (Equiv.subLeft n).tsum_eq]
  apply tsum_congr
  intro l
  conv_rhs => rw [← (Equiv.subLeft n).tsum_eq]
  apply tsum_congr
  intro k
  exact offDiagonalProofWeightedTerm_eq hq i w d a f n l k

/-- Equation (1.16) for each literal source region and its displayed reciprocal moment. -/
theorem sourceEquation1_16 [p.HolderConjugate q] (hq : 1 < q) (hqt : q ≠ ⊤)
    (i : OffDiagonalProofRegion) (w : SpectralWeight) (d a f : WeightedCoeff w.toWeight p) (n : ℤ) :
    (∑' l : ℤ, ∑' k : ℤ, offDiagonalProofWeightedTerm i w d a f n l k) ≤
      ‖d‖*w.shiftedNorm n f*(offDiagonalProofMoment q i (WeightedCoeff.weightEquiv w.toWeight p a) n)^(1/q.toReal) := by
  rw [offDiagonalProofWeightedSum_eq hq,offDiagonalProofMoment_eq hq hqt,
    ← Real.rpow_mul (norm_nonneg _),mul_one_div_cancel (ENNReal.toReal_pos (zero_lt_one.trans hq).ne' hqt).ne',Real.rpow_one]
  exact offDiagonalProofTest_holder hq i w d a f n

/-- The near case of (1.16) retains the stronger full-cutoff outer-potential tail. -/
theorem sourceEquation1_16_near [p.HolderConjugate q] (hq : 1 < q) (hqt : q ≠ ⊤)
    (w : SpectralWeight) (d a f : WeightedCoeff w.toWeight p) (N : ℕ) (n : ℤ) (hn : N ≤ n.natAbs) :
    (∑' l : ℤ, ∑' k : ℤ, offDiagonalProofWeightedTerm .near w d a f n l k) ≤
      ‖WeightedCoeff.fourierTail w.toWeight N d‖*w.shiftedNorm n f*
        (offDiagonalProofMoment q .near (WeightedCoeff.weightEquiv w.toWeight p a) n)^(1/q.toReal) := by
  rw [offDiagonalProofWeightedSum_eq hq,offDiagonalProofMoment_eq hq hqt,
    ← Real.rpow_mul (norm_nonneg _),mul_one_div_cancel (ENNReal.toReal_pos (zero_lt_one.trans hq).ne' hqt).ne',Real.rpow_one]
  exact offDiagonalProofNearTest_holder hq w d a f N n hn

omit [Fact (1 ≤ q)] in
/-- Three positive regional tests dominate the actual weighted term; overlap can only increase the bound. -/
theorem norm_weightedOffDiagonalTerm_le_proof_regions (hq : 1 < q) (w : SpectralWeight)
    (d a f : WeightedCoeff w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) (j k : ℤ) :
    ‖weightedOffDiagonalTerm w d a f n z j k‖ ≤
      offDiagonalProofTest hq .farK w d a f n j k + offDiagonalProofTest hq .farL w d a f n j k +
      offDiagonalProofTest hq .near w d a f n j k := by
  apply (norm_weightedOffDiagonalTerm_le hq w d a f n z hz j k).trans
  by_cases hj : offDiagonalProofCutoff n ≤ j.natAbs <;>
    by_cases hk : offDiagonalProofCutoff n ≤ k.natAbs
  all_goals simp only [offDiagonalProofTest,offDiagonalProofLeftKernel_apply,
    offDiagonalProofRightKernel_apply,OffDiagonalProofRegion.left,OffDiagonalProofRegion.right,
    lt_iff_not_ge,hj,hk,not_false_eq_true,not_true_eq_false,if_true,if_false,mul_zero,zero_mul,norm_zero,add_zero,zero_add]
  all_goals first | exact le_rfl | exact le_add_of_nonneg_right (norm_nonneg _)

/-- The actual weighted series is bounded by the exact far moments and the stronger near outer-potential tail. -/
theorem norm_tsum_offDiagonal_proof_regions_le [p.HolderConjugate q] (hq : 1 < q)
    (w : SpectralWeight) (d a f : WeightedCoeff w.toWeight p) (N : ℕ) (n : ℤ) (hn : N ≤ n.natAbs)
    (z : ℂ) (hz : z ∈ resonantStrip n) :
    ‖∑' jk : ℤ × ℤ, weightedOffDiagonalTerm w d a f n z jk.1 jk.2‖ ≤
      w.shiftedNorm n f*(‖d‖*(‖offDiagonalProofRow hq .farK (WeightedCoeff.weightEquiv w.toWeight p a) n‖ +
        ‖offDiagonalProofRow hq .farL (WeightedCoeff.weightEquiv w.toWeight p a) n‖) +
        ‖WeightedCoeff.fourierTail w.toWeight N d‖*‖offDiagonalProofRow hq .near (WeightedCoeff.weightEquiv w.toWeight p a) n‖) := by
  have hs := summable_norm_weightedOffDiagonalTerm hq w d a f n z hz
  have hK := summable_offDiagonalProofTest hq .farK w d a f n
  have hL := summable_offDiagonalProofTest hq .farL w d a f n
  have hH := summable_offDiagonalProofTest hq .near w d a f n
  let K := fun jk : ℤ × ℤ => offDiagonalProofTest hq .farK w d a f n jk.1 jk.2
  let L := fun jk : ℤ × ℤ => offDiagonalProofTest hq .farL w d a f n jk.1 jk.2
  let H := fun jk : ℤ × ℤ => offDiagonalProofTest hq .near w d a f n jk.1 jk.2
  have hdom : (∑' jk : ℤ × ℤ, ‖weightedOffDiagonalTerm w d a f n z jk.1 jk.2‖) ≤
      ∑' jk : ℤ × ℤ, (K jk+L jk+H jk) :=
    hs.tsum_le_tsum (fun jk => norm_weightedOffDiagonalTerm_le_proof_regions hq w d a f n z hz jk.1 jk.2)
      ((hK.add hL).add hH)
  have he : (∑' jk : ℤ × ℤ, (K jk+L jk+H jk)) = (∑' jk,K jk)+(∑' jk,L jk)+(∑' jk,H jk) := by
    rw [(hK.add hL).tsum_add hH,hK.tsum_add hL]
  rw [he] at hdom
  have hb := add_le_add (add_le_add (offDiagonalProofTest_holder hq .farK w d a f n)
    (offDiagonalProofTest_holder hq .farL w d a f n))
    (offDiagonalProofNearTest_holder hq w d a f N n hn)
  exact ((norm_tsum_le_tsum_norm hs).trans hdom).trans (hb.trans_eq (by ring))

end NLS.ZakharovShabat
