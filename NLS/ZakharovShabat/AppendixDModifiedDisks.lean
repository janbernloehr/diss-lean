import NLS.ZakharovShabat.DisplacedRootsSeparation
import NLS.ZakharovShabat.AppendixDRelativeProductRows
import NLS.Fourier.ModifiedHilbert
import NLS.SequenceSpaces.UniformSelectionSup

/-! # The finite modification of the head discs in the proof of D.6 -/
noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Keep all separated tail discs and use small root-centered discs in the finite head. -/
def appendixDModifiedDisk (r : Coeff ⊤) (N : ℕ) (ε : ℝ) (n : ℤ) : Set ℂ :=
  if N ≤ n.natAbs then refinedResonantDisk n else ball (displacedRoots r n) ε

/-- Simplicity permits the finite head modification, with its separation constant explicit. -/
theorem exists_appendixDModifiedDisks_separated (r : Coeff ⊤)
    (hr : Function.Injective (displacedRoots r)) {c : ℝ} {N : ℕ}
    (hc : 0 < c) (hsep : AppendixDReferenceSeparated r c N) :
    ∃ ε C : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 0 < C ∧ c ≤ C ∧
      ∀ n : ℤ, ∀ z ∈ appendixDModifiedDisk r N ε n, ∀ m : ℤ, m ≠ n →
        C⁻¹*|((m-n:ℤ):ℝ)| ≤ ‖displacedRoots r m-z‖ := by
  classical
  let S : Finset ℤ := Finset.Icc (-(N:ℤ)) N
  choose d hd hdist using exists_displacedRoot_separation r hr
  obtain ⟨δ,hδ,hδn⟩ := S.finite_toSet.isCompact.exists_forall_le'
    (continuous_of_discreteTopology.continuousOn : ContinuousOn d (S:Set ℤ))
    (fun n _ => hd n)
  let ε := min (δ/2) 1
  have hε : 0 < ε := lt_min (half_pos hδ) (by norm_num)
  have hεδ : ε ≤ δ/2 := min_le_left _ _
  let A := 2*(δ+2*‖r‖)/δ
  have hA : 0 < A := by dsimp [A]; positivity
  let C := max c A
  have hC : 0 < C := lt_of_lt_of_le hc (le_max_left _ _)
  refine ⟨ε,C,hε,min_le_right _ _,hC,le_max_left _ _,?_⟩
  intro n z hz m hmn
  by_cases hn : N ≤ n.natAbs
  · have hz' : z ∈ refinedResonantDisk n := by
      simpa only [appendixDModifiedDisk,if_pos hn] using hz
    exact (mul_le_mul_of_nonneg_right (inv_anti₀ hc (le_max_left c A))
      (abs_nonneg _)).trans (hsep n hn z hz' m hmn)
  · have hnS : n ∈ S := by simp only [S,Finset.mem_Icc]; omega
    have hdroot : δ ≤ ‖displacedRoots r m-displacedRoots r n‖ := by
      have h := (hδn n hnS).trans (hdist n m hmn)
      simpa only [dist_eq_norm,norm_sub_rev] using h
    have hzn : ‖z-displacedRoots r n‖ < ε := by
      simpa only [appendixDModifiedDisk,if_neg hn,mem_ball,dist_eq_norm] using hz
    have htri : ‖displacedRoots r m-displacedRoots r n‖ ≤
        ‖displacedRoots r m-z‖+‖z-displacedRoots r n‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    have hhalf : ‖displacedRoots r m-displacedRoots r n‖ ≤ 2*‖displacedRoots r m-z‖ := by
      linarith
    have hfree : |((m-n:ℤ):ℝ)| ≤ ‖displacedRoots r m-displacedRoots r n‖+2*‖r‖ := by
      have he : (Real.pi:ℂ)*m-(Real.pi:ℂ)*n =
          (displacedRoots r m-displacedRoots r n)-r m+r n := by
        simp only [displacedRoots]
        ring
      have ht : ‖(Real.pi:ℂ)*m-(Real.pi:ℂ)*n‖ ≤
          ‖displacedRoots r m-displacedRoots r n‖+‖r m‖+‖r n‖ := by
        rw [he]
        exact (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      rw [norm_free_center_sub] at ht
      have hmR := lp.norm_apply_le_norm (by simp : (⊤:ℝ≥0∞) ≠ 0) r m
      have hnR := lp.norm_apply_le_norm (by simp : (⊤:ℝ≥0∞) ≠ 0) r n
      nlinarith [Real.pi_gt_three,abs_nonneg (((m-n:ℤ):ℝ))]
    have hweighted : δ*|((m-n:ℤ):ℝ)| ≤
        (δ+2*‖r‖)*‖displacedRoots r m-displacedRoots r n‖ := by
      nlinarith [mul_nonneg (norm_nonneg r) (sub_nonneg.mpr hdroot),
        mul_le_mul_of_nonneg_left hfree hδ.le]
    have hden : |((m-n:ℤ):ℝ)| ≤ A*‖displacedRoots r m-z‖ := by
      dsimp only [A]
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hδ).mpr
      nlinarith [mul_le_mul_of_nonneg_left hhalf
        (show 0 ≤ δ+2*‖r‖ by positivity)]
    have hdenC : |((m-n:ℤ):ℝ)| ≤ C*‖displacedRoots r m-z‖ :=
      hden.trans (mul_le_mul_of_nonneg_right (le_max_right c A) (norm_nonneg _))
    calc
      _ ≤ C⁻¹*(C*‖displacedRoots r m-z‖) := mul_le_mul_of_nonneg_left hdenC (inv_nonneg.mpr hC.le)
      _ = _ := by rw [← mul_assoc,inv_mul_cancel₀ hC.ne',one_mul]

/-- Every modified disc is nonempty. -/
theorem appendixDModifiedDisk_nonempty (r : Coeff ⊤) (N : ℕ) {ε : ℝ}
    (hε : 0 < ε) (n : ℤ) : (appendixDModifiedDisk r N ε n).Nonempty := by
  by_cases hn : N ≤ n.natAbs
  · refine ⟨(Real.pi:ℂ)*n,?_⟩
    simp only [appendixDModifiedDisk,if_pos hn,refinedResonantDisk,mem_ball,dist_self]
    positivity
  · refine ⟨displacedRoots r n,?_⟩
    simpa only [appendixDModifiedDisk,if_neg hn,mem_ball,dist_self] using hε

/-- Modified-disc samples still have one bounded displacement from the free lattice. -/
theorem appendixDModifiedDisk_displacement_le (r : Coeff ⊤) (N : ℕ) {ε : ℝ}
    (hε : ε ≤ 1) (n : ℤ) {z : ℂ} (hz : z ∈ appendixDModifiedDisk r N ε n) :
    ‖z-(Real.pi:ℂ)*n‖ ≤ ‖r‖+1+Real.pi/4 := by
  by_cases hn : N ≤ n.natAbs
  · have hz' : ‖z-(Real.pi:ℂ)*n‖ < Real.pi/4 := by
      simpa only [appendixDModifiedDisk,if_pos hn,refinedResonantDisk,mem_ball,dist_eq_norm] using hz
    linarith [norm_nonneg r]
  · have hz' : ‖z-displacedRoots r n‖ < ε := by
      simpa only [appendixDModifiedDisk,if_neg hn,mem_ball,dist_eq_norm] using hz
    have ht := norm_sub_le_norm_sub_add_norm_sub z (displacedRoots r n) ((Real.pi:ℂ)*n)
    simp only [displacedRoots,add_sub_cancel_left] at ht hz'
    have hr := lp.norm_apply_le_norm (by simp : (⊤:ℝ≥0∞) ≠ 0) r n
    linarith [Real.pi_pos]

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The signed row on the modified discs is an actual convergent ell-p sequence. -/
theorem exists_appendixDModifiedDisk_rows (hp1 : 1 < p) (hp : p ≠ ⊤)
    (r : Coeff ⊤) (N : ℕ) {ε C : ℝ} (hε : ε ≤ 1) (hC : 0 < C)
    (hsep : ∀ n : ℤ, ∀ z ∈ appendixDModifiedDisk r N ε n, ∀ m : ℤ, m ≠ n →
      C⁻¹*|((m-n:ℤ):ℝ)| ≤ ‖displacedRoots r m-z‖)
    (a : Coeff p) (z : ℤ → ℂ) (hz : ∀ n, z n ∈ appendixDModifiedDisk r N ε n) :
    ∃ b : Coeff p,
      (∀ n : ℤ, HasSum (fun m : ℤ => if m=n then 0 else a m/(displacedRoots r m-z n)) (b n)) ∧
      ‖b‖ ≤ Real.pi⁻¹*(NLS.Fourier.hilbertTransformBound hp1 hp+
        C*(2*‖r‖+1+Real.pi/4)*‖NLS.Fourier.hilbertSquareCoeffs‖)*‖a‖ := by
  let s : Coeff ⊤ := ⟨fun n => z n-(Real.pi:ℂ)*n, by
    apply memℓp_infty
    refine ⟨‖r‖+1+Real.pi/4,?_⟩
    rintro _ ⟨n,rfl⟩
    exact appendixDModifiedDisk_displacement_le r N hε n (hz n)⟩
  have hs : ‖s‖ ≤ ‖r‖+1+Real.pi/4 := by
    apply lp.norm_le_of_forall_le (by positivity)
    intro n
    exact appendixDModifiedDisk_displacement_le r N hε n (hz n)
  have hsn (n : ℤ) : NLS.Fourier.hilbertLattice s n = z n := by
    change (Real.pi:ℂ)*n+(z n-(Real.pi:ℂ)*n)=z n
    ring
  have hsep' : NLS.Fourier.HilbertLatticeSeparated s r C := by
    intro n m hmn
    rw [hsn]
    have he : (m:ℂ)-n = (((m-n:ℤ):ℝ):ℂ) := by push_cast; rfl
    simpa only [he,Complex.norm_real,Real.norm_eq_abs,NLS.Fourier.hilbertLattice,displacedRoots]
      using hsep n (z n) (hz n) m hmn
  let A := NLS.Fourier.modifiedHilbert s r hC hsep' hp1 hp
  let b : Coeff p := (Real.pi:ℂ)⁻¹ • A a
  refine ⟨b,?_,?_⟩
  · intro n
    have h := (NLS.Fourier.summable_norm_modifiedHilbert_source_series s r hC hsep' hp1 hp a n).of_norm.hasSum
    have hb : b n = ∑' m : ℤ, if m=n then 0 else a m/(displacedRoots r m-z n) := by
      simp only [b,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,A,
        NLS.Fourier.modifiedHilbert_source_apply,← mul_assoc,
        inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero),one_mul]
      simp_rw [hsn]
      rfl
    rw [hb]
    simp_rw [hsn] at h
    exact h
  · have hnorm := NLS.Fourier.norm_modifiedHilbert_apply_le s r hC hsep' hp1 hp a
    have hbound : ‖A a‖ ≤ (NLS.Fourier.hilbertTransformBound hp1 hp+
        C*(2*‖r‖+1+Real.pi/4)*‖NLS.Fourier.hilbertSquareCoeffs‖)*‖a‖ := by
      apply hnorm.trans
      have hsum : ‖s‖+‖r‖ ≤ 2*‖r‖+1+Real.pi/4 := by linarith
      exact mul_le_mul_of_nonneg_right
        (add_le_add le_rfl (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsum hC.le) (norm_nonneg _))) (norm_nonneg a)
    change ‖(Real.pi:ℂ)⁻¹ • A a‖ ≤ _
    rw [norm_smul,norm_inv,Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le]
    exact (mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr Real.pi_pos.le)).trans_eq (by ring)

/-- One least majorant controls the signed sums on all the modified discs. -/
theorem exists_appendixDModifiedDisk_signed_sup (hp1 : 1 < p) (hp : p ≠ ⊤)
    (r : Coeff ⊤) (N : ℕ) {ε C : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1) (hC : 0 < C)
    (hsep : ∀ n : ℤ, ∀ z ∈ appendixDModifiedDisk r N ε n, ∀ m : ℤ, m ≠ n →
      C⁻¹*|((m-n:ℤ):ℝ)| ≤ ‖displacedRoots r m-z‖) (a : Coeff p) :
    ∃ b : Coeff p,
      (∀ n : ℤ, ∀ z ∈ appendixDModifiedDisk r N ε n,
        ‖∑' m : ℤ, if m=n then 0 else a m/(displacedRoots r m-z)‖ ≤ ‖b n‖) ∧
      (∀ n : ℤ, ∀ t : ℝ, 0 ≤ t →
        (∀ z ∈ appendixDModifiedDisk r N ε n,
          ‖∑' m : ℤ, if m=n then 0 else a m/(displacedRoots r m-z)‖ ≤ t) → ‖b n‖ ≤ t) ∧
      ‖b‖ ≤ Real.pi⁻¹*(NLS.Fourier.hilbertTransformBound hp1 hp+
        C*(2*‖r‖+1+Real.pi/4)*‖NLS.Fourier.hilbertSquareCoeffs‖)*‖a‖ := by
  have hK : 0 ≤ Real.pi⁻¹*(NLS.Fourier.hilbertTransformBound hp1 hp+
      C*(2*‖r‖+1+Real.pi/4)*‖NLS.Fourier.hilbertSquareCoeffs‖)*‖a‖ := by
    have hH := NLS.Fourier.hilbertTransformBound_nonneg hp1 hp
    positivity
  obtain ⟨b,hb,hmin,_,hbn⟩ := NLS.exists_uniformSelectionSup hp Set.univ
    (appendixDModifiedDisk r N ε) (appendixDModifiedDisk_nonempty r N hε0)
    (fun n z => ∑' m : ℤ, if m=n then 0 else a m/(displacedRoots r m-z)) _ hK (by
      intro z hz
      obtain ⟨b,hb,hbn⟩ := exists_appendixDModifiedDisk_rows hp1 hp r N hε hC hsep a z hz
      exact ⟨b,fun n _ => (hb n).tsum_eq.symm,hbn⟩)
  exact ⟨b,fun n => hb n (Set.mem_univ n),fun n => hmin n (Set.mem_univ n),hbn⟩

/-- One finite modification and separation constant work before every input sequence. -/
theorem exists_appendixDModifiedDisk_signed_sup_of_simple (hp1 : 1 < p) (hp : p ≠ ⊤)
    (r : Coeff ⊤) (hr : Function.Injective (displacedRoots r)) {c : ℝ} {N : ℕ}
    (hc : 0 < c) (hsep : AppendixDReferenceSeparated r c N) :
    ∃ ε C : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 0 < C ∧ c ≤ C ∧ ∀ a : Coeff p,
      ∃ b : Coeff p,
        (∀ n : ℤ, ∀ z ∈ appendixDModifiedDisk r N ε n,
          ‖∑' m : ℤ, if m=n then 0 else a m/(displacedRoots r m-z)‖ ≤ ‖b n‖) ∧
        (∀ n : ℤ, ∀ t : ℝ, 0 ≤ t →
          (∀ z ∈ appendixDModifiedDisk r N ε n,
            ‖∑' m : ℤ, if m=n then 0 else a m/(displacedRoots r m-z)‖ ≤ t) → ‖b n‖ ≤ t) ∧
        ‖b‖ ≤ Real.pi⁻¹*(NLS.Fourier.hilbertTransformBound hp1 hp+
          C*(2*‖r‖+1+Real.pi/4)*‖NLS.Fourier.hilbertSquareCoeffs‖)*‖a‖ := by
  obtain ⟨ε,C,hε0,hε,hC,hcC,hD⟩ := exists_appendixDModifiedDisks_separated r hr hc hsep
  exact ⟨ε,C,hε0,hε,hC,hcC,fun a =>
    exists_appendixDModifiedDisk_signed_sup hp1 hp r N hε0 hε hC hD a⟩

end NLS.ZakharovShabat
