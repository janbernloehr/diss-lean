import NLS.Fourier.PhysicalMidpointProductRemainder
import NLS.ZakharovShabat.FreeDiscSeparation
import NLS.ZakharovShabat.RestoredSpectralPairs

/-! # Lemma D.6: relative products over a bounded reference displacement

The reference roots are pi*m+r(m), with r in ell-infinity. Separation is
required only on the selected distant free discs. The signed reciprocal
row and the quadratic remainder give a bound uniform in all independent
choices of one spectral point from each disc.
-/
noncomputable section
open Set Metric
open scoped ENNReal
open NLS.Fourier
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The pointwise form of the source's lower bound on every distant disc. -/
def AppendixDReferenceSeparated (r : Coeff ⊤) (c : ℝ) (N : ℕ) : Prop :=
  ∀ n : ℤ, N ≤ n.natAbs → ∀ z ∈ refinedResonantDisk n, ∀ m : ℤ, m ≠ n →
    c⁻¹*|((m-n:ℤ):ℝ)| ≤ ‖displacedRoots r m-z‖

/-- The literal omitted relative product minus one in D.6. -/
def appendixDRelativeProductError (r : Coeff ⊤) (a : Coeff p) (n : ℤ) (z : ℂ) : ℂ :=
  (∏' m : ℤ, if m = n then 1 else
    (displacedRoots r m+a m-z)/(displacedRoots r m-z))-1

/-- The row bound before replacing the input norm by a norm-ball radius. -/
def appendixDRelativeProductBound (hp1 : 1 < p) (hp : p ≠ ⊤) (c B A : ℝ) : ℝ :=
  (Real.pi⁻¹*(hilbertTransformBound hp1 hp+‖hilbertSquareCoeffs‖)+
    c*B*‖hilbertSquareCoeffs‖)*A+
    Real.exp ((c/2)*absoluteSampledRowConstant hp*A)*
      ((c/2)*absoluteSampledRowConstant hp*A)^2

/-- Source separation and free-disc geometry satisfy the abstract row hypotheses. -/
theorem appendixD_separatedReciprocalRows (r : Coeff ⊤) {c B : ℝ} {N : ℕ}
    (hc : 0 < c) (hB : 0 ≤ B) (hr : ‖r‖ ≤ B)
    (hsep : AppendixDReferenceSeparated r c N) (z : ℤ → ℂ)
    (hz : ∀ n : ℤ, N ≤ n.natAbs → z n ∈ refinedResonantDisk n) :
    SeparatedReciprocalRows {n : ℤ | N ≤ n.natAbs} c B (displacedRoots r) z := by
  refine ⟨hB,hc,?_,?_,?_⟩
  · intro m
    simpa only [displacedRoots, add_sub_cancel_left] using
      (lp.norm_apply_le_norm (by simp : (⊤:ℝ≥0∞) ≠ 0) r m).trans hr
  · intro n hn m hmn
    have h := mul_le_mul_of_nonneg_left (hsep n hn (z n) (hz n hn) m hmn) hc.le
    rw [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul] at h
    simpa only [Int.cast_sub, abs_sub_comm] using h
  · intro n hn m hmn
    have hm : (Real.pi:ℂ)*m ∈ refinedResonantDisk m := by
      simp only [refinedResonantDisk, mem_ball, dist_self]
      positivity
    have h := (refinedResonantDisk_pointwise_separation hmn hm (hz n hn)).1
    have hπ : 1 ≤ Real.pi/2 := by nlinarith [Real.pi_gt_three]
    have he : |((m-n:ℤ):ℝ)| = |((n-m:ℤ):ℝ)| := by
      simp only [Int.cast_sub, abs_sub_comm]
    rw [he, dist_eq_norm] at h
    nlinarith [abs_nonneg (((n-m:ℤ):ℝ))]

/-- At an admissible sample, every retained reference denominator is nonzero. -/
theorem appendixD_reference_denominator_ne_zero (r : Coeff ⊤) {c : ℝ} {N : ℕ}
    (hc : 0 < c) (hsep : AppendixDReferenceSeparated r c N)
    {n m : ℤ} (hn : N ≤ n.natAbs) (hmn : m ≠ n)
    {z : ℂ} (hz : z ∈ refinedResonantDisk n) : displacedRoots r m-z ≠ 0 := by
  have h := hsep n hn z hz m hmn
  have hd : 0 < |((m-n:ℤ):ℝ)| := by
    apply abs_pos.mpr
    exact_mod_cast sub_ne_zero.mpr hmn
  exact norm_pos_iff.mp ((mul_pos (inv_pos.mpr hc) hd).trans_le h)

omit [Fact (1 ≤ p)] in
/-- The literal ratios equal their one-plus-perturbation factors. -/
theorem appendixDRelativeProductError_eq (r : Coeff ⊤) (a : Coeff p)
    {c : ℝ} {N : ℕ} (hc : 0 < c) (hsep : AppendixDReferenceSeparated r c N)
    {n : ℤ} (hn : N ≤ n.natAbs) {z : ℂ} (hz : z ∈ refinedResonantDisk n) :
    appendixDRelativeProductError r a n z =
      (∏' m : ℤ, (1+(if m = n then 0 else a m/(displacedRoots r m-z))))-1 := by
  unfold appendixDRelativeProductError
  congr 1
  apply tprod_congr
  intro m
  by_cases hmn : m = n
  · simp [hmn]
  have hd := appendixD_reference_denominator_ne_zero r hc hsep hn hmn hz
  simp only [if_neg hmn]
  field_simp
  ring

/-- The source separation persists when the cutoff is increased. -/
theorem AppendixDReferenceSeparated.mono (r : Coeff ⊤) {c : ℝ} {N K : ℕ}
    (hsep : AppendixDReferenceSeparated r c N) (hNK : N ≤ K) :
    AppendixDReferenceSeparated r c K :=
  fun n hn => hsep n (hNK.trans hn)

/-- Every retained relative product is convergent, even if a numerator vanishes. -/
theorem multipliable_appendixDRelativeProduct (hp1 : 1 < p) (hp : p ≠ ⊤)
    (r : Coeff ⊤) (a : Coeff p) {c : ℝ} {N : ℕ}
    (hc : 0 < c) (hsep : AppendixDReferenceSeparated r c N)
    {n : ℤ} (hn : N ≤ n.natAbs) {w : ℂ} (hw : w ∈ refinedResonantDisk n) :
    Multipliable (fun m : ℤ => if m = n then 1 else
      (displacedRoots r m+a m-w)/(displacedRoots r m-w)) := by
  classical
  let z : ℤ → ℂ := fun k => if k = n then w else (Real.pi:ℂ)*k
  have hz (k : ℤ) : z k ∈ refinedResonantDisk k := by
    by_cases hk : k = n
    · simpa [z,hk] using hw
    · simp only [z,if_neg hk,refinedResonantDisk,mem_ball,dist_self]
      positivity
  have hs := appendixD_separatedReciprocalRows r hc (norm_nonneg r) le_rfl hsep z
    (fun k _ => hz k)
  have hf : ∀ k ∈ {k : ℤ | N ≤ k.natAbs}, ‖z k-(Real.pi:ℂ)*k‖ ≤ Real.pi/4 := by
    intro k _
    exact (show ‖z k-(Real.pi:ℂ)*k‖ < Real.pi/4 by
      simpa only [refinedResonantDisk,mem_ball,dist_eq_norm] using hz k).le
  have hsum := summable_norm_physicalReciprocalRow hp1 hp hs hf a hn
  have hsum' : Summable (fun m : ℤ => ‖if m = n then 0 else a m/(displacedRoots r m-w)‖) := by
    simpa only [z,if_pos rfl] using hsum
  apply (multipliable_one_add_of_summable hsum').congr
  intro m
  by_cases hmn : m = n
  · simp [hmn]
  have hd := appendixD_reference_denominator_ne_zero r hc hsep hn hmn hw
  simp only [if_neg hmn]
  field_simp
  ring

/-- One coefficient-space bound works for all independent choices of points in the distant discs. -/
theorem exists_appendixDRelativeProductRows (hp1 : 1 < p) (hp : p ≠ ⊤)
    (r : Coeff ⊤) (a : Coeff p) {c B : ℝ} {N : ℕ}
    (hc : 0 < c) (hB : 0 ≤ B) (hr : ‖r‖ ≤ B)
    (hsep : AppendixDReferenceSeparated r c N) (z : ℤ → ℂ)
    (hz : ∀ n : ℤ, N ≤ n.natAbs → z n ∈ refinedResonantDisk n) :
    ∃ b : Coeff p,
      (∀ n : ℤ, N ≤ n.natAbs → b n = appendixDRelativeProductError r a n (z n)) ∧
      ‖b‖ ≤ appendixDRelativeProductBound hp1 hp c B ‖a‖ := by
  have hs := appendixD_separatedReciprocalRows r hc hB hr hsep z hz
  have hf : ∀ n ∈ {n : ℤ | N ≤ n.natAbs}, ‖z n-(Real.pi:ℂ)*n‖ ≤ Real.pi/4 := by
    intro n hn
    exact (show ‖z n-(Real.pi:ℂ)*n‖ < Real.pi/4 by
      simpa only [refinedResonantDisk, mem_ball, dist_eq_norm] using hz n hn).le
  let L := physicalReciprocalRows hp1 hp hs hf a
  let E := physicalMidpointProductRemainder hp hs a
  refine ⟨L+E,?_,?_⟩
  · intro n hn
    rw [lp.coeFn_add, Pi.add_apply, appendixDRelativeProductError_eq r a hc hsep hn (hz n hn)]
    have hL := physicalReciprocalRows_apply hp1 hp hs hf a hn
    change L n + ((∏' m : ℤ, (1+physicalMidpointTerm _ _ _ a n m))-1-
      ∑' m : ℤ, physicalMidpointTerm _ _ _ a n m) = _
    simp only [physicalMidpointTerm, Set.mem_ofPred_eq, if_pos hn]
    dsimp [L]
    rw [hL]
    ring
  · exact (norm_add_le L E).trans (add_le_add
      (norm_physicalReciprocalRows_le hp1 hp hs hf a)
      (norm_physicalMidpointProductRemainder_le hp hs a))

end NLS.ZakharovShabat
