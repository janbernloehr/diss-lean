import NLS.ZakharovShabat.AppendixDRelativeProductSup
import NLS.Fourier.SquaredAbsoluteRows
import NLS.ComplexAnalysis.GlobalSignedProductRemainder

/-! # Signed and squared rows on the source discs of Appendix D -/
noncomputable section
open Set Metric
open scoped ENNReal
open NLS.Fourier
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
local instance : Fact (1 ≤ 2*p) := ⟨one_le_double_exponent Fact.out⟩

/-- The retained reciprocal factor, with the omitted index set to zero. -/
def appendixDReciprocalTerm (r : Coeff ⊤) (a : Coeff p) (n : ℤ) (z : ℂ) (m : ℤ) : ℂ :=
  if m = n then 0 else a m/(displacedRoots r m-z)

/-- Absolute convergence, a uniform absolute-sum bound, and pointwise separation. -/
theorem appendixDReciprocalTerm_bounds (hp : p ≠ ⊤)
    (r : Coeff ⊤) (a : Coeff p) {c : ℝ} {N : ℕ}
    (hc : 0 < c) (hsep : AppendixDReferenceSeparated r c N)
    {n : ℤ} (hn : N ≤ n.natAbs) {w : ℂ} (hw : w ∈ refinedResonantDisk n) :
    Summable (fun m => ‖appendixDReciprocalTerm r a n w m‖) ∧
      (∑' m, ‖appendixDReciprocalTerm r a n w m‖) ≤
        (c/2)*absoluteSampledRowConstant hp*‖a‖ ∧
      ∀ m, ‖appendixDReciprocalTerm r a n w m‖ ≤ c*(‖a m‖*‖hilbertKernel (n-m)‖) := by
  classical
  let z : ℤ → ℂ := fun k => if k = n then w else (Real.pi:ℂ)*k
  have hz (k : ℤ) : z k ∈ refinedResonantDisk k := by
    by_cases hk : k = n
    · simpa [z,hk] using hw
    · simp only [z,if_neg hk,refinedResonantDisk,mem_ball,dist_self]
      positivity
  have hs := appendixD_separatedReciprocalRows r hc (norm_nonneg r) le_rfl hsep z
    (fun k _ => hz k)
  have he (m : ℤ) : physicalMidpointTerm {k : ℤ | N ≤ k.natAbs} (displacedRoots r) z a n m =
      appendixDReciprocalTerm r a n w m := by
    simp only [physicalMidpointTerm,Set.mem_ofPred_eq,if_pos hn,z,if_pos rfl,appendixDReciprocalTerm]
  refine ⟨by simpa only [he] using summable_norm_physicalMidpointTerm hp hs a n,?_,?_⟩
  · have hb := tsum_norm_physicalMidpointTerm_le_majorant hp hs a n
    simp only [he] at hb
    apply hb.trans
    apply (lp.norm_apply_le_norm (ne_of_gt (zero_lt_one.trans_le (Fact.out : 1 ≤ 2*p))) _ n).trans
    rw [physicalMidpointAbsoluteMajorant,norm_smul,Complex.norm_real,
      Real.norm_of_nonneg (by positivity : 0 ≤ c/2)]
    exact (mul_le_mul_of_nonneg_left (norm_absoluteSampledRowMajorant_le hp a)
      (by positivity : 0 ≤ c/2)).trans_eq (by ring)
  · intro m
    simpa only [he] using norm_physicalMidpointTerm_le hs a hn m

/-- The uniform signed row norm on bounded reference displacements. -/
def appendixDSignedRowConstant (hp1 : 1 < p) (hp : p ≠ ⊤) (c B : ℝ) : ℝ :=
  Real.pi⁻¹*(hilbertTransformBound hp1 hp+‖hilbertSquareCoeffs‖)+c*B*‖hilbertSquareCoeffs‖

/-- One ell-p sequence controls the signed sum on every selected disc. -/
theorem exists_appendixDSignedRowSup (hp1 : 1 < p) (hp : p ≠ ⊤)
    (r : Coeff ⊤) (a : Coeff p) {c B : ℝ} {N : ℕ}
    (hc : 0 < c) (hB : 0 ≤ B) (hr : ‖r‖ ≤ B)
    (hsep : AppendixDReferenceSeparated r c N) :
    ∃ L : Coeff p,
      (∀ n : ℤ, N ≤ n.natAbs → ∀ w ∈ refinedResonantDisk n,
        ‖∑' m, appendixDReciprocalTerm r a n w m‖ ≤ ‖L n‖) ∧
      ‖L‖ ≤ appendixDSignedRowConstant hp1 hp c B*‖a‖ := by
  have hD (n : ℤ) : (refinedResonantDisk n).Nonempty := by
    refine ⟨(Real.pi:ℂ)*n,?_⟩
    simp only [refinedResonantDisk,mem_ball,dist_self]
    positivity
  have hK : 0 ≤ appendixDSignedRowConstant hp1 hp c B*‖a‖ := by
    have hH := hilbertTransformBound_nonneg hp1 hp
    unfold appendixDSignedRowConstant
    positivity
  have hsel (z : ℤ → ℂ) (hz : ∀ n, z n ∈ refinedResonantDisk n) :
      ∃ b : Coeff p,
        (∀ n ∈ {n : ℤ | N ≤ n.natAbs}, b n = ∑' m, appendixDReciprocalTerm r a n (z n) m) ∧
        ‖b‖ ≤ appendixDSignedRowConstant hp1 hp c B*‖a‖ := by
    have hs := appendixD_separatedReciprocalRows r hc hB hr hsep z (fun n _ => hz n)
    have hf : ∀ n ∈ {n : ℤ | N ≤ n.natAbs}, ‖z n-(Real.pi:ℂ)*n‖ ≤ Real.pi/4 := by
      intro n _
      exact (show ‖z n-(Real.pi:ℂ)*n‖ < Real.pi/4 by
        simpa only [refinedResonantDisk,mem_ball,dist_eq_norm] using hz n).le
    exact ⟨physicalReciprocalRows hp1 hp hs hf a,
      (fun _ hn => physicalReciprocalRows_apply hp1 hp hs hf a hn),
      norm_physicalReciprocalRows_le hp1 hp hs hf a⟩
  obtain ⟨L,hL,_,_,hLn⟩ := NLS.exists_uniformSelectionSup hp {n : ℤ | N ≤ n.natAbs}
    refinedResonantDisk hD (fun n w => ∑' m, appendixDReciprocalTerm r a n w m)
    _ hK hsel
  exact ⟨L,hL,hLn⟩

/-- The square row is controlled by a single half-exponent sequence on all the discs. -/
theorem exists_appendixDSquaredRowSup (hp1 : 1 < p) (hp : p ≠ ⊤)
    (r : Coeff ⊤) (a : Coeff p) {c : ℝ} {N : ℕ}
    (hc : 0 < c) (hsep : AppendixDReferenceSeparated r c N) :
    ∃ Q : Coeff (p/2),
      (∀ n : ℤ, N ≤ n.natAbs → ∀ w ∈ refinedResonantDisk n,
        (∑' m, ‖appendixDReciprocalTerm r a n w m‖^2) ≤ c^2*‖Q n‖) ∧
      ‖Q‖ ≤ ‖a‖^2*squaredAbsoluteRowConstant hp1 hp := by
  obtain ⟨Q,hQ,hQn⟩ := exists_squaredAbsoluteRows hp1 hp a
  refine ⟨Q,?_,hQn⟩
  intro n hn w hw
  obtain ⟨hs,_,hpoint⟩ := appendixDReciprocalTerm_bounds hp r a hc hsep hn hw
  have hsquare := NLS.ComplexAnalysis.summable_sq_norm_of_summable_norm
    (appendixDReciprocalTerm r a n w) hs
  have hdom (m : ℤ) : ‖appendixDReciprocalTerm r a n w m‖^2 ≤
      c^2*(‖a m‖^2*‖hilbertKernel (n-m)‖^2) := by
    calc
      _ ≤ (c*(‖a m‖*‖hilbertKernel (n-m)‖))^2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hpoint m) 2
      _ = _ := by ring
  have h := hsquare.tsum_le_tsum hdom ((hQ n).1.mul_left (c^2))
  rw [tsum_mul_left] at h
  rw [(hQ n).2,Complex.norm_real,Real.norm_of_nonneg
    (tsum_nonneg (fun _ => by positivity))]
  exact h

end NLS.ZakharovShabat
