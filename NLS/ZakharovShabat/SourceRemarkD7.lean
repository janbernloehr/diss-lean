import NLS.ZakharovShabat.AppendixDQuadraticRemainder
import NLS.ZakharovShabat.SourceLemmaD6
import NLS.SequenceSpaces.OnePlus

/-! # The literal remainder in Remark D.7

The remainder after subtracting the signed reciprocal sum has a disc
supremum in ell-(p/2). This implies the printed sum-space assertion with
zero ell-(1+) component. As in D.6, only the separated distant discs are
selected; the sequence is extended by zero over the omitted finite head.
-/
noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The exact product-minus-linear-sum expression printed in D.7. -/
def sourceRemarkD7Remainder (r s : Coeff ⊤) (n : ℤ) (z : ℂ) : ℂ :=
  (∏' m : ℤ, if m = n then 1 else
    (displacedRoots s m-z)/(displacedRoots r m-z))-1-
    ∑' m : ℤ, if m = n then 0 else
      (displacedRoots s m-displacedRoots r m)/(displacedRoots r m-z)

omit [Fact (1 ≤ p)] in
/-- Subtracting the displacement sum is exactly subtracting the source root-difference sum. -/
theorem sourceRemarkD7Remainder_eq (r s : Coeff ⊤)
    (h : Memℓp (fun m : ℤ => s m-r m) p) (n : ℤ) (z : ℂ) :
    sourceRemarkD7Remainder r s n z =
      appendixDQuadraticRemainder r (appendixDDisplacementDifference r s h) n z := by
  rw [appendixDQuadraticRemainder,appendixDRelativeProductError_difference]
  unfold sourceRemarkD7Remainder
  congr 1
  apply tsum_congr
  intro m
  have he : displacedRoots s m-displacedRoots r m =
      appendixDDisplacementDifference r s h m := by
    change (Real.pi:ℂ)*m+s m-((Real.pi:ℂ)*m+r m) = s m-r m
    ring
  simp only [appendixDReciprocalTerm,he]

/-- The literal norm supremum over every selected open source disc. -/
def sourceRemarkD7Sup (r s : Coeff ⊤) (N : ℕ) (n : ℤ) : ℝ :=
  if N ≤ n.natAbs then
    sSup ((fun z => ‖sourceRemarkD7Remainder r s n z‖) '' refinedResonantDisk n)
  else 0

omit [Fact (1 ≤ p)] in
/-- Identification of the source and perturbation disc suprema. -/
theorem sourceRemarkD7Sup_eq (r s : Coeff ⊤)
    (h : Memℓp (fun m : ℤ => s m-r m) p) (N : ℕ) :
    sourceRemarkD7Sup r s N =
      appendixDQuadraticSup r (appendixDDisplacementDifference r s h) N := by
  funext n
  simp only [sourceRemarkD7Sup,appendixDQuadraticSup,sourceRemarkD7Remainder_eq r s h]

/-- The stronger half-exponent bound, uniform on both norm balls and for every later cutoff. -/
theorem sourceRemarkD7_uniform (hp1 : 1 < p) (hp : p ≠ ⊤)
    {c B A : ℝ} (hc : 0 < c) (hB : 0 ≤ B) (_hA : 0 ≤ A) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (r s : Coeff ⊤) (h : Memℓp (fun m : ℤ => s m-r m) p) (N K : ℕ),
      ‖r‖ ≤ B → ‖appendixDDisplacementDifference r s h‖ ≤ A →
      AppendixDReferenceSeparated r c N → N ≤ K →
      ∃ b : Coeff (p/2), (∀ n, b n = ((sourceRemarkD7Sup r s K n):ℂ)) ∧ ‖b‖ ≤ C := by
  have hbound : 0 ≤ appendixDQuadraticBound hp1 hp c B A := by
    unfold appendixDQuadraticBound
    have hQ : 0 ≤ NLS.Fourier.squaredAbsoluteRowConstant hp1 hp := lp.norm_nonneg' _
    positivity
  refine ⟨1+appendixDQuadraticBound hp1 hp c B A,by linarith,?_⟩
  intro r s h N K hr ha hsep hNK
  obtain ⟨b,hb,hbn⟩ := exists_appendixDQuadraticSup hp1 hp r
    (appendixDDisplacementDifference r s h) hc hB hr ha (hsep.mono r hNK)
  exact ⟨b,(by simpa only [sourceRemarkD7Sup_eq r s h K] using hb),by linarith⟩

/-- Half-exponent membership of the literal disc supremum. -/
theorem sourceRemarkD7_mem (hp1 : 1 < p) (hp : p ≠ ⊤)
    (r s : Coeff ⊤) (h : Memℓp (fun m : ℤ => s m-r m) p)
    {c : ℝ} {N : ℕ} (hc : 0 < c) (hsep : AppendixDReferenceSeparated r c N) :
    Memℓp (fun n => ((sourceRemarkD7Sup r s N n):ℂ)) (p/2) := by
  obtain ⟨b,hb,_⟩ := exists_appendixDQuadraticSup hp1 hp r
    (appendixDDisplacementDifference r s h) hc (norm_nonneg r) le_rfl le_rfl hsep
  have he : (fun n => ((sourceRemarkD7Sup r s N n):ℂ)) = ⇑b := by
    funext n
    rw [sourceRemarkD7Sup_eq r s h N]
    exact (hb n).symm
  rw [he]
  exact lp.memℓp b

/-- Remark D.7's printed ell-(p/2) plus ell-(1+) decomposition.
One common second component works for every exponent strictly above one. -/
theorem sourceRemarkD7 (hp1 : 1 < p) (hp : p ≠ ⊤)
    (r s : Coeff ⊤) (h : Memℓp (fun m : ℤ => s m-r m) p)
    {c : ℝ} {N : ℕ} (hc : 0 < c) (hsep : AppendixDReferenceSeparated r c N) :
    ∃ u : Coeff (p/2), ∃ v : CoeffOnePlus,
      ∀ n : ℤ, ((sourceRemarkD7Sup r s N n):ℂ) = u n+v.1 n := by
  refine ⟨⟨_,sourceRemarkD7_mem hp1 hp r s h hc hsep⟩,0,?_⟩
  intro n
  simp

end NLS.ZakharovShabat
