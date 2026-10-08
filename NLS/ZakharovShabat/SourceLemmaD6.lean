import NLS.ZakharovShabat.AppendixDRelativeProductBounds

/-! # The source statement of Lemma D.6

Two arbitrary bounded displacements r and s are allowed. Their difference
belongs to ell-p, 1 < p < infinity. The reference sequence obeys the source
separation on every distant free disc. Constants are uniform on norm balls,
and every later cutoff is allowed. Simplicity of the reference sequence and
the printed additional small-tail condition are unnecessary for these bounds.
-/
noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The literal difference of two bounded root displacements in the finite exponent. -/
def appendixDDisplacementDifference (r s : Coeff ⊤)
    (h : Memℓp (fun m : ℤ => s m-r m) p) : Coeff p := ⟨fun m => s m-r m,h⟩

omit [Fact (1 ≤ p)] in
/-- Reconstructing the numerator roots gives precisely the source quotient. -/
theorem appendixDRelativeProductError_difference (r s : Coeff ⊤)
    (h : Memℓp (fun m : ℤ => s m-r m) p) (n : ℤ) (z : ℂ) :
    appendixDRelativeProductError r (appendixDDisplacementDifference r s h) n z =
      (∏' m : ℤ, if m = n then 1 else (displacedRoots s m-z)/(displacedRoots r m-z))-1 := by
  unfold appendixDRelativeProductError
  congr 1
  apply tprod_congr
  intro m
  have he : displacedRoots r m+appendixDDisplacementDifference r s h m = displacedRoots s m := by
    change (Real.pi:ℂ)*m+r m+(s m-r m) = (Real.pi:ℂ)*m+s m
    ring
  rw [he]

/-- Literal source ratios are convergent at every point of every selected disc. -/
theorem sourceLemmaD6_multipliable (hp1 : 1 < p) (hp : p ≠ ⊤)
    (r s : Coeff ⊤) (hdiff : Memℓp (fun m : ℤ => s m-r m) p)
    {c : ℝ} {N : ℕ} (hc : 0 < c) (hsep : AppendixDReferenceSeparated r c N)
    {n : ℤ} (hn : N ≤ n.natAbs) {z : ℂ} (hz : z ∈ refinedResonantDisk n) :
    Multipliable (fun m : ℤ => if m = n then 1 else
      (displacedRoots s m-z)/(displacedRoots r m-z)) := by
  apply (multipliable_appendixDRelativeProduct hp1 hp r
    (appendixDDisplacementDifference r s hdiff) hc hsep hn hz).congr
  intro m
  have he : displacedRoots r m+appendixDDisplacementDifference r s hdiff m = displacedRoots s m := by
    change (Real.pi:ℂ)*m+r m+(s m-r m) = (Real.pi:ℂ)*m+s m
    ring
  rw [he]

/-- The exact summands printed in D.6, zero outside the selected tail. -/
def sourceLemmaD6PowerSup (r s : Coeff ⊤) (p : ℝ≥0∞) (N : ℕ) (n : ℤ) : ℝ :=
  if N ≤ n.natAbs then sSup ((fun z : ℂ =>
    ‖(∏' m : ℤ, if m = n then 1 else
      (displacedRoots s m-z)/(displacedRoots r m-z))-1‖^p.toReal) '' refinedResonantDisk n)
  else 0

omit [Fact (1 ≤ p)] in
/-- The abstract perturbation summands coincide with the literal source ones. -/
theorem sourceLemmaD6PowerSup_eq (r s : Coeff ⊤)
    (h : Memℓp (fun m : ℤ => s m-r m) p) (N : ℕ) :
    sourceLemmaD6PowerSup r s p N =
      appendixDRelativeProductPowerSup r (appendixDDisplacementDifference r s h) N := by
  funext n
  simp only [sourceLemmaD6PowerSup,appendixDRelativeProductPowerSup,
    appendixDRelativeProductError_difference]

/-- Lemma D.6 on bounded sets, including the literal linear-norm right side.
The constants are chosen before either displacement, the original cutoff,
or any later cutoff. This includes every cutoff meeting the printed condition. -/
theorem sourceLemmaD6 (hp1 : 1 < p) (hp : p ≠ ⊤)
    {c B A : ℝ} (hc : 0 < c) (hB : 0 ≤ B) (hA : 0 ≤ A) :
    ∃ C L : ℝ, 0 < C ∧ 0 < L ∧
      ∀ (r s : Coeff ⊤) (h : Memℓp (fun m : ℤ => s m-r m) p) (N K : ℕ),
      ‖r‖ ≤ B → ‖appendixDDisplacementDifference r s h‖ ≤ A →
      AppendixDReferenceSeparated r c N → N ≤ K →
      Summable (sourceLemmaD6PowerSup r s p K) ∧
      (∑' n : ℤ, sourceLemmaD6PowerSup r s p K n) ≤
        C*‖appendixDDisplacementDifference r s h‖^p.toReal ∧
      (∑' n : ℤ, sourceLemmaD6PowerSup r s p K n) ≤
        L*‖appendixDDisplacementDifference r s h‖ := by
  obtain ⟨C,L,hC,hL,hbound⟩ := appendixDRelativeProductPowerSup_normBall hp1 hp hc hB hA
  refine ⟨C,L,hC,hL,?_⟩
  intro r s h N K hr ha hsep hNK
  rw [sourceLemmaD6PowerSup_eq r s h K]
  exact hbound r (appendixDDisplacementDifference r s h) K hr ha (hsep.mono r hNK)

end NLS.ZakharovShabat
