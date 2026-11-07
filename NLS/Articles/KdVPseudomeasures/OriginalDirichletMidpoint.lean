import NLS.Articles.KdVPseudomeasures.OriginalDirichletLabels
import NLS.Articles.KdVPseudomeasures.SpectralWeightedGaps
import NLS.SequenceSpaces.FiniteTailDomination

/-! Actual original Dirichlet midpoint errors at every real potential.
The complete ordered characteristic labels are used, including all central
indices. Real high-gap inclusion transfers arbitrary weighted gap regularity.
The FULL COMPLEX local-boundedness clause of source 2.1(ii) remains separate. -/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue NLS.KdV

/-- Exact original tau_n minus mu_n, evenly extended with zero at index zero. -/
def originalDirichletMidpointValues (q : OriginalHminusOnePotential) (k : ℤ) : ℂ :=
  if hk : k = 0 then 0 else
    (((originalHillLabels q (2*k.natAbs-1)+originalHillLabels q (2*k.natAbs))/2:ℝ):ℂ)-
      (originalDirichletLabels q ⟨k.natAbs,Int.natAbs_pos.mpr hk⟩:ℂ)

@[simp] theorem originalDirichletMidpointValues_zero (q : OriginalHminusOnePotential) :
    originalDirichletMidpointValues q 0 = 0 := by simp [originalDirichletMidpointValues]

theorem originalDirichletMidpointValues_neg (q : OriginalHminusOnePotential) (k : ℤ) :
    originalDirichletMidpointValues q (-k) = originalDirichletMidpointValues q k := by
  simp only [originalDirichletMidpointValues,neg_eq_zero,Int.natAbs_neg]

/-- One cutoff controls the actual full midpoint errors on BOTH signed
tails by one half of the exact original periodic gap norm. -/
theorem exists_originalDirichletMidpoint_half_gap_bound (q : OriginalHminusOnePotential) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ k : ℤ, N ≤ k.natAbs →
      ‖originalDirichletMidpointValues q k‖ ≤ ‖originalCanonicalGapValues q k‖/2 := by
  obtain ⟨N,hN,hgap⟩ := exists_originalDirichletLabels_in_high_gap q
  refine ⟨N,hN,fun k hk => ?_⟩
  have hk0 : k ≠ 0 := by intro hz; subst k; simp at hk; omega
  have h := (hgap ⟨k.natAbs,Int.natAbs_pos.mpr hk0⟩ hk).2.2
  simpa only [originalDirichletMidpointValues,dif_neg hk0,
    originalCanonicalGapValues,if_neg hk0] using! h

/-- ANY complex scalar weight and ANY exponent transfer original real
gap regularity to the complete actual Dirichlet midpoint sequence.
The finite central block is handled by finite modification. -/
theorem memlp_originalDirichletMidpoint_of_gap (q : OriginalHminusOnePotential)
    (a : ℤ → ℂ) {p : ℝ≥0∞}
    (hgap : Memℓp (fun k => a k*originalCanonicalGapValues q k) p) :
    Memℓp (fun k => a k*originalDirichletMidpointValues q k) p := by
  obtain ⟨N,_,hbound⟩ := exists_originalDirichletMidpoint_half_gap_bound q
  apply memlp_of_natAbs_tail_norm_le
    (fun k => a k*originalDirichletMidpointValues q k)
    (fun k => a k*originalCanonicalGapValues q k) hgap N (1/2) (by norm_num)
  intro k hk
  rw [norm_mul,norm_mul]
  have h := mul_le_mul_of_nonneg_left (hbound k hk) (norm_nonneg (a k))
  simpa only [div_eq_mul_inv,one_mul,mul_assoc,mul_left_comm,mul_comm] using h

/-- Real characteristic-label weighted midpoint membership needed for
source Theorem 2.1(ii), with the ENTIRE original distribution unchanged.
Native scalar operator identification and full complex local boundedness
are not claimed by this membership result. -/
theorem originalDirichletMidpoint_real_weighted_membership (w : SpectralWeight) (r : ℝ)
    (hr : AdmissiblePredualOrder r)
    (q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤)
    (hq : q.val.IsRealMeanZeroPeriodOne) :
    let z : Potential r := ⟨sourceForgetWeight w r q,by rwa [sourceForgetWeight_val]⟩
    Memℓp (fun k => (w.negativeSobolev r k:ℂ)*
      originalDirichletMidpointValues (sourceOriginalPotential r hr z) k) ⊤ := by
  let z : Potential r := ⟨sourceForgetWeight w r q,by rwa [sourceForgetWeight_val]⟩
  apply memlp_originalDirichletMidpoint_of_gap (sourceOriginalPotential r hr z)
    (fun k => (w.negativeSobolev r k:ℂ))
  have h := sourceWeightedCanonicalGapValues_mem w r hr q
  convert! h using 1
  funext k
  rw [originalCanonicalGapValues_sourceOriginalPotential]
  exact congrArg (fun t : ℂ => (w.negativeSobolev r k:ℂ)*t)
    (sourceComplexCanonicalGapValues_ofPotential r hr z k).symm

end NLS.Articles.KdVPseudomeasures
