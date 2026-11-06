import NLS.ZakharovShabat.PeriodicSpectrum
import NLS.SequenceSpaces.ShiftedWeight

/-! # Exact Fourier modulation of the original Dirac operator

Opposite shifts of the two domain components intertwine the actual
operator with an exact constant spectral translation. The derivative
domain and the original convolution potential are retained.
-/
noncomputable section
set_option autoImplicit false
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

private def domainSpectralWeight : SpectralWeight where
  toWeight := Weight.sobolev 1
  one_le n := by change 1≤(1+|(n : ℝ)|)^1; rw [Real.rpow_one]; exact le_add_of_nonneg_right (abs_nonneg _)
  neg_eq n := by change (1+|((-n : ℤ) : ℝ)|)^1=(1+|(n : ℝ)|)^1; simp
  add_le m n := by
    change (1+|((m+n : ℤ) : ℝ)|)^1≤(1+|(m : ℝ)|)^1*(1+|(n : ℝ)|)^1
    simp only [Real.rpow_one,Int.cast_add]
    nlinarith [abs_add_le (m : ℝ) n,mul_nonneg (abs_nonneg (m : ℝ)) (abs_nonneg (n : ℝ))]
  monotone_nat := by
    intro m n h
    change (1+|((m : ℤ) : ℝ)|)^1≤(1+|((n : ℤ) : ℝ)|)^1
    simpa only [Real.rpow_one,Int.cast_natCast,Nat.abs_cast,add_le_add_iff_left] using (Nat.cast_le.mpr h : (m : ℝ)≤n)

/-- Opposite Fourier shifts on the original period-two base space. -/
def pairSpectralModulation (n : ℤ) : PairSpace p ≃ₗᵢ[ℂ] PairSpace p where
  __ := (Coeff.shift (-n)).toLinearEquiv.prodCongr (Coeff.shift n).toLinearEquiv
  norm_map' a := by simp [Prod.norm_def]

/-- Opposite Fourier shifts preserve the actual derivative domain. -/
def domainSpectralModulation (n : ℤ) : Domain p ≃L[ℂ] Domain p :=
  (SpectralWeight.modulation domainSpectralWeight (-n)).prodCongr
    (SpectralWeight.modulation domainSpectralWeight n)

@[simp] theorem domainSpectralModulation_fst (n j : ℤ) (f : Domain p) :
    (domainSpectralModulation n f).1.val j=f.1.val (j+n) := by
  change (SpectralWeight.modulation domainSpectralWeight (-n) f.1).val j=_
  simpa only [sub_neg_eq_add] using! SpectralWeight.modulation_apply domainSpectralWeight (-n) f.1 j

@[simp] theorem domainSpectralModulation_snd (n j : ℤ) (f : Domain p) :
    (domainSpectralModulation n f).2.val j=f.2.val (j-n) :=
  SpectralWeight.modulation_apply domainSpectralWeight n f.2 j

@[simp] theorem pairSpectralModulation_fst (n j : ℤ) (f : PairSpace p) :
    (pairSpectralModulation n f).1 j=f.1 (j+n) := by
  change Coeff.shift (-n) f.1 j=_
  rw [Coeff.shift_apply,sub_neg_eq_add]

@[simp] theorem pairSpectralModulation_snd (n j : ℤ) (f : PairSpace p) :
    (pairSpectralModulation n f).2 j=f.2 (j-n) := rfl

theorem domainInclusion_spectralModulation (n : ℤ) (f : Domain p) :
    domainInclusion (domainSpectralModulation n f)=pairSpectralModulation n (domainInclusion f) := by
  apply Prod.ext <;> ext j <;>
    simp only [domainInclusion_apply,scalarInclusion_apply,domainSpectralModulation_fst,
      domainSpectralModulation_snd,pairSpectralModulation_fst,pairSpectralModulation_snd]

private theorem tsum_spectralModulation (a b : ℤ → ℂ) (i k j : ℤ) :
    (∑' m : ℤ, a (j-m-i)*b (m-k))=∑' m : ℤ, a (j-(i+k)-m)*b m := by
  calc
    _ = ∑' m : ℤ, a (j-(m+k)-i)*b (m+k-k) :=
      ((Equiv.addRight k).tsum_eq (fun m : ℤ => a (j-m-i)*b (m-k))).symm
    _ = _ := by
      apply tsum_congr
      intro m
      rw [add_sub_cancel_right,show j-(m+k)-i=j-(i+k)-m by omega]

/-- The original operator is intertwined with a constant spectral shift. -/
theorem operator_spectralModulation (hp : p≠⊤) (n : ℤ) (φ : PairSpace p) (f : Domain p) :
    operator hp (pairSpectralModulation (2*n) φ) (domainSpectralModulation n f)=
      pairSpectralModulation n (operator hp φ f)+
        ((Real.pi : ℂ)*n) • pairSpectralModulation n (domainInclusion f) := by
  apply Prod.ext <;> ext j
  · simp only [operator_fst_apply,pairSpectralModulation_fst,domainSpectralModulation_fst,
      domainSpectralModulation_snd,Prod.fst_add,Prod.smul_fst,lp.coeFn_add,Pi.add_apply,
      lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,domainInclusion_apply,scalarInclusion_apply]
    have hsum : (∑' k : ℤ, φ.1 (j-k+2*n)*f.2.val (k-n))=
        ∑' k : ℤ, φ.1 (j+n-k)*f.2.val k := by
      simpa only [sub_neg_eq_add,show j-(-(2*n)+n)=j+n by omega] using
        tsum_spectralModulation φ.1 f.2.val (-(2*n)) n j
    rw [hsum]
    push_cast
    ring
  · simp only [operator_snd_apply,pairSpectralModulation_snd,domainSpectralModulation_fst,
      domainSpectralModulation_snd,Prod.snd_add,Prod.smul_snd,lp.coeFn_add,Pi.add_apply,
      lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,domainInclusion_apply,scalarInclusion_apply]
    have hsum : (∑' k : ℤ, φ.2 (j-k-2*n)*f.1.val (k+n))=
        ∑' k : ℤ, φ.2 (j-n-k)*f.1.val k := by
      simpa only [sub_neg_eq_add,show j-(2*n+-n)=j-n by omega] using
        tsum_spectralModulation φ.2 f.1.val (2*n) (-n) j
    rw [hsum]
    push_cast
    ring

/-- Every original eigenvalue is transported to the exact translated
spectral point, with a genuine nonzero eigenvector in the SAME domain. -/
theorem mem_periodicSpectrum_spectralModulation (hp : p≠⊤) (n : ℤ) (φ : PairSpace p)
    (z : ℂ) (hz : z∈periodicSpectrum hp φ) :
    z+(Real.pi : ℂ)*n ∈ periodicSpectrum hp (pairSpectralModulation (2*n) φ) := by
  obtain ⟨f,hf,he⟩ := (mem_periodicSpectrum_iff_exists_eigenvector hp φ z).mp hz
  apply (mem_periodicSpectrum_iff_exists_eigenvector hp _ _).mpr
  refine ⟨domainSpectralModulation n f,?_,?_⟩
  · intro h
    exact hf ((domainSpectralModulation n).injective (h.trans (map_zero _).symm))
  · rw [operator_spectralModulation,he,map_smul,domainInclusion_spectralModulation,add_smul]

end NLS.ZakharovShabat
