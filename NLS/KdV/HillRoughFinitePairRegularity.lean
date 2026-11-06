import NLS.KdV.HillRoughPairInverse
import NLS.KdV.NativeHamiltonianIsospectral
import NLS.SequenceSpaces.PhysicalRealMeanZeroWeighted

/-! # Finite actual inverse-pair targets have every native Sobolev regularity -/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.Articles.KdVKdV2Frequencies
namespace NLS.KdV

theorem positive_finiteSupport_of_pair_inverse
    (D : GlobalRoughAbelianForwardData) (e : ℤ ≃ ℕ+)
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q)
    (z : Coeff 2 × Coeff 2)
    (hi : D.signed q = WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1/2))
      (signedPairToDeleted e z))
    (S : Finset ℤ) (hz : ∀ k : ℤ, k ∉ S → z.1 k=0 ∧ z.2 k=0) :
    (Function.support (D.positive q)).Finite := by
  apply (S.finite_toSet.image (positiveIndexInjection e)).subset
  intro j hj
  have hjpos : 0 < j := by
    by_contra h
    exact hj (D.positive_zero q (D.real_mem_domain q hr) j (by omega))
  let k := e.symm (⟨j.toNat,by omega⟩ : ℕ+)
  have hkj : positiveIndexInjection e k=j := by
    have he := congrArg (fun n : ℕ+ => ((n : ℕ) : ℤ))
      (e.apply_symm_apply (⟨j.toNat,by omega⟩ : ℕ+))
    exact he.trans (Int.toNat_of_nonneg hjpos.le)
  have hk : k ∈ S := by
    by_contra h
    obtain ⟨hx,hy⟩ := hz k h
    apply hj
    rw [←hkj,positive_eq_signedPair_of_inverse_identity D e q hr z hi k,hx,hy]
    simp only [mul_zero,sub_zero,zero_div]
  exact ⟨k,hk,hkj⟩

/-- Stronger source regularity is a conclusion of the proved nonlinear
regularity criterion. Every original raw coefficient is retained. -/
theorem exists_native_of_finite_positive_support
    (D : GlobalRoughAbelianForwardData) (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (hm : q.val 0=0)
    (hf : (Function.support (D.positive q)).Finite) (m : ℕ) :
    ∃ p : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (m : ℝ)),
      nativeHillSource m p.val=q := by
  have hweighted : (Function.support (fun j => (Weight.sobolev ((m : ℝ)+1) j : ℂ)*D.positive q j)).Finite := by
    apply hf.subset
    intro j hj hz
    apply hj
    change (Weight.sobolev ((m : ℝ)+1) j : ℂ)*D.positive q j=0
    exact mul_eq_zero_of_right _ hz
  have hmem := (D.sobolev_iff_positive_mem q hr (m : ℝ)
    (by have := Nat.cast_nonneg (α := ℝ) m; linarith)).mpr
      ((memℓp_zero_iff.mpr hweighted).of_exponent_ge bot_le)
  refine ⟨⟨⟨q.val,hmem⟩,hr,hm⟩,?_⟩
  apply Subtype.ext
  funext j
  exact nativeHillSource_apply m _ j

end NLS.KdV
