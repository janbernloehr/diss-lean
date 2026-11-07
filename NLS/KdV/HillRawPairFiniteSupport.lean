import NLS.KdV.HillRoughFinitePairRegularity

/-! Finite RAW signed Hilbert pair targets force finite positive
coordinates. The existing nonlinear regularity theorem then supplies
every original native Sobolev source, with unchanged raw coefficients. -/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.Articles.KdVKdV2Frequencies
namespace NLS.KdV

theorem positive_zero_of_raw_pair_zero
    (D : GlobalRoughAbelianForwardData) (e : ℤ ≃ ℕ+)
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (z : Coeff 2 × Coeff 2)
    (hi : ∀ j : ℤ, (D.signed q).val j=(signedPairToDeleted e z).val j)
    (k : ℤ) (hx : z.1 k=0) (hy : z.2 k=0) : D.positive q (positiveIndexInjection e k)=0 := by
  have H := hi (positiveIndexInjection e k)
  rw [D.signed_positive_real q hr _ (by dsimp only [positiveIndexInjection];exact_mod_cast (e k).pos),
    signedPairToDeleted_positive,hx,hy,mul_zero,sub_zero,zero_div] at H
  exact (div_eq_zero_iff.mp H).resolve_right (Weight.complex_ne_zero _ _)

theorem positive_finiteSupport_of_raw_pair_inverse
    (D : GlobalRoughAbelianForwardData) (e : ℤ ≃ ℕ+)
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q)
    (z : Coeff 2 × Coeff 2)
    (hi : ∀ j : ℤ, (D.signed q).val j=(signedPairToDeleted e z).val j)
    (S : Finset ℤ) (hz : ∀ k : ℤ, k∉S → z.1 k=0 ∧ z.2 k=0) :
    (Function.support (D.positive q)).Finite := by
  apply (S.finite_toSet.image (positiveIndexInjection e)).subset
  intro j hj
  have hjpos : 0<j := by
    by_contra h
    exact hj (D.positive_zero q (D.real_mem_domain q hr) j (by omega))
  let k := e.symm (⟨j.toNat,by omega⟩ : ℕ+)
  have hkj : positiveIndexInjection e k=j := by
    have he := congrArg (fun n : ℕ+ => ((n : ℕ) : ℤ))
      (e.apply_symm_apply (⟨j.toNat,by omega⟩ : ℕ+))
    exact he.trans (Int.toNat_of_nonneg hjpos.le)
  have hk : k∈S := by
    by_contra h
    obtain ⟨hx,hy⟩ := hz k h
    apply hj
    rw [←hkj]
    exact positive_zero_of_raw_pair_zero D e q hr z hi k hx hy
  exact ⟨k,hk,hkj⟩

end NLS.KdV
