import NLS.KdV.NativeHamiltonianIsospectral
import NLS.SequenceSpaces.PhysicalRealMeanZeroWeightedTruncation
import NLS.SequenceSpaces.PhysicalRealMeanZeroWeightedRelift

/-! Literal finite Fourier approximants of every original real mean-zero
rough source belong to EVERY integer native Sobolev space. Their actual
rough inclusions converge in the entire original H-minus-one norm. -/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology NLS.ZakharovShabat
namespace NLS.KdV

/-- All-order native real approximants retain the original finite Fourier
coefficients and converge to the entire original mean-zero rough source. -/
theorem exists_native_real_meanZero_rough_approximants (m : ℕ)
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) (hm : q.val 0=0) :
    ∃ u : ℕ → physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (m : ℝ)),
      (∀ N j, (u N).val.val j=if j∈Finset.Icc (-(N : ℤ)) N then q.val j else 0) ∧
      Tendsto (fun N => nativeHillSource m (u N).val) atTop (𝓝 q) := by
  let p : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (-1)) := ⟨q,hq,hm⟩
  let v := fun N => physicalRealMeanZeroWeightedTruncate (Weight.sobolev (-1)) N p
  have hmem (N : ℕ) : Memℓp (fun j => (Weight.sobolev (m : ℝ) j : ℂ)*(v N).val.val j) 2 := by
    apply Memℓp.of_exponent_ge (q := 0) _ bot_le
    apply memℓp_zero_iff.mpr
    apply (Finset.finite_toSet (Finset.Icc (-(N : ℤ)) N)).subset
    intro j hj
    by_contra hout
    apply hj
    have hjN : j∉Finset.Icc (-(N : ℤ)) N := hout
    have hv : (v N).val.val j=0 :=
      (physicalRealMeanZeroWeightedTruncate_coefficient _ N p j).trans (if_neg hjN)
    exact mul_eq_zero_of_right _ hv
  let u := fun N => physicalRealMeanZeroWeightedRelift (v N) (hmem N)
  have hcoeff (N : ℕ) (j : ℤ) : (u N).val.val j=if j∈Finset.Icc (-(N : ℤ)) N then q.val j else 0 :=
    physicalRealMeanZeroWeightedTruncate_coefficient _ N p j
  have he (N : ℕ) : nativeHillSource m (u N).val=(v N).val := by
    apply Subtype.ext
    funext j
    rw [nativeHillSource_apply]
    rfl
  refine ⟨u,hcoeff,?_⟩
  simp_rw [he]
  exact continuous_subtype_val.continuousAt.tendsto.comp
    (tendsto_physicalRealMeanZeroWeightedTruncate (Weight.sobolev (-1)) p)

end NLS.KdV
