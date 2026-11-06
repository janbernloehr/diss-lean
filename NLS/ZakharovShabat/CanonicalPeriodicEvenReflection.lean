import NLS.ZakharovShabat.PeriodicEndpointGlobalMultiplicity
import NLS.ZakharovShabat.PeriodicEndpointRootCounts
import NLS.SequenceSpaces.OrderedPairedL2Enumeration

/-! # Exact indexed reflection of an even periodic characteristic

Global multiplicities, ordering and the original l2 lattice asymptotics
fix the reflected pair at index -n. No relabeling of a central block is
allowed, and the central pair is included.
-/
noncomputable section
open Set Complex NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.ZakharovShabat

private theorem order_neg (z w : ℂ) (h : complexLexLE z w) : complexLexLE (-w) (-z) := by
  rw [complexLexLE_iff] at h ⊢
  simpa only [neg_re,neg_im,neg_lt_neg_iff,neg_le_neg_iff,neg_inj,eq_comm] using h

private theorem displacement_reflection (ξ : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) 2) :
    Memℓp (fun n => -ξ (-n)-(Real.pi : ℂ)*n) 2 := by
  let a : Coeff 2 := ⟨_,hξ⟩
  have he : (fun n => -ξ (-n)-(Real.pi : ℂ)*n) =
      (fun n => (-Coeff.reflection a) n) := by
    funext n
    simp only [lp.coeFn_neg,Pi.neg_apply,Coeff.reflection_apply,a,Int.cast_neg]
    ring
  rw [he]
  exact lp.memℓp _

private theorem count_neg_pair (a b z : ℂ) :
    ({-b,-a} : Multiset ℂ).count z = ({a,b} : Multiset ℂ).count (-z) := by
  simp only [Multiset.insert_eq_cons,Multiset.count_cons,Multiset.count_singleton,
    neg_eq_iff_eq_neg,Nat.add_comm]

theorem canonicalPeriodicMultiplicity_neg_of_even (φ : PairSpace 2)
    (heven : ∀ z, canonicalPeriodicProduct (by simp) φ (-z) = canonicalPeriodicProduct (by simp) φ z)
    (z : ℂ) : periodicAlgebraicMultiplicity (by simp) φ (-z) = periodicAlgebraicMultiplicity (by simp) φ z := by
  have hd : HasDerivAt (fun w : ℂ => -w) (-1) z := (hasDerivAt_id z).neg
  have hn : deriv (fun w : ℂ => -w) z ≠ 0 := by rw [hd.deriv]; norm_num
  have ho := analyticOrderAt_comp_of_deriv_ne_zero
    (f := canonicalPeriodicProduct (by simp) φ) analyticAt_id.neg hn
  have hf : (fun w : ℂ => canonicalPeriodicProduct (by simp) φ (-w)) =
      canonicalPeriodicProduct (by simp) φ := funext heven
  have h := congrArg ENat.toNat ho
  change analyticOrderNatAt (fun w : ℂ => canonicalPeriodicProduct (by simp) φ (-w)) z =
    analyticOrderNatAt (canonicalPeriodicProduct (by simp) φ) (-z) at h
  rw [hf,analyticOrderNatAt_canonicalPeriodicProduct (by simp) (by norm_num),
    analyticOrderNatAt_canonicalPeriodicProduct (by simp) (by norm_num)] at h
  exact h.symm

theorem canonicalPeriodicEndpoints_neg_of_even (φ : PairSpace 2) (hφ : φ ∈ pairParitySubspace 0)
    (heven : ∀ z, canonicalPeriodicProduct (by simp) φ (-z) = canonicalPeriodicProduct (by simp) φ z) :
    ∀ n : ℤ,
      canonicalPeriodicLeft (by simp) (by norm_num) φ hφ n =
        -canonicalPeriodicRight (by simp) (by norm_num) φ hφ (-n) ∧
      canonicalPeriodicRight (by simp) (by norm_num) φ hφ n =
        -canonicalPeriodicLeft (by simp) (by norm_num) φ hφ (-n) := by
  let ξ := canonicalPeriodicLeft (by simp) (by norm_num) φ hφ
  let η := canonicalPeriodicRight (by simp) (by norm_num) φ hφ
  have hs := canonicalPeriodicEndpoints_spec (by simp) (by norm_num) φ hφ
  have hm (z : ℂ) : (∑ᶠ n : ℤ, ({ξ n,η n} : Multiset ℂ).count z) =
      ∑ᶠ n : ℤ, ({-η (-n),-ξ (-n)} : Multiset ℂ).count z := by
    simp_rw [count_neg_pair]
    have hn := finsum_comp_equiv (Equiv.neg ℤ)
      (f := fun n : ℤ => ({ξ n,η n} : Multiset ℂ).count (-z))
    simp only [Equiv.neg_apply] at hn
    rw [hn,hs.1.global_multiplicity z,hs.1.global_multiplicity (-z)]
    exact (canonicalPeriodicMultiplicity_neg_of_even φ heven z).symm
  obtain ⟨hL,hR⟩ := ordered_paired_unique_of_l2 ξ η
    (fun n => -η (-n)) (fun n => -ξ (-n))
    hs.1.left_displacement hs.1.right_displacement
    (displacement_reflection η hs.1.right_displacement) (displacement_reflection ξ hs.1.left_displacement)
    hs.2.1 hs.2.2 (fun n => order_neg _ _ (hs.2.1 (-n)))
    (fun i j hij => order_neg _ _ (hs.2.2 (-j) (-i) (by omega))) hm
  intro n
  exact ⟨congrFun hL n,congrFun hR n⟩

end NLS.ZakharovShabat
