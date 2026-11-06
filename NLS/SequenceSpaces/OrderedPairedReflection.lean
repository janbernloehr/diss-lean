import NLS.SequenceSpaces.OrderedPairedL2Enumeration
import NLS.SequenceSpaces.Reflection

/-! Full reflection of ordered paired spectral enumerations. The global
multiplicity symmetry and original L2 displacements fix every signed index,
including the entire central block and all repeated pairs. -/
noncomputable section
open Set Complex
open scoped ENNReal Classical
namespace NLS.ComplexAnalysis

theorem complexLexLE_neg_neg (z w : ℂ) : complexLexLE (-z) (-w) ↔ complexLexLE w z := by
  rw [complexLexLE_iff,complexLexLE_iff]
  simp only [Complex.neg_re,Complex.neg_im,neg_lt_neg_iff,neg_le_neg_iff,neg_inj]
  constructor
  · rintro (h | ⟨h₁,h₂⟩)
    · exact Or.inl h
    · exact Or.inr ⟨h₁.symm,h₂⟩
  · rintro (h | ⟨h₁,h₂⟩)
    · exact Or.inl h
    · exact Or.inr ⟨h₁.symm,h₂⟩

end NLS.ComplexAnalysis
namespace NLS
open NLS.ComplexAnalysis

theorem paired_count_neg_reflection (ξ η : ℤ → ℂ) (z : ℂ) :
    (∑ᶠ n : ℤ, ({-η (-n),-ξ (-n)} : Multiset ℂ).count z) =
      ∑ᶠ n : ℤ, ({ξ n,η n} : Multiset ℂ).count (-z) := by
  have hc (n : ℤ) : ({-η (-n),-ξ (-n)} : Multiset ℂ).count z =
      ({ξ (-n),η (-n)} : Multiset ℂ).count (-z) := by
    simp [Multiset.count_cons,Multiset.count_singleton,neg_eq_iff_eq_neg,add_comm]
  simp_rw [hc]
  exact finsum_comp_equiv (Equiv.neg ℤ)
    (f := fun n : ℤ => ({ξ n,η n} : Multiset ℂ).count (-z))

/-- Exact signed reflection, without an unspecified finite index shift. -/
theorem ordered_paired_reflection_of_l2 (ξ η : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi:ℂ)*n) 2)
    (hη : Memℓp (fun n => η n-(Real.pi:ℂ)*n) 2)
    (hw : ∀ n, complexLexLE (ξ n) (η n))
    (hc : ∀ i j : ℤ, i < j → complexLexLE (η i) (ξ j))
    (hmult : ∀ z, (∑ᶠ n : ℤ, ({ξ n,η n} : Multiset ℂ).count (-z)) =
      ∑ᶠ n : ℤ, ({ξ n,η n} : Multiset ℂ).count z) :
    (∀ n, ξ (-n) = -η n) ∧ (∀ n, η (-n) = -ξ n) := by
  have hd (f : ℤ → ℂ) (hf : Memℓp (fun n => f n-(Real.pi:ℂ)*n) 2) :
      Memℓp (fun n => -f (-n)-(Real.pi:ℂ)*n) 2 := by
    have h := lp.memℓp (-(Coeff.reflection (⟨_,hf⟩ : Coeff 2)))
    convert! h using 1
    funext n
    simp only [lp.coeFn_neg,Pi.neg_apply,Coeff.reflection_apply,Int.cast_neg]
    ring
  have he := ordered_paired_unique_of_l2 ξ η (fun n => -η (-n)) (fun n => -ξ (-n))
    hξ hη (hd η hη) (hd ξ hξ) hw hc
    (fun n => (complexLexLE_neg_neg _ _).mpr (hw (-n)))
    (fun i j hij => (complexLexLE_neg_neg _ _).mpr (hc (-j) (-i) (neg_lt_neg hij)))
    (fun z => by rw [paired_count_neg_reflection,hmult])
  constructor
  · intro n
    have h := congrFun he.1 (-n)
    simpa only [neg_neg] using h
  · intro n
    have h := congrFun he.2 (-n)
    simpa only [neg_neg] using h

end NLS
