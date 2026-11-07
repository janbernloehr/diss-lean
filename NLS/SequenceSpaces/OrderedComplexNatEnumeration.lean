import NLS.SequenceSpaces.OrderedNatEnumerationUnique
import NLS.ComplexAnalysis.LexicographicOrder

/-! Ordered complex one-sided enumerations are determined by their actual
multiplicities, including all repeated entries and without a common tail. -/
noncomputable section
open Set NLS.ComplexAnalysis
open scoped Classical
namespace NLS

theorem ordered_complex_nat_enumeration_unique (f g : ℕ → ℂ)
    (hf : ∀ e, {j | f j = e}.Finite) (hg : ∀ e, {j | g j = e}.Finite)
    (hfm : Monotone (fun j => complexLexKey (f j)))
    (hgm : Monotone (fun j => complexLexKey (g j)))
    (hmult : ∀ e, (∑ᶠ j, if f j = e then (1:ℕ) else 0) =
      ∑ᶠ j, if g j = e then (1:ℕ) else 0) : f = g := by
  have hfkey (k : ℝ ×ₗ ℝ) : {j | complexLexKey (f j) = k}.Finite := by
    let e : ℂ := ⟨(ofLex k).1,(ofLex k).2⟩
    have hek : complexLexKey e = k := by cases k; rfl
    simpa only [← hek,complexLexKey_injective.eq_iff] using hf e
  have hgkey (k : ℝ ×ₗ ℝ) : {j | complexLexKey (g j) = k}.Finite := by
    let e : ℂ := ⟨(ofLex k).1,(ofLex k).2⟩
    have hek : complexLexKey e = k := by cases k; rfl
    simpa only [← hek,complexLexKey_injective.eq_iff] using hg e
  have hmkey (k : ℝ ×ₗ ℝ) :
      (∑ᶠ j, if complexLexKey (f j) = k then (1:ℕ) else 0) =
        ∑ᶠ j, if complexLexKey (g j) = k then (1:ℕ) else 0 := by
    let e : ℂ := ⟨(ofLex k).1,(ofLex k).2⟩
    have hek : complexLexKey e = k := by cases k; rfl
    simpa only [← hek,complexLexKey_injective.eq_iff] using hmult e
  have he := ordered_nat_enumeration_eq_of_multiplicity
    (fun j => complexLexKey (f j)) (fun j => complexLexKey (g j))
      hfkey hgkey hfm hgm hmkey
  funext j
  exact complexLexKey_injective (congrFun he j)

end NLS
