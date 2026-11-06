import NLS.SequenceSpaces.OrderedPairedL2Enumeration

/-! Strictly ordered simple signed spectral enumerations. Their actual
range and L2 displacement fix the index offset, including the central block. -/
noncomputable section
open Set Complex NLS.ComplexAnalysis
open scoped Classical
namespace NLS

/-- Injective enumerations count a doubled singleton twice on their
range and zero times elsewhere, with no finiteness assumption on the range. -/
theorem finsum_double_singleton_count_of_injective (f : ℤ → ℂ)
    (hf : Function.Injective f) (z : ℂ) :
    (∑ᶠ n : ℤ, ({f n,f n} : Multiset ℂ).count z) = if z ∈ range f then 2 else 0 := by
  by_cases hz : z ∈ range f
  · obtain ⟨n,rfl⟩ := hz
    rw [if_pos (mem_range_self n),finsum_eq_single _ n (by
      intro m hmn
      have hne : f m ≠ f n := fun h => hmn (hf h)
      simp [Ne.symm hne])]
    simp
  · rw [if_neg hz]
    have he : (fun n : ℤ => ({f n,f n} : Multiset ℂ).count z) = 0 := by
      funext n
      have hn : f n ≠ z := fun h => hz ⟨n,h⟩
      simp [Ne.symm hn]
    rw [he]
    change (∑ᶠ _ : ℤ, (0:ℕ)) = 0
    exact finsum_zero

/-- Equal actual ranges and strict real ordering determine the entire
signed sequence once both displacements from pi*n are in L2. In particular
no integer shift of the finite central labeling remains possible. -/
theorem ordered_signed_simple_unique_of_l2 (f g : ℤ → ℂ)
    (hf : Memℓp (fun n => f n-(Real.pi:ℂ)*n) 2)
    (hg : Memℓp (fun n => g n-(Real.pi:ℂ)*n) 2)
    (hfm : StrictMono (fun n => (f n).re)) (hgm : StrictMono (fun n => (g n).re))
    (hrange : range f = range g) : f = g := by
  have hfi : Function.Injective f := fun i j hij => hfm.injective (congrArg Complex.re hij)
  have hgi : Function.Injective g := fun i j hij => hgm.injective (congrArg Complex.re hij)
  exact (ordered_paired_unique_of_l2 f f g g hf hf hg hg
    (fun _ => le_rfl) (fun i j hij => complexLexLE_of_re_lt (hfm hij))
    (fun _ => le_rfl) (fun i j hij => complexLexLE_of_re_lt (hgm hij)) (fun z => by
      rw [finsum_double_singleton_count_of_injective f hfi,
        finsum_double_singleton_count_of_injective g hgi,hrange])).1

end NLS
