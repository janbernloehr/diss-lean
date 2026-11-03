import NLS.KdV.HillHminusOneCanonicalRealLabels
import NLS.KdV.HillCumulativeCounts
import NLS.SequenceSpaces.OrderedFiniteContinuity
import NLS.ComplexAnalysis.ZeroMultisetRestriction

/-! # Cumulative characteristic counts of intrinsic H^-1 labels

Diameter discs ending at a real threshold count exactly the ordered
central labels below that threshold. Together with contour stability,
this identifies the continuous order statistics even at double roots.
-/

noncomputable section
set_option autoImplicit false
open Set Metric
open scoped Classical
namespace NLS.KdV

theorem HillHminusRealCharacteristicLabeling.central_complex_multiset
    {q : PeriodOneHminusOne} {N : ℕ} {r : ℝ} {lambda : ℕ → ℝ}
    (h : HillHminusRealCharacteristicLabeling q N r lambda)
    (hreal : IsRealPeriodOneHminusOne q) :
    (∑ j ∈ Finset.range (2*N-1), ({(lambda j : ℂ)} : Multiset ℂ)) =
      hillHminusCentralRoots q N h.central_control := by
  have hr : (∑ j ∈ Finset.range (2*N-1), ({lambda j} : Multiset ℝ)) =
      hillHminusRealCentralRoots q N h.central_control := by
    apply Multiset.ext.mpr
    intro x
    have hc := (h.central_counts x).trans
      (count_hillHminusRealCentralRoots q hreal N h.central_control x).symm
    simpa only [Multiset.count_sum', Multiset.count_singleton, eq_comm] using hc
  have hm := congrArg (Multiset.map Complex.ofReal) hr
  rw [map_ofReal_hillHminusRealCentralRoots q hreal] at hm
  have hs := map_sum (Multiset.mapAddMonoidHom Complex.ofReal)
    (fun j => ({lambda j} : Multiset ℝ)) (Finset.range (2*N-1))
  change (∑ j ∈ Finset.range (2*N-1), ({lambda j} : Multiset ℝ)).map Complex.ofReal = _ at hs
  rw [hs] at hm
  simpa only [Multiset.mapAddMonoidHom_apply, Multiset.map_singleton] using hm

theorem HillHminusRealCharacteristicLabeling.cumulative_count
    {q : PeriodOneHminusOne} {N : ℕ} {r : ℝ} {lambda : ℕ → ℝ}
    (h : HillHminusRealCharacteristicLabeling q N r lambda)
    (hreal : IsRealPeriodOneHminusOne q)
    (c : ℝ) (hc : c ≤ hillCentralSeparator N) :
    ComplexAnalysis.analyticZeroCount (hillHminusRadicand q) (hillLeftDisc N c) =
      NLS.finiteLowerCount (2*N-1) lambda c := by
  classical
  let g := hillHminusRadicand q
  let S := hillLeftDisc N c
  let T := hillCentralDisc N
  let : DecidablePred (fun z : ℂ => z ∈ T ∩ S) := fun _ => Classical.propDecidable _
  have he : ComplexAnalysis.analyticZeroCount g S = ComplexAnalysis.analyticZeroCount g (T ∩ S) := by
    apply ComplexAnalysis.analyticZeroCount_congr_set
    intro z hz
    have hi := hillHminusRadicand_root_im_zero q hreal z hz
    have hzr : (z.re : ℂ) = z := by apply Complex.ext <;> simp [hi]
    rw [← hzr]
    change (z.re : ℂ) ∈ hillLeftDisc N c ↔
      (z.re : ℂ) ∈ hillCentralDisc N ∩ hillLeftDisc N c
    rw [mem_inter_iff, ofReal_mem_hillLeftDisc_iff, ofReal_mem_hillCentralDisc_iff]
    exact ⟨fun hz => ⟨⟨hz.1,hz.2.trans hc⟩,hz⟩,fun hz => hz.2⟩
  let H : Multiset ℂ →+ ℕ :=
    { toFun := fun s => (s.filter (fun z => z ∈ T ∩ S)).card
      map_zero' := by simp
      map_add' := by intro u v; simp only [Multiset.filter_add, Multiset.card_add] }
  have hfilter : ComplexAnalysis.analyticZeroCount g (T ∩ S) =
      H (hillHminusCentralRoots q N h.central_control) := by
    convert! ComplexAnalysis.analyticZeroCount_subset_eq_card_filter (S := T ∩ S) (T := T) g
      inter_subset_left (hillHminusCentralRootSupport q N h.central_control) using 1
  calc
    _ = H (hillHminusCentralRoots q N h.central_control) := he.trans hfilter
    _ = H (∑ j ∈ Finset.range (2*N-1), ({(lambda j : ℂ)} : Multiset ℂ)) := by
      rw [h.central_complex_multiset hreal]
    _ = ∑ j ∈ Finset.range (2*N-1), H ({(lambda j : ℂ)} : Multiset ℂ) := map_sum H _ _
    _ = ∑ j ∈ Finset.range (2*N-1), if lambda j ≤ c then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      have hj' := Finset.mem_range.mp hj
      have hmem := h.central_mem j hj'
      have hT : (lambda j : ℂ) ∈ T :=
        (ofReal_mem_hillCentralDisc_iff N _).mpr ⟨hmem.1.le,hmem.2.le⟩
      have hS : (lambda j : ℂ) ∈ T ∩ S ↔ lambda j ≤ c := by
        rw [mem_inter_iff, and_iff_right hT, ofReal_mem_hillLeftDisc_iff]
        exact ⟨fun hz => hz.2,fun hz => ⟨hmem.1.le,hz⟩⟩
      change (({(lambda j : ℂ)} : Multiset ℂ).filter (fun z => z ∈ T ∩ S)).card = _
      rw [Multiset.filter_singleton]
      by_cases hjc : lambda j ≤ c
      · simp only [if_pos (hS.mpr hjc), if_pos hjc, Multiset.card_singleton]
      · simp only [if_neg (fun ht => hjc (hS.mp ht)), if_neg hjc,
          Multiset.empty_eq_zero, Multiset.card_zero]
    _ = _ := by simp [NLS.finiteLowerCount]

end NLS.KdV
