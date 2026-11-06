import NLS.KdV.HillHminusPsiCharts
import NLS.SequenceSpaces.PeriodOneMiuraRealFormCharts
import NLS.KdV.HillHminusOriginalLabels
import NLS.KdV.HminusOneMiuraHighPairs

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.KdV

/-- The actual common numerator chart can preserve the full real form,
not just the base value, and retain the checked all-index phase estimates. -/
theorem exists_hillHminusPsiChart_real_form_with_original_estimates
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) (M : ℝ) :
    ∃ P : HillHminusPsiChart, ∃ c : ℝ, 0<c ∧ M<c ∧
      P.miura.energyShift=(c : ℂ)^2 ∧ q∈P.source ∧
      (∀ a∈P.miura.domain, IsRealPeriodOneHminusOne a → ∀ k : ℤ,
        P.miura.lift a (-k)=conj (P.miura.lift a k)) ∧
      SourceLemma12_12Data (by norm_num) (by norm_num)
        P.family.originalDomain P.family.domain P.family.roots := by
  obtain ⟨c,hc,hMc,V,hV,hqV,u,hu,himage,hreal⟩ := exists_periodOneMiura_energyChart_real_form q M
  obtain ⟨A,hA⟩ := exists_miuraHillPsiFamily_with_original_estimates
  let C : HillHminusMiuraChart := ⟨V,hV,(c : ℂ)^2,u,hu,himage⟩
  let P : HillHminusPsiChart := ⟨C,A⟩
  have hsource : u q∈A.source := A.real_mem_source ⟨u q,hreal q hqV hq⟩
  exact ⟨P,c,hc,hMc,rfl,⟨hqV,hsource⟩,hreal,hA⟩

/-- At every original physical source in such a chart, the actual canonical
Dirac endpoint slots square and translate to the ORIGINAL Hill endpoints,
with the SAME high indices and all collapsed multiplicities retained. -/
theorem HillHminusPsiChart.exists_original_labels_squared_miuraDirac
    (P : HillHminusPsiChart) (q : RealPeriodOneHillPotential)
    (hq : hillOriginalHminusSource q.val∈P.source)
    (hreal : ∀ a∈P.miura.domain, IsRealPeriodOneHminusOne a → ∀ k : ℤ,
      P.miura.lift a (-k)=conj (P.miura.lift a k))
    (c : ℝ) (hshift : P.miura.energyShift=(c : ℂ)^2) :
    ∃ N : ℕ, 2≤N ∧ ∀ n : ℕ, N≤n →
      hillRealLabels q.val q.property.1 q.property.2 (2*n-1)=
        (hillMiuraDiracLeft (P.miura.lift (hillOriginalHminusSource q.val)) n).re^2-c^2 ∧
      hillRealLabels q.val q.property.1 q.property.2 (2*n)=
        (hillMiuraDiracRight (P.miura.lift (hillOriginalHminusSource q.val)) n).re^2-c^2 ∧
      Real.pi*(n : ℝ)≤(hillMiuraDiracLeft (P.miura.lift (hillOriginalHminusSource q.val)) n).re+
        (hillMiuraDiracRight (P.miura.lift (hillOriginalHminusSource q.val)) n).re := by
  let u : PeriodOneRealL2 := ⟨P.miura.lift (hillOriginalHminusSource q.val),
    hreal _ hq.1 (hillOriginalHminusSource_real q.val q.property.2)⟩
  have hi : periodOneMiura u.val=hillOriginalHminusSource q.val+
      periodOneL2Inclusion (lp.single 2 0 ((c^2 : ℝ) : ℂ)) := by
    have h := P.miura.image _ hq.1
    rw [hshift] at h
    simpa only [Complex.ofReal_pow] using h
  obtain ⟨N,hN,hlabels⟩ := exists_hillHminusLabels_squared_miuraDirac
    (hillOriginalHminusSource q.val) (hillOriginalHminusSource_real q.val q.property.2) u (c^2) hi
  refine ⟨N,hN,?_⟩
  simpa only [hillHminusLabels_original_source q] using hlabels

end NLS.KdV
