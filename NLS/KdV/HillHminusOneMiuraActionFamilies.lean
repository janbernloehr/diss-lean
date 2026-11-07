import NLS.KdV.HillHminusOneMiuraHigherAction
import NLS.SequenceSpaces.PeriodOneMiuraRealCharts
import NLS.ZakharovShabat.SourceIndexedHigherActionAnalytic
import NLS.ZakharovShabat.SourceSection11Contours

/-! # Common analytic Miura contour-action families near every real H-minus-one source

One complex source neighborhood supports the actual shifted Miura
identity, full Dirac primitive charts and analytic level-two action
functions at ALL indices. Positive isolating-circle geometry and
identification of the low Hill index slots remain separate obligations.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV

theorem exists_hillHminus_real_Miura_action_family
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) (A : ℝ) :
    ∃ c : ℝ, 0 < c ∧ A < c ∧
      ∃ V : Set PeriodOneHminusOne, IsOpen V ∧ q ∈ V ∧
        ∃ u : PeriodOneHminusOne → Coeff 2, AnalyticOnNhd ℂ u V ∧
          (∀ k : ℤ, u q (-k) = star (u q k)) ∧
          (∀ a ∈ V, periodOneMiura (u a) =
            a+periodOneL2Inclusion (lp.single 2 0 ((c : ℂ)^2))) ∧
          (∀ n : ℤ, AnalyticOnNhd ℂ (fun a => hillHminusMiuraIndexedAction (u a) n) V) ∧
          ∃ W : Set (CoeffPair 2), ∀ a ∈ V,
            Nonempty (SourceAbelianSpectralChart (by simp) (by norm_num) W (hillMiuraDiagonal (u a))) := by
  obtain ⟨c,hc,hAc,U,hU,hqU,u,hu,hureal,himage⟩ := exists_real_periodOneMiura_energyChart q hq A
  let φ : realTypeSourceSubmodule 2 := hillMiuraRealSource ⟨u q,hureal⟩
  have hφ : hillMiuraDiagonal (u q) ∈ realTypeSourceLocus 2 := φ.property
  obtain ⟨W,hW,_,hreal,h11⟩ := sourceSection11Contours (p := 2) (by simp) (by norm_num)
  obtain ⟨W₂,V₂,_,hV₂,_,hreal₂,_,_,_,hcharts⟩ :=
    exists_sourceAbelian_almostReal_spectral_charts (p := 2) (by simp) (by norm_num)
  let f : PeriodOneHminusOne → CoeffPair 2 := fun a => hillMiuraDiagonal (u a)
  have hf : AnalyticOnNhd ℂ f U := by
    intro a ha
    exact (hillMiuraDiagonal.analyticAt (u a)).comp (f := u) (hu a ha)
  let V : Set PeriodOneHminusOne := U ∩ f ⁻¹' (W ∩ V₂)
  have hV : IsOpen V := hf.continuousOn.isOpen_inter_preimage hU (hW.inter hV₂)
  have hqV : q ∈ V := ⟨hqU,hreal hφ,hreal₂ hφ⟩
  refine ⟨c,hc,hAc,V,hV,hqV,u,hu.mono inter_subset_left,?_,?_,?_,W₂,?_⟩
  · intro k
    simpa only [Complex.star_def] using hureal k
  · intro a ha
    exact himage a ha.1
  · intro n a ha
    have hi := h11.analytic_indexedHigherAction hW n 1 (f a) ha.2.1
    change AnalyticAt ℂ (fun b => 2*sourceIndexedHigherAction (by simp) (by norm_num) n 1 (f b)) a
    exact analyticAt_const.mul (hi.comp (f := f) (hf a ha.1))
  · intro a ha
    obtain ⟨D,hfa,hE⟩ := hcharts (f a) ha.2.2
    obtain ⟨E,_⟩ := hE (f a) hfa
    exact ⟨E⟩

end NLS.KdV
