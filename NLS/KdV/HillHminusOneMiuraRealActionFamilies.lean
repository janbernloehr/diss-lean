import NLS.KdV.HillHminusOneMiuraHigherAction
import NLS.SequenceSpaces.PeriodOneMiuraRealNeighborhood
import NLS.ZakharovShabat.SourceIndexedHigherActionReal
import NLS.ZakharovShabat.SourceIndexedHigherActionAnalytic
import NLS.ZakharovShabat.SourceSection11Contours

/-! # Real-preserving analytic Miura action families

The same complex neighborhood supports every signed-index analytic
level-two action, full Abelian charts, and real Miura lifts at every
nearby real potential. The transferred root therefore agrees with the
physical Hill root for every real input, not just the base source.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV

theorem exists_hillHminus_real_preserving_Miura_action_family
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) (A : ℝ) :
    ∃ c : ℝ, 0 < c ∧ A < c ∧
      ∃ V : Set PeriodOneHminusOne, IsOpen V ∧ q ∈ V ∧
        ∃ u : PeriodOneHminusOne → Coeff 2, AnalyticOnNhd ℂ u V ∧
          (∀ a ∈ V, IsRealPeriodOneHminusOne a →
            ∀ k : ℤ, u a (-k) = star (u a k)) ∧
          (∀ a ∈ V, periodOneMiura (u a) =
            a+periodOneL2Inclusion (lp.single 2 0 ((c : ℂ)^2))) ∧
          (∀ n : ℤ, AnalyticOnNhd ℂ (fun a => hillHminusMiuraIndexedAction (u a) n) V) ∧
          ∃ W : Set (CoeffPair 2), ∀ a ∈ V,
            Nonempty (SourceAbelianSpectralChart (by simp) (by norm_num) W (hillMiuraDiagonal (u a))) := by
  obtain ⟨c,hc,hAc,U,hU,hqU,u,hu,hureal,himage⟩ := exists_real_preserving_periodOneMiura_energyChart q A
  let φ : realTypeSourceSubmodule 2 := hillMiuraRealSource ⟨u q,hureal q hqU hq⟩
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
  · intro a ha hreal k
    simpa only [Complex.star_def] using hureal a ha.1 hreal k
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

theorem hillHminusMiuraIndexedAction_real (u : PeriodOneRealL2) (n : ℤ) :
    (hillHminusMiuraIndexedAction u.val n).im = 0 := by
  have h := sourceIndexedHigherAction_real (by simp) (by norm_num) (hillMiuraRealSource u) n 1
  have hh : (sourceIndexedHigherAction (by simp) (by norm_num) n 1 (hillMiuraDiagonal u.val)).im = 0 := h
  simp [hillHminusMiuraIndexedAction,mul_im,hh]

theorem hillHminusMiuraRoot_eq_physical_on_real_neighborhood
    (V : Set PeriodOneHminusOne) (u : PeriodOneHminusOne → Coeff 2) (c : ℝ)
    (hreal : ∀ a ∈ V, IsRealPeriodOneHminusOne a →
      ∀ k : ℤ, u a (-k) = star (u a k))
    (himage : ∀ a ∈ V, periodOneMiura (u a) =
      a+periodOneL2Inclusion (lp.single 2 0 ((c : ℂ)^2)))
    (a : PeriodOneHminusOne) (ha : a ∈ V) (har : IsRealPeriodOneHminusOne a)
    (E : ℂ) (hE : E.im ≠ 0) :
    hillHminusMiuraRoot (u a) ((c : ℂ)^2) E = hillHminusContinuedRoot (E,a) := by
  let v : PeriodOneRealL2 := ⟨u a,hreal a ha har⟩
  have hc : ((c^2 : ℝ) : ℂ) = (c : ℂ)^2 := by push_cast; rfl
  rw [← hc]
  exact hillHminusMiuraRoot_eq_physical_of_real v a (c^2) (by rw [hc]; exact himage a ha) E hE

end NLS.KdV
