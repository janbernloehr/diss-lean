import NLS.KdV.HillHminusOneMiuraHigherAction
import NLS.KdV.HillHminusOneMiuraOutsideShift
import NLS.KdV.HillHminusOneMiuraCanonicalGaps
import NLS.ZakharovShabat.SourceIndexedHigherActionReal
import NLS.ZakharovShabat.SourceIndexedHigherActionAnalytic
import NLS.ZakharovShabat.SourceSection11Contours

/-! # One analytic Miura action family with all original real Hill indices

The energy shift lies below the actual full Hill spectrum for EVERY
complex input in the common source neighborhood. On every real input,
the same analytic lift has the original Hill label slots and its actions
vanish exactly at the corresponding original Hill gaps, at ALL positive
indices. Invariance of the action under a different Miura chart remains
a separate step before gluing these local analytic families.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV

theorem exists_hillHminus_Miura_action_family_outside_spectrum
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) (A : ℝ) :
    ∃ c : ℝ, 0 < c ∧ A < c ∧
      ∃ V : Set PeriodOneHminusOne, IsOpen V ∧ q ∈ V ∧
        ∃ u : PeriodOneHminusOne → Coeff 2, AnalyticOnNhd ℂ u V ∧
          (∀ a ∈ V, IsRealPeriodOneHminusOne a →
            ∀ k : ℤ, u a (-k) = star (u a k)) ∧
          (∀ a ∈ V, periodOneMiura (u a) =
            a+periodOneL2Inclusion (lp.single 2 0 ((c : ℂ)^2))) ∧
          (∀ n : ℤ, AnalyticOnNhd ℂ (fun a => hillHminusMiuraIndexedAction (u a) n) V) ∧
          (∀ a ∈ V, -((c : ℂ)^2) ∉ singularHillSpectrum (periodOneOriginal a)) ∧
          ∃ W : Set (CoeffPair 2), ∀ a ∈ V,
            Nonempty (SourceAbelianSpectralChart (by simp) (by norm_num) W (hillMiuraDiagonal (u a))) := by
  obtain ⟨c,hc,hAc,U,hU,hqU,u,hu,hureal,himage,houtside⟩ := exists_periodOneMiura_energyChart_outside_spectrum q A
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
  refine ⟨c,hc,hAc,V,hV,hqV,u,hu.mono inter_subset_left,?_,?_,?_,?_,W₂,?_⟩
  · intro a ha hreal k
    simpa only [Complex.star_def] using hureal a ha.1 hreal k
  · intro a ha
    exact himage a ha.1
  · intro n a ha
    have hi := h11.analytic_indexedHigherAction hW n 1 (f a) ha.2.1
    change AnalyticAt ℂ (fun b => 2*sourceIndexedHigherAction (by simp) (by norm_num) n 1 (f b)) a
    exact analyticAt_const.mul (hi.comp (f := f) (hf a ha.1))
  · intro a ha
    exact houtside a ha.1
  · intro a ha
    obtain ⟨D,hfa,hE⟩ := hcharts (f a) ha.2.2
    obtain ⟨E,_⟩ := hE (f a) hfa
    exact ⟨E⟩

theorem hillHminusMiura_action_family_original_real_slots
    (V : Set PeriodOneHminusOne) (u : PeriodOneHminusOne → Coeff 2) (c : ℝ)
    (hreal : ∀ a ∈ V, IsRealPeriodOneHminusOne a → ∀ k : ℤ, u a (-k) = star (u a k))
    (himage : ∀ a ∈ V, periodOneMiura (u a) =
      a+periodOneL2Inclusion (lp.single 2 0 ((c : ℂ)^2)))
    (houtside : ∀ a ∈ V, -((c : ℂ)^2) ∉ singularHillSpectrum (periodOneOriginal a))
    (a : PeriodOneHminusOne) (ha : a ∈ V) (har : IsRealPeriodOneHminusOne a) :
    hillHminusLabels a har = hillMiuraSquaredLabels (u a) (c^2) ∧
      ∀ n : ℕ+, 0 ≤ (hillHminusMiuraIndexedAction (u a) (n : ℕ)).re ∧
        (hillHminusMiuraIndexedAction (u a) (n : ℕ)).im = 0 ∧
        (hillHminusMiuraIndexedAction (u a) (n : ℕ) = 0 ↔
          ((hillHminusLabels a har (2*(n : ℕ))-hillHminusLabels a har (2*(n : ℕ)-1) : ℝ) : ℂ) = 0) := by
  let v : PeriodOneRealL2 := ⟨u a,hreal a ha har⟩
  have himage' : periodOneMiura v.val = a+periodOneL2Inclusion (lp.single 2 0 ((c^2 : ℝ) : ℂ)) := by
    simpa only [ofReal_pow] using himage a ha
  have houtside' : -((c^2 : ℝ) : ℂ) ∉ singularHillSpectrum (periodOneOriginal a) := by
    simpa only [ofReal_pow] using houtside a ha
  refine ⟨hillHminusLabels_eq_squared_miuraDirac a har v (c^2) himage' houtside',?_⟩
  intro n
  have hs := hillHminusMiuraIndexedAction_positive_index_spec v (n : ℕ) (by exact_mod_cast n.pos)
  exact ⟨hs.1,hs.2.1,hillHminusMiuraIndexedAction_eq_zero_iff_Hill_gap
    a har v (c^2) himage' houtside' (n : ℕ) n.pos⟩

end NLS.KdV
