import NLS.SequenceSpaces.PeriodOneMiuraSobolevEquivalence
import NLS.KdV.HillHminusOneDiscriminant
import NLS.KdV.MiuraCanonicalEndpoints
import NLS.KdV.HillHminusOutsideMiuraChart
import NLS.KdV.HillHminusOneMiuraAllLabels
import NLS.ZakharovShabat.SourceSobolevGapRegularity
import NLS.ZakharovShabat.SourceWeightedRealMembership

/-! # All-order Sobolev regularity of the actual rough Hill Miura source

Every actual complex chart preserves the exact source/lift regularity
shift. For real lifts this identifies H^s of the ORIGINAL rough datum
with H^(s+1) of its ACTUAL signed canonical Dirac gaps, including all low,
negative and collapsed indices. No finite-gap or smallness hypothesis.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ENNReal ComplexConjugate
open NLS.ZakharovShabat
namespace NLS.KdV

/-- EVERY actual complex Hill Miura chart has the exact all-order
source/lift Sobolev criterion, on its entire domain. -/
theorem HillHminusMiuraChart.sobolev_iff_lift_mem
    (C : HillHminusMiuraChart) (q : PeriodOneHminusOne) (hq : q∈C.domain)
    (s : ℝ) (hs : -1 ≤ s) :
    Memℓp (fun n => (Weight.sobolev s n : ℂ)*q.val n) 2 ↔
      Memℓp (fun n => (Weight.sobolev (s+1) n : ℂ)*C.lift q n) 2 :=
  periodOneMiura_sobolev_iff q (C.lift q) C.energyShift (C.image q hq) s hs

/-- A genuinely rough Hill source has exactly the shifted Sobolev
regularity of the ACTUAL full signed Dirac gap sequence of ANY real L2
Miura lift. No initial L2 membership of q is assumed. -/
theorem hillHminus_sobolev_iff_real_miuraDirac_gap_mem
    (q : PeriodOneHminusOne) (u : PeriodOneRealL2) (c : ℂ)
    (himage : periodOneMiura u.val=q+periodOneL2Inclusion (lp.single 2 0 c))
    (s : ℝ) (hs : -1 ≤ s) :
    Memℓp (fun n => (Weight.sobolev s n : ℂ)*q.val n) 2 ↔
      Memℓp (fun n : ℤ => (Weight.sobolev (s+1) n : ℂ)*
        (hillMiuraDiracRight u.val n-hillMiuraDiracLeft u.val n)) 2 := by
  let φ : realTypeSourceSubmodule 2 := ⟨hillMiuraDiagonal u.val,isRealType_hillMiuraDiagonal u⟩
  have ht : 0 ≤ s+1 := by linarith
  have hsource :
      (Memℓp (fun n => (Weight.sobolev (s+1) n : ℂ)*φ.val.fst n) 2 ∧
        Memℓp (fun n => (Weight.sobolev (s+1) n : ℂ)*φ.val.snd n) 2) ↔
      Memℓp (fun n : ℤ => (Weight.sobolev (s+1) n : ℂ)*
        sourcePeriodicGapDisplacement (by simp) (by norm_num) φ.val n) 2 := by
    constructor
    · intro hφ
      let w := sourceSobolevSpectralWeight (s+1) ht
      obtain ⟨a,ha⟩ := (exists_originalWeightedRealSource_iff w φ).mpr
        (by simpa only [w,sourceSobolevSpectralWeight_even] using hφ)
      have hbase : weightedBaseToPair w
          (normalizedWeightedPeriodOne w (weightedRealSourceEquiv w a).val)=periodOnePotential φ.val := by
        rw [weightedBaseToPair_normalizedWeightedPeriodOne]
        change periodOnePotential (originalWeightedRealSource w a).val=_
        rw [ha]
      have hg := sourceWeightedGap_mem (by simp) (by norm_num) w φ.val _ hbase
      simpa only [w,sourceSobolevSpectralWeight_even] using hg
    · exact source_mem_sobolev_of_gap (by simp) (by norm_num) φ (s+1) ht
  have hp : Memℓp (fun n => (Weight.sobolev (s+1) n : ℂ)*u.val n) 2 ↔
      (Memℓp (fun n => (Weight.sobolev (s+1) n : ℂ)*φ.val.fst n) 2 ∧
        Memℓp (fun n => (Weight.sobolev (s+1) n : ℂ)*φ.val.snd n) 2) := by
    simp only [φ,hillMiuraDiagonal_fst,hillMiuraDiagonal_snd,and_self]
  have h := (periodOneMiura_sobolev_iff q u.val c himage s hs).trans (hp.trans hsource)
  simpa only [φ,sourcePeriodicGapDisplacement_apply,canonicalPeriodicGap,
    hillMiuraDiracRight,hillMiuraDiracLeft] using h

/-- On EVERY actual real-preserving Hill chart, the original rough datum
has H^s coefficients exactly when its actual canonical Dirac gaps have
H^(s+1) coefficients, for every real s>=-1. -/
theorem HillHminusMiuraChart.sobolev_iff_real_Dirac_gap_mem
    (C : HillHminusMiuraChart) (q : PeriodOneHminusOne) (hq : q∈C.domain)
    (hr : ∀ n : ℤ, C.lift q (-n)=conj (C.lift q n))
    (s : ℝ) (hs : -1 ≤ s) :
    Memℓp (fun n => (Weight.sobolev s n : ℂ)*q.val n) 2 ↔
      Memℓp (fun n : ℤ => (Weight.sobolev (s+1) n : ℂ)*
        (hillMiuraDiracRight (C.lift q) n-hillMiuraDiracLeft (C.lift q) n)) 2 :=
  hillHminus_sobolev_iff_real_miuraDirac_gap_mem q ⟨C.lift q,hr⟩ C.energyShift (C.image q hq) s hs

/-- At EVERY real rough base, ONE actual complex analytic Miura chart
simultaneously detects ALL s>=-1 Sobolev orders, preserves the real form,
and retains EVERY exact original Hill endpoint label on its whole real
slice. The chart and energy shift are selected before sources and orders. -/
theorem exists_hillHminus_real_Miura_all_sobolev_chart
    (q0 : PeriodOneHminusOne) (hr0 : IsRealPeriodOneHminusOne q0) :
    ∃ C : HillHminusMiuraChart, ∃ c : ℝ,
      0<c ∧ C.energyShift=(c : ℂ)^2 ∧ q0∈C.domain ∧
      ∀ q∈C.domain,
        (∀ s : ℝ, -1 ≤ s →
          (Memℓp (fun n => (Weight.sobolev s n : ℂ)*q.val n) 2 ↔
            Memℓp (fun n => (Weight.sobolev (s+1) n : ℂ)*C.lift q n) 2)) ∧
        ∀ hr : IsRealPeriodOneHminusOne q,
          (∀ n : ℤ, C.lift q (-n)=conj (C.lift q n)) ∧
          (∀ n : ℕ, 0<n →
            hillHminusRealLabels q hr (2*n-1)=(hillMiuraDiracLeft (C.lift q) n).re^2-c^2 ∧
            hillHminusRealLabels q hr (2*n)=(hillMiuraDiracRight (C.lift q) n).re^2-c^2) ∧
          ∀ s : ℝ, -1 ≤ s →
            (Memℓp (fun n => (Weight.sobolev s n : ℂ)*q.val n) 2 ↔
              Memℓp (fun n : ℤ => (Weight.sobolev (s+1) n : ℂ)*
                (hillMiuraDiracRight (C.lift q) n-hillMiuraDiracLeft (C.lift q) n)) 2) := by
  obtain ⟨C,c,hc,hshift,hq0,hreal,houtside⟩ := exists_hillHminus_outside_real_Miura_chart q0 hr0
  refine ⟨C,c,hc,hshift,hq0,?_⟩
  intro q hq
  refine ⟨(fun s hs => C.sobolev_iff_lift_mem q hq s hs), ?_⟩
  intro hr
  have hu : ∀ n : ℤ, C.lift q (-n)=conj (C.lift q n) :=
    (periodOneL2Conjugation_fixed_iff _).mp (hreal q hq hr)
  refine ⟨hu,?_,(fun s hs => C.sobolev_iff_real_Dirac_gap_mem q hq hu s hs)⟩
  intro n hn
  have hi : periodOneMiura (C.lift q)=q+periodOneL2Inclusion (lp.single 2 0 ((c^2 : ℝ) : ℂ)) := by
    simpa only [hshift,Complex.ofReal_pow] using C.image q hq
  have ho : hillHminusRadicand q (-((c^2 : ℝ) : ℂ))≠0 := by
    simpa only [hshift,Complex.ofReal_pow] using houtside q hq
  exact hillHminusLabels_pair_eq_squared_miuraDirac q hr ⟨C.lift q,hu⟩ (c^2) hi ho n hn

end NLS.KdV
