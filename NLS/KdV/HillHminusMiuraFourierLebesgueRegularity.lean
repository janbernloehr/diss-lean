import NLS.KdV.HillHminusFourierLebesgueMiuraCharts
import NLS.KdV.HillHminusMiuraSobolevRegularity
import NLS.ZakharovShabat.SourceAngularEtaPhaseExponent

/-! # Exact Fourier-Lebesgue regularity of the actual Miura Dirac gaps

The canonical gap sequence is the original Hilbert physical sequence.
Exponent compatibility transfers the all-finite-exponent Dirac criterion
to this fixed sequence; no stronger source membership is assumed.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ENNReal ComplexConjugate
open NLS.ZakharovShabat
namespace NLS.KdV

theorem hillHminus_fourierLebesgue_iff_real_miuraDirac_gap_mem
    (q : PeriodOneHminusOne) (u : PeriodOneRealL2) (c : ℂ)
    (himage : periodOneMiura u.val=q+periodOneL2Inclusion (lp.single 2 0 c))
    (s : ℝ) (hs : -1/2≤s) (p : ℝ≥0∞) (hp : p≠⊤) (h2p : 2≤p) [Fact (1≤p)] :
    Memℓp (fun n => (Weight.sobolev s n : ℂ)*q.val n) p ↔
      Memℓp (fun n : ℤ => (Weight.sobolev (s+1) n : ℂ)*
        (hillMiuraDiracRight u.val n-hillMiuraDiracLeft u.val n)) p := by
  have hp1 : 1<p := lt_of_lt_of_le (by norm_num : (1 : ℝ≥0∞)<2) h2p
  let φ2 : realTypeSourceSubmodule 2 := ⟨hillMiuraDiagonal u.val,isRealType_hillMiuraDiagonal u⟩
  let φ : realTypeSourceSubmodule p :=
    ⟨CoeffPair.exponentInclusion h2p φ2.val,fun n => φ2.property n⟩
  have ht : 0 ≤ s+1 := by linarith
  have hsource :
      (Memℓp (fun n => (Weight.sobolev (s+1) n : ℂ)*φ.val.fst n) p ∧
        Memℓp (fun n => (Weight.sobolev (s+1) n : ℂ)*φ.val.snd n) p) ↔
      Memℓp (fun n : ℤ => (Weight.sobolev (s+1) n : ℂ)*
        sourcePeriodicGapDisplacement hp hp1 φ.val n) p := by
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
      have hg := sourceWeightedGap_mem hp hp1 w φ.val _ hbase
      simpa only [w,sourceSobolevSpectralWeight_even] using hg
    · exact source_mem_sobolev_of_gap hp hp1 φ (s+1) ht
  have hdiag : Memℓp (fun n => (Weight.sobolev (s+1) n : ℂ)*u.val n) p ↔
      (Memℓp (fun n => (Weight.sobolev (s+1) n : ℂ)*φ.val.fst n) p ∧
        Memℓp (fun n => (Weight.sobolev (s+1) n : ℂ)*φ.val.snd n) p) := by
    simp only [φ,φ2,CoeffPair.exponentInclusion_fst,CoeffPair.exponentInclusion_snd,
      Coeff.exponentInclusion_apply,hillMiuraDiagonal_fst,hillMiuraDiagonal_snd,and_self]
  have h := (periodOneMiura_fourierLebesgue_iff_finite_exponent q u.val c himage s hs p h2p hp).trans (hdiag.trans hsource)
  have hgap (n : ℤ) : sourcePeriodicGapDisplacement hp hp1 φ.val n=
      hillMiuraDiracRight u.val n-hillMiuraDiracLeft u.val n := by
    rw [sourcePeriodicGapDisplacement_apply]
    change canonicalPeriodicGap hp hp1
      (periodOnePotential (CoeffPair.exponentInclusion h2p φ2.val)) _ n=_
    rw [←canonicalPeriodicGap_source_exponent (by simp) hp (by norm_num) hp1 h2p φ2.val n]
    rfl
  simpa only [hgap] using h

theorem HillHminusMiuraChart.fourierLebesgue_iff_real_Dirac_gap_mem
    (C : HillHminusMiuraChart) (q : PeriodOneHminusOne) (hq : q∈C.domain)
    (hr : ∀ n : ℤ, C.lift q (-n)=conj (C.lift q n))
    (s : ℝ) (hs : -1/2≤s) (p : ℝ≥0∞) (hp : p≠⊤) (h2p : 2≤p) [Fact (1≤p)] :
    Memℓp (fun n => (Weight.sobolev s n : ℂ)*q.val n) p ↔
      Memℓp (fun n : ℤ => (Weight.sobolev (s+1) n : ℂ)*
        (hillMiuraDiracRight (C.lift q) n-hillMiuraDiracLeft (C.lift q) n)) p :=
  hillHminus_fourierLebesgue_iff_real_miuraDirac_gap_mem q ⟨C.lift q,hr⟩ C.energyShift
    (C.image q hq) s hs p hp h2p

end NLS.KdV
