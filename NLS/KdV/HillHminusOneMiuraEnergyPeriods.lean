import NLS.KdV.HillHminusOneRealMiuraEnergyPsi
import NLS.KdV.HillHminusOneMiuraRootSymmetry
import NLS.ZakharovShabat.EvenPsiAntisymmetricPeriods

/-! # Actual shifted-square pullback periods of the rough energy candidates

The Jacobian 2z, actual NLS canonical root and fixed energy translation
are retained in the literal circle integral. At every real rough base
potential one common complex neighborhood supports all candidates and
actual isolating circles, with the exact positive Kronecker periods.
This does not yet identify a global chart-independent Hill root/family.
-/
noncomputable section
open Set Metric Complex
namespace NLS.KdV
open NLS.ZakharovShabat

theorem hillHminusMiuraEnergyPsi_pullback_period (C : HillHminusMiuraChart)
    {W₀ W : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
    (H : SourceTheorem12_1Data (by simp) (by norm_num) W₀ W s)
    (q : PeriodOneHminusOne) (hq : C.criticalSource q ∈ W) (n m : ℤ)
    (D : SourceCriticalRootPeriodCircle (by simp) (by norm_num) (C.criticalSource q) m) :
    (∮ z in C((D.center:ℂ),D.radius),
      (2*z)*hillHminusMiuraEnergyPsi C s n (z^2-C.energyShift,q) /
        sourceCanonicalRoot (by simp) (by norm_num) (C.criticalSource q) z) =
      (2*Real.pi:ℂ)*((if m = n then 1 else 0)-(if -m = n then 1 else 0)) := by
  have he : (fun z => (2*z)*hillHminusMiuraEnergyPsi C s n (z^2-C.energyShift,q) /
      sourceCanonicalRoot (by simp) (by norm_num) (C.criticalSource q) z) =
      fun z => (hillHminusMiuraSourcePsi C s n (z,q)-hillHminusMiuraSourcePsi C s n (-z,q)) /
        sourceCanonicalRoot (by simp) (by norm_num) (C.criticalSource q) z := by
    funext z
    rw [hillHminusMiuraEnergyPsi_factor]
  rw [he]
  exact H.antisymmetric_raw_period (C.criticalSource q) hq (hillMiuraFrequencyTrace_even (C.lift q)) n m D

theorem hillHminusMiuraEnergyPsi_positive_pullback_period (C : HillHminusMiuraChart)
    {W₀ W : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
    (H : SourceTheorem12_1Data (by simp) (by norm_num) W₀ W s)
    (q : PeriodOneHminusOne) (hq : C.criticalSource q ∈ W) (n m : ℕ+)
    (D : SourceCriticalRootPeriodCircle (by simp) (by norm_num) (C.criticalSource q) (m:ℤ)) :
    (∮ z in C((D.center:ℂ),D.radius),
      (2*z)*hillHminusMiuraEnergyPsi C s (n:ℤ) (z^2-C.energyShift,q) /
        sourceCanonicalRoot (by simp) (by norm_num) (C.criticalSource q) z) =
      (2*Real.pi:ℂ)*(if m = n then 1 else 0) := by
  have hn : (0:ℤ) < n := by exact_mod_cast n.pos
  have hm : (0:ℤ) < m := by exact_mod_cast m.pos
  have hneg : -(m:ℤ) ≠ (n:ℤ) := by omega
  have he := hillHminusMiuraEnergyPsi_pullback_period C H q hq (n:ℤ) (m:ℤ) D
  simpa only [if_neg hneg,sub_zero,Int.natCast_inj,PNat.coe_inj] using he

theorem exists_hillHminus_real_normalized_energy_pullbacks (q0 : PeriodOneHminusOne)
    (hq0 : periodOneHminusConjugation q0 = q0) :
    ∃ C : HillHminusMiuraChart, ∃ V : Set PeriodOneHminusOne,
      ∃ W₀ W : Set (CoeffPair 2), ∃ s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n,
        IsOpen V ∧ q0 ∈ V ∧ V ⊆ C.domain ∧
        (∀ q ∈ C.domain, periodOneHminusConjugation q = q → q ∈ V) ∧
        0 < C.energyShift.re ∧ C.energyShift.im = 0 ∧
        (∀ q ∈ C.domain, periodOneHminusConjugation q = q →
          periodOneL2Conjugation (C.lift q) = C.lift q ∧
            IsRealType (CoeffPair.toMax 2 (C.criticalSource q))) ∧
        SourceTheorem12_1Data (by simp) (by norm_num) W₀ W s ∧
        (∀ q ∈ V, C.criticalSource q ∈ W) ∧
        (∀ n : ℤ, AnalyticOnNhd ℂ (hillHminusMiuraEnergyPsi C s n) (univ ×ˢ V)) ∧
        (∀ q ∈ V, Nonempty ((m : ℤ) →
          SourceCriticalRootPeriodCircle (by simp) (by norm_num) (C.criticalSource q) m)) ∧
        ∀ q ∈ V, ∀ n m : ℕ+,
          ∀ D : SourceCriticalRootPeriodCircle (by simp) (by norm_num) (C.criticalSource q) (m:ℤ),
            (∮ z in C((D.center:ℂ),D.radius),
              (2*z)*hillHminusMiuraEnergyPsi C s (n:ℤ) (z^2-C.energyShift,q) /
                sourceCanonicalRoot (by simp) (by norm_num) (C.criticalSource q) z) =
              (2*Real.pi:ℂ)*(if m = n then 1 else 0) := by
  obtain ⟨C,hqC,hshift,hshiftim,hreal⟩ := exists_real_hillHminusMiuraChart q0 hq0
  obtain ⟨W₀,_,_,_,W,hW,_,hrealW,s,H⟩ := sourceTheorem12_1
    (by simp : (2:ENNReal) ≠ ⊤) (by norm_num : 1 < (2:ENNReal))
  obtain ⟨A,hAo,hAc,hrealA,hgeometry⟩ := exists_global_source_isolating_neighborhood
    (by simp : (2:ENNReal) ≠ ⊤) (by norm_num : 1 < (2:ENNReal))
  have hA : SourceSpectralIsolationNeighborhood (by simp) (by norm_num) A :=
    ⟨hAo,hAc,hrealA,hgeometry⟩
  let V := C.domain ∩ C.criticalSource ⁻¹' (W ∩ A)
  have hV : IsOpen V :=
    C.analyticOnNhd_criticalSource.continuousOn.isOpen_inter_preimage C.domain_open (hW.inter hAo)
  have hrealV (q : PeriodOneHminusOne) (hq : q ∈ C.domain)
      (hr : periodOneHminusConjugation q = q) : q ∈ V :=
    ⟨hq,hrealW (hreal q hq hr).2,hrealA (hreal q hq hr).2⟩
  have hs (n : ℤ) : AnalyticOnNhd ℂ (fun q => s n (C.criticalSource q)) V := by
    intro q hq
    exact (H.analytic n (C.criticalSource q) hq.2.1).comp
      (C.analyticOnNhd_criticalSource q hq.1)
  refine ⟨C,V,W₀,W,s,hV,hrealV q0 hqC hq0,inter_subset_left,hrealV,hshift,hshiftim,hreal,H,
    fun _ hq => hq.2.1,analyticOnNhd_hillHminusMiuraEnergyPsi C s hV hs,?_,?_⟩
  · intro q hq
    exact hA.nonempty_periodCircles (C.criticalSource q) hq.2.2
  · intro q hq n m D
    exact hillHminusMiuraEnergyPsi_positive_pullback_period C H q hq.2.1 n m D

end NLS.KdV
