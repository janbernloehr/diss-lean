import NLS.KdV.HillHminusOneMiuraEnergyRoot
import NLS.ZakharovShabat.SourcePsiGapRootIsospectral

/-! # Spectral invariance of actual rough Miura normalized numerators

Equality of the intrinsic rough Hill discriminants gives equality of the
shifted diagonal NLS discriminants, including their full periodic spectral
data. The canonical real psi roots and root products are invariant under
those data. Actual normalized extensions therefore give the same entire
energy numerator for any two real-type inputs in one fixed Miura chart.
The construction is available around every real rough base potential.
-/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV

/-- A fixed Miura translation transports intrinsic Hill discriminant equality to actual NLS isospectrality, including multiplicities. -/
theorem hillHminusMiuraSource_isospectral_of_discriminant_eq (C : HillHminusMiuraChart)
    (q p : PeriodOneHminusOne) (hq : q ∈ C.domain) (hp : p ∈ C.domain)
    (hqr : IsRealType (CoeffPair.toMax 2 (C.criticalSource q)))
    (hpr : IsRealType (CoeffPair.toMax 2 (C.criticalSource p)))
    (htrace : hillHminusDiscriminant p = hillHminusDiscriminant q) :
    (⟨C.criticalSource p,hpr⟩ : realTypeSourceSubmodule 2) ∈
      sourceIsospectralSet (by simp) (⟨C.criticalSource q,hqr⟩ : realTypeSourceSubmodule 2) := by
  apply (mem_sourceIsospectralSet_iff_discriminant_eq (by simp) (by norm_num) _ _).mpr
  funext z
  rw [← C.trace_shifted_square p hp,← C.trace_shifted_square q hq,htrace]

/-- Actual normalized entire numerators depend only on the Hill discriminant within one real-type chart. No gap or energy is excluded. -/
theorem hillHminusMiuraEnergyPsi_eq_of_discriminant_eq (C : HillHminusMiuraChart)
    {W₀ W : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
    (H : SourceTheorem12_1Data (by simp) (by norm_num) W₀ W s)
    (q p : PeriodOneHminusOne) (hq : q ∈ C.domain) (hp : p ∈ C.domain)
    (hqr : IsRealType (CoeffPair.toMax 2 (C.criticalSource q)))
    (hpr : IsRealType (CoeffPair.toMax 2 (C.criticalSource p)))
    (htrace : hillHminusDiscriminant p = hillHminusDiscriminant q) (n : ℤ) :
    (fun energy => hillHminusMiuraEnergyPsi C s n (energy,p)) =
      (fun energy => hillHminusMiuraEnergyPsi C s n (energy,q)) := by
  have hi := hillHminusMiuraSource_isospectral_of_discriminant_eq C q p hq hp hqr hpr htrace
  have hs : s n (C.criticalSource p) = s n (C.criticalSource q) := by
    rw [H.real_agreement n ⟨C.criticalSource p,hpr⟩,H.real_agreement n ⟨C.criticalSource q,hqr⟩]
    exact sourcePsiGapRoot_eq_of_isospectral (by simp) (by norm_num) _ _ hi n
  funext energy
  simp only [hillHminusMiuraEnergyPsi,hillHminusMiuraSourcePsi,hs]

/-- The sign-normalized canonical root product is invariant as a literal function, including totalized values on the cuts. -/
theorem hillHminusMiuraChart_energyRoot_eq_of_discriminant_eq (C : HillHminusMiuraChart)
    (q p : PeriodOneHminusOne) (hq : q ∈ C.domain) (hp : p ∈ C.domain)
    (hqr : IsRealType (CoeffPair.toMax 2 (C.criticalSource q)))
    (hpr : IsRealType (CoeffPair.toMax 2 (C.criticalSource p)))
    (htrace : hillHminusDiscriminant p = hillHminusDiscriminant q) (energy : ℂ) :
    C.energyRoot p energy = C.energyRoot q energy := by
  exact sourceCanonicalRoot_eq_of_isospectral (by simp) (by norm_num) _ _
    (hillHminusMiuraSource_isospectral_of_discriminant_eq C q p hq hp hqr hpr htrace) _

/-- At every real rough base, one actual normalized family is jointly complex analytic and spectrally invariant on the whole real slice of its chart domain. -/
theorem exists_hillHminus_real_spectral_miura_family (q0 : PeriodOneHminusOne)
    (hq0 : periodOneHminusConjugation q0 = q0) :
    ∃ C : HillHminusMiuraChart, ∃ V : Set PeriodOneHminusOne,
      ∃ W₀ W : Set (CoeffPair 2), ∃ s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n,
        IsOpen V ∧ q0 ∈ V ∧ V ⊆ C.domain ∧
        (∀ q ∈ C.domain, periodOneHminusConjugation q = q → q ∈ V) ∧
        SourceTheorem12_1Data (by simp) (by norm_num) W₀ W s ∧
        (∀ q ∈ V, C.criticalSource q ∈ W) ∧
        (∀ n : ℤ, AnalyticOnNhd ℂ (hillHminusMiuraEnergyPsi C s n) (univ ×ˢ V)) ∧
        ∀ q ∈ C.domain, ∀ p ∈ C.domain,
          periodOneHminusConjugation q = q → periodOneHminusConjugation p = p →
          hillHminusDiscriminant p = hillHminusDiscriminant q →
          ∀ n : ℤ, (fun energy => hillHminusMiuraEnergyPsi C s n (energy,p)) =
            (fun energy => hillHminusMiuraEnergyPsi C s n (energy,q)) := by
  obtain ⟨C,V,W₀,W,s,hV,hqV,hVC,hrealV,_,_,hr,H,hW,hpsi,_,_⟩ :=
    exists_hillHminus_real_normalized_energy_pullbacks q0 hq0
  refine ⟨C,V,W₀,W,s,hV,hqV,hVC,hrealV,H,hW,hpsi,?_⟩
  intro q hq p hp hqr hpr htrace n
  exact hillHminusMiuraEnergyPsi_eq_of_discriminant_eq C H q p hq hp (hr q hq hqr).2 (hr p hp hpr).2 htrace n

end NLS.KdV
