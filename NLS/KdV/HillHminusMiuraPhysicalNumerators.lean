import NLS.KdV.HillHminusFixedPhysicalNumerators
import NLS.KdV.HillHminusOneRealMiuraEnergyPsi

/-! The independently normalized rough series numerator is the original
physical numerator when evaluated on the same real Miura chart. The comparison
includes the removable zero-frequency value, without cancelling a frequency. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ComplexConjugate
namespace NLS.KdV

/-- Two verified Dirac root factories give exactly the same filled energy
numerator at every real input, including zero translated energy. -/
theorem hillHminusMiuraEnergyPsi_eq_chart_numerator (C : HillHminusMiuraChart)
    {W₀ W : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
    (H : SourceTheorem12_1Data (by simp) (by norm_num) W₀ W s)
    (B : MiuraHillPsiFamily) (q : PeriodOneHminusOne)
    (hr : IsRealType (CoeffPair.toMax 2 (C.criticalSource q))) (n : ℕ+) (E : ℂ) :
    hillHminusMiuraEnergyPsi C s (n : ℤ) (E,q) =
      (HillHminusPsiChart.mk C B).numerator n (E,q) := by
  have hs : s (n : ℤ) (C.criticalSource q) = B.roots (n : ℤ) (C.criticalSource q) := by
    rw [H.real_agreement (n : ℤ) ⟨C.criticalSource q,hr⟩,
      B.verified.real_agreement (n : ℤ) ⟨C.criticalSource q,hr⟩]
  simp only [hillHminusMiuraEnergyPsi,hillHminusMiuraSourcePsi,HillHminusPsiChart.numerator,
    MiuraHillPsiFamily.numerator,sourcePsiEnergyNumerator,jointOddSquareDescent,
    oddPartQuotient,jointDSlopeZero,oddSquareDescent,sourceSelectedPsiNumerator,
    sourcePsiDeletedCandidate,HillHminusMiuraChart.criticalSource] at hs ⊢
  rw [hs]

/-- Reality of the actual diagonal source implies coefficientwise reality
of its literal Miura lift, with no assumption on a chosen root factory. -/
theorem HillHminusMiuraChart.lift_real_of_criticalSource_real (C : HillHminusMiuraChart)
    (q : PeriodOneHminusOne) (hr : IsRealType (CoeffPair.toMax 2 (C.criticalSource q))) :
    ∀ k : ℤ, C.lift q (-k) = conj (C.lift q k) := by
  intro k
  have h := hr (-k)
  change (hillMiuraDiagonal (C.lift q)).snd (-k) =
    conj ((hillMiuraDiagonal (C.lift q)).fst (-(-k))) at h
  simpa only [hillMiuraDiagonal_fst,hillMiuraDiagonal_snd,neg_neg] using h

/-- A real physical input in the Miura domain belongs to the actual
all-index numerator chart source. -/
theorem HillHminusPsiChart.original_source_mem_of_real (P : HillHminusPsiChart)
    (q : RealPeriodOneHillPotential) (hq : hillOriginalHminusSource q.val ∈ P.miura.domain)
    (hr : IsRealType (CoeffPair.toMax 2 (P.miura.criticalSource (hillOriginalHminusSource q.val)))) :
    hillOriginalHminusSource q.val ∈ P.source := by
  exact ⟨hq,P.family.real_subset hr⟩

/-- The rough-series numerator is the ORIGINAL physical numerator. The
chart reality and outside-shift assumptions are explicit; no normalization
or physical-numerator agreement is supplied as a hypothesis. -/
theorem HillHminusPsiChart.miuraEnergyPsi_eq_original (P : HillHminusPsiChart)
    {W₀ W : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
    (H : SourceTheorem12_1Data (by simp) (by norm_num) W₀ W s)
    (q : RealPeriodOneHillPotential) (hq : hillOriginalHminusSource q.val ∈ P.source)
    (hr : ∀ a ∈ P.miura.domain, IsRealPeriodOneHminusOne a →
      IsRealType (CoeffPair.toMax 2 (P.miura.criticalSource a)))
    (houtside : hillHminusRadicand (hillOriginalHminusSource q.val) (-P.miura.energyShift) ≠ 0)
    (c : ℝ) (hshift : P.miura.energyShift = (c : ℂ)^2) (n : ℕ+) (E : ℂ) :
    hillHminusMiuraEnergyPsi P.miura s (n : ℤ) (E,hillOriginalHminusSource q.val) =
      hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n n.pos E := by
  have hreal : ∀ a ∈ P.miura.domain, IsRealPeriodOneHminusOne a →
      ∀ k : ℤ, P.miura.lift a (-k) = conj (P.miura.lift a k) :=
    fun a ha har => P.miura.lift_real_of_criticalSource_real a (hr a ha har)
  rw [hillHminusMiuraEnergyPsi_eq_chart_numerator P.miura H P.family _
    (hr _ hq.1 (hillOriginalHminusSource_real q.val q.property.2)) n E]
  exact congrFun (P.numerator_eq_original q hq hreal houtside c hshift n) E

end NLS.KdV
