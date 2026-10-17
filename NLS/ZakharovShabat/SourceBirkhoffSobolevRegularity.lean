import NLS.ZakharovShabat.SourceSobolevGapRegularity
import NLS.ZakharovShabat.SourceWeightedRealMembership
import NLS.ZakharovShabat.SourceBirkhoffGapNormEquivalence

/-! # Exact Sobolev regularity of the source, gaps and Birkhoff coordinates

At every finite p>1 and nonnegative real order, the original real source,
its actual periodic gaps, and both original Birkhoff coordinates carry
exactly the same Sobolev weight. No finite-gap or Hilbert-space premise
is used for the converse. Native weighted representatives are also supplied.
-/
noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The exact same Sobolev order characterizes the real source and its actual gaps. -/
theorem source_sobolev_mem_iff_gap_mem (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (t : ℝ) (ht : 0 ≤ t) :
    (Memℓp (fun n : ℤ => (Weight.sobolev t n:ℂ)*φ.val.fst n) p ∧
      Memℓp (fun n : ℤ => (Weight.sobolev t n:ℂ)*φ.val.snd n) p) ↔
    Memℓp (fun n : ℤ => (Weight.sobolev t n:ℂ)*sourcePeriodicGapDisplacement hp hp1 φ.val n) p := by
  constructor
  · intro hφ
    let w := sourceSobolevSpectralWeight t ht
    obtain ⟨a,ha⟩ := (exists_originalWeightedRealSource_iff w φ).mpr
      (by simpa only [w,sourceSobolevSpectralWeight_even] using hφ)
    have hbase : weightedBaseToPair w (normalizedWeightedPeriodOne w (weightedRealSourceEquiv w a).val) =
        periodOnePotential φ.val := by
      rw [weightedBaseToPair_normalizedWeightedPeriodOne]
      change periodOnePotential (originalWeightedRealSource w a).val = _
      rw [ha]
    have hg := sourceWeightedGap_mem hp hp1 w φ.val _ hbase
    simpa only [w,sourceSobolevSpectralWeight_even] using hg
  · exact source_mem_sobolev_of_gap hp hp1 φ t ht

namespace SourceBirkhoffMapComplexData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}

/-- Original source and original Birkhoff outputs have exactly the same Sobolev regularity. -/
theorem source_sobolev_mem_iff_real_map_mem
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (φ : realTypeSourceSubmodule p) (t : ℝ) (ht : 0 ≤ t) :
    (Memℓp (fun n : ℤ => (Weight.sobolev t n:ℂ)*φ.val.fst n) p ∧
      Memℓp (fun n : ℤ => (Weight.sobolev t n:ℂ)*φ.val.snd n) p) ↔
    (Memℓp (fun n : ℤ => Weight.sobolev t n*(sourceRealBirkhoffMap hp hp1 s φ).1 n) p ∧
      Memℓp (fun n : ℤ => Weight.sobolev t n*(sourceRealBirkhoffMap hp hp1 s φ).2 n) p) :=
  (source_sobolev_mem_iff_gap_mem hp hp1 φ t ht).trans
    (D.weighted_gap_mem_iff_real_map_mem (Weight.sobolev t) φ)

/-- Weighted outputs produce a representative of the very same source in the native weighted space. -/
theorem exists_originalWeightedRealSource_iff_real_map_mem
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (φ : realTypeSourceSubmodule p) (t : ℝ) (ht : 0 ≤ t) :
    (∃ a : weightedRealSourceSubmodule (p := p) (sourceSobolevSpectralWeight t ht),
      originalWeightedRealSource (sourceSobolevSpectralWeight t ht) a = φ) ↔
    (Memℓp (fun n : ℤ => Weight.sobolev t n*(sourceRealBirkhoffMap hp hp1 s φ).1 n) p ∧
      Memℓp (fun n : ℤ => Weight.sobolev t n*(sourceRealBirkhoffMap hp hp1 s φ).2 n) p) := by
  rw [exists_originalWeightedRealSource_iff]
  simpa only [sourceSobolevSpectralWeight_even] using D.source_sobolev_mem_iff_real_map_mem φ t ht

end SourceBirkhoffMapComplexData

/-- One actual Section 14 construction preserves and reflects every nonnegative real Sobolev order. -/
theorem sourceSection14_sobolev_characterization (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W₀ W V : Set (CoeffPair p), ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
      ∃ _D : SourceSection14Data hp hp1 W₀ W V s, ∀ t : ℝ, ∀ _ht : 0 ≤ t,
        ∀ φ : realTypeSourceSubmodule p,
          (Memℓp (fun n : ℤ => (Weight.sobolev t n:ℂ)*φ.val.fst n) p ∧
            Memℓp (fun n : ℤ => (Weight.sobolev t n:ℂ)*φ.val.snd n) p) ↔
          (Memℓp (fun n : ℤ => Weight.sobolev t n*(sourceRealBirkhoffMap hp hp1 s φ).1 n) p ∧
            Memℓp (fun n : ℤ => Weight.sobolev t n*(sourceRealBirkhoffMap hp hp1 s φ).2 n) p) := by
  obtain ⟨W₀,W,V,s,D⟩ := sourceSection14 hp hp1
  exact ⟨W₀,W,V,s,D,fun t ht φ => D.complex.source_sobolev_mem_iff_real_map_mem φ t ht⟩

end NLS.ZakharovShabat
