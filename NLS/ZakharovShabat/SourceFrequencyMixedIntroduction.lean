import NLS.ZakharovShabat.SourceSection20Original

/-! # The introductory mixed estimate for the uncorrected frequency

A single pair of sequence-valued maps realizes omega-star in
ell(p/2) + OnePlus near each original real source. One common source
neighborhood works before choosing any finite OnePlus projection.
This is separate from the stronger corrected remainder omega-star + 2I.
-/
noncomputable section
set_option autoImplicit false
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceSection20Data
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
  {W₀ W V Wa B U : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
  {D : SourceSection17OriginalData hp hp1 W₀ W V s}
  {A : SourceAbelianMomentAtlas hp hp1 Wa s} (Q : SourceSection20Data D A B U)
include Q

/-- One complex domain contains all real sources, and every point has one
locally bounded mixed decomposition chosen before the projection exponent. -/
theorem exists_frequency_mixed_neighborhood :
    ∃ Y : Set (CoeffPair p), IsOpen Y ∧ realTypeSourceLocus p ⊆ Y ∧ Y ⊆ U ∧
      ∀ φ ∈ Y, ∃ T : Set (CoeffPair p), IsOpen T ∧ φ ∈ T ∧ T ⊆ Y ∧
        ∃ g : CoeffPair p → Coeff (ENNReal.ofReal (p.toReal/2)),
        ∃ h : CoeffPair p → CoeffOnePlus,
          (∀ ψ ∈ T, ∀ n, A.renormalizedFrequency n ψ = g ψ n + (h ψ).1 n) ∧
          (∃ C : ℝ, 0 ≤ C ∧ ∀ ψ ∈ T, ‖g ψ‖ ≤ C) ∧
          ∀ (r : ℝ≥0∞) (hr1 : 1 < r) (hr : r ≠ ⊤),
            ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ ∈ T, ‖CoeffOnePlus.toCoeff r hr1 hr (h ψ)‖ ≤ C := by
  have hW : IsOpen W := by
    obtain ⟨E,hE,_⟩ := D.previous.previous.previous.atlas
    exact hE ▸ E.toSourcePsiComplexRootAtlas.isOpen_domain
  have hrealW : realTypeSourceLocus p ⊆ W :=
    D.complex.real_subset.trans D.complex.source_subset
  obtain ⟨Uf,hUf,_,hreal,_,_,hlocal⟩ :=
    A.exists_frequencySequence_neighborhood Q.roots hW hrealW
  let Y := Uf ∩ U
  have hY : IsOpen Y := hUf.inter Q.source_open
  refine ⟨Y,hY,fun φ hφ => ⟨hreal hφ,Q.real_subset hφ⟩,inter_subset_right,?_⟩
  intro φ hφ
  obtain ⟨T,hT,hφT,_,hb⟩ := hlocal φ hφ.1
  refine ⟨T ∩ Y,hT.inter hY,⟨hφT,hφ⟩,inter_subset_right,?_⟩
  apply Coeff.exists_onePlus_decomposition_of_refined (T ∩ Y)
    (fun ψ n => A.renormalizedFrequency n ψ) ENNReal.ofReal_ne_top
  intro r hr hr1 hpr
  let : Fact (1 ≤ r) := ⟨hr1.le⟩
  obtain ⟨C,hC,hbound⟩ := hb r hr hr1 hpr
  exact ⟨C,hC,fun ψ hψ => ⟨A.frequencySequence r ψ,
    (hbound ψ hψ.1).1,(hbound ψ hψ.1).2⟩⟩

/-- The literal introductory estimate, with a common locally bounded decomposition. -/
theorem frequency_mixed_at_real (φ : realTypeSourceSubmodule p) :
    ∃ T : Set (CoeffPair p), IsOpen T ∧ φ.val ∈ T ∧ T ⊆ U ∧
      ∃ g : CoeffPair p → Coeff (ENNReal.ofReal (p.toReal/2)),
      ∃ h : CoeffPair p → CoeffOnePlus,
        (∀ ψ ∈ T, ∀ n, A.renormalizedFrequency n ψ = g ψ n + (h ψ).1 n) ∧
        (∃ C : ℝ, 0 ≤ C ∧ ∀ ψ ∈ T, ‖g ψ‖ ≤ C) ∧
        ∀ (r : ℝ≥0∞) (hr1 : 1 < r) (hr : r ≠ ⊤),
          ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ ∈ T, ‖CoeffOnePlus.toCoeff r hr1 hr (h ψ)‖ ≤ C := by
  obtain ⟨Y,_,hreal,hYU,hlocal⟩ := Q.exists_frequency_mixed_neighborhood
  obtain ⟨T,hT,hφT,hTY,g,h,hval,hg,hh⟩ := hlocal φ.val (hreal φ.property)
  exact ⟨T,hT,hφT,hTY.trans hYU,g,h,hval,hg,hh⟩

end NLS.ZakharovShabat.SourceSection20Data
