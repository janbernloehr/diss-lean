import NLS.ZakharovShabat.SourceCanonicalCoefficientContinuity
import NLS.ZakharovShabat.SourceHilbertCoefficientCompactness

/-! # Uniform central endpoint bounds on actual real Hilbert norm balls

Bounded real sources have coefficientwise convergent subsequences. The
actual indexed endpoints are continuous under these bounded coefficient
limits, so the two central endpoints are uniformly bounded on each norm
ball. No common strong-source neighborhood or extra Sobolev norm is used.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal Classical
namespace NLS.ZakharovShabat

/-- Both actual central Dirac endpoints have one bound on EVERY real
Hilbert norm ball, without a tail cutoff or stronger regularity premise. -/
theorem exists_uniform_real_hilbert_central_endpoint_bound (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ φ : realTypeSourceSubmodule 2, ‖φ.val‖ ≤ R →
      ‖canonicalPeriodicLeft (by simp) (by norm_num)
        (periodOnePotential φ.val) (periodOnePotential_mem _) 0‖+
      ‖canonicalPeriodicRight (by simp) (by norm_num)
        (periodOnePotential φ.val) (periodOnePotential_mem _) 0‖ ≤ C := by
  by_contra hn
  push Not at hn
  choose a ha hb using fun k : ℕ => hn (k : ℝ) (by positivity)
  have hba : Bornology.IsBounded (range a) := by
    apply isBounded_iff_forall_norm_le.mpr
    exact ⟨R,by rintro _ ⟨k,rfl⟩; exact ha k⟩
  obtain ⟨b,σ,hσ,ht,_ht₂⟩ := exists_realTypeSource_coefficientwise_subseq a hba
  have hbval : Bornology.IsBounded (range (fun k => (a (σ k)).val)) := by
    apply isBounded_iff_forall_norm_le.mpr
    exact ⟨R,by rintro _ ⟨k,rfl⟩; exact ha (σ k)⟩
  have he := tendsto_source_canonicalPeriodicEndpoints_of_bounded_coefficientwise
    (by simp : (2 : ℝ≥0∞)≠⊤) (by norm_num : 1<(2 : ℝ≥0∞))
    (fun k => (a (σ k)).val) b.val hbval (fun k => (a (σ k)).property) b.property ht 0
  have hconv := he.1.norm.add he.2.norm
  obtain ⟨B,hB⟩ := (Metric.isBounded_range_of_tendsto _ hconv).exists_norm_le
  obtain ⟨k,hk⟩ := exists_nat_gt B
  have hbad := hb (σ k)
  have hs : (k : ℝ) ≤ σ k := by exact_mod_cast hσ.id_le k
  have hupper := hB _ ⟨k,rfl⟩
  rw [Real.norm_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))] at hupper
  linarith

end NLS.ZakharovShabat
