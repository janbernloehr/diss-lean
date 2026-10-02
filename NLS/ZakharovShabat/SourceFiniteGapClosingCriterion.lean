import NLS.ZakharovShabat.SourceFiniteGap
import NLS.ZakharovShabat.SourceResonantCenterClosing

/-!
# Singleton distant strips imply the actual finite-gap property

The canonical endpoint labeling places both sufficiently distant
endpoints in the corresponding resonant strip. If its original
periodic spectrum has only one possible value there, the two canonical
endpoints coincide. Only finitely many actual indexed gaps can remain.
-/

noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Closing the original periodic spectra in all distant strips
leaves only finitely many nonzero canonical periodic gaps. -/
theorem finite_canonicalPeriodicGap_of_singleton_strips
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) (N : ℕ) (c : ℤ → ℂ)
    (hc : ∀ n : ℤ, N ≤ n.natAbs → ∀ z ∈ resonantStrip n,
      z ∈ periodicSpectrum hp (periodOnePotential φ) ↔ z = c n) :
    {n : ℤ | canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n ≠ 0}.Finite := by
  let M := max N (canonicalPeriodicCutoff hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ)+1)
  have hgap (n : ℤ) (hn : M ≤ n.natAbs) :
      canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n = 0 := by
    have ht := (canonicalPeriodicEndpoints_spec hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ)).1.distant
      n ((Nat.lt_succ_self _).trans_le ((le_max_right _ _).trans hn))
    have hs := canonicalPeriodicEndpoints_mem_spectrum hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n
    have hnN : N ≤ n.natAbs := (le_max_left _ _).trans hn
    have hl := (hc n hnN _ (refinedResonantDisk_subset_strip n ht.left_mem)).mp hs.1
    have hr := (hc n hnN _ (refinedResonantDisk_subset_strip n ht.right_mem)).mp hs.2
    simp only [canonicalPeriodicGap,hl,hr,sub_self]
  apply (Set.finite_Icc (-(M : ℤ)) (M : ℤ)).subset
  intro n hn
  have hsmall : n.natAbs < M := lt_of_not_ge (fun h => hn (hgap n h))
  simp only [Set.mem_Icc]
  constructor <;> omega

/-- The singleton-strip criterion gives membership in the existing
spectral finite-gap locus of real sources. -/
theorem mem_sourceFiniteGapLocus_of_singleton_strips
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceLocus p) (N : ℕ) (c : ℤ → ℂ)
    (hc : ∀ n : ℤ, N ≤ n.natAbs → ∀ z ∈ resonantStrip n,
      z ∈ periodicSpectrum hp (periodOnePotential φ.val) ↔ z = c n) :
    φ ∈ sourceFiniteGapLocus hp hp1 :=
  finite_canonicalPeriodicGap_of_singleton_strips hp hp1 φ.val N c hc

end NLS.ZakharovShabat
