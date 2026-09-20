import NLS.ZakharovShabat.PeriodicPairDiscriminantValues
import NLS.ZakharovShabat.DistantCriticalInterlacing

/-!
# Interlacing in actual distant periodic gaps

The completed periodic pair has one discriminant level. For distinct
real endpoints, Rolle and distant uniqueness put the critical label
strictly between them. A repeated pair has multiplicity two and equals
the critical label. No ordering of the pair's two chosen slots is needed.
-/

noncomputable section
open Set Complex Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {hp : p ≠ ⊤} {w : SpectralWeight} {φ : WeightedCoeffPair w.toWeight p}
variable {N : ℕ} {ξ η : ℤ → ℂ}

/-- A collapsed distant periodic pair equals the corresponding critical label. -/
theorem CompletePeriodicParityPairs.critical_eq_of_collapsed_gap
    (h : CompletePeriodicParityPairs hp w φ N ξ η) (hp1 : 1 < p)
    {M : ℕ} {χ : ℤ → ℂ}
    (hχ : CriticalPointLabeling hp hp1 (weightedBaseToPair w φ) h.even_potential M χ)
    (n : ℤ) (hn : N < n.natAbs) (hm : M < n.natAbs) (he : ξ n = η n) : χ n = ξ n := by
  have hs := h.distant n hn
  have hmult : periodicAlgebraicMultiplicity hp (weightedBaseToPair w φ) (ξ n) = 2 := by
    simpa [← he] using hs.multiplicity_eq_count (ξ n) (refinedResonantDisk_subset_strip n hs.left_mem)
  exact hχ.distant_eq_of_repeated_periodic_root n hm (ξ n) (ball_subset_closedBall hs.left_mem)
    (h.roots_mem_periodicSpectrum hp1 n).1 hmult.ge

/-- A distant critical point lies strictly between distinct real periodic endpoints in increasing order. -/
theorem CompletePeriodicParityPairs.critical_between_of_re_lt
    (h : CompletePeriodicParityPairs hp w φ N ξ η) (hp1 : 1 < p)
    (hreal : IsRealType (weightedBaseToPair w φ)) {M : ℕ} {χ : ℤ → ℂ}
    (hχ : CriticalPointLabeling hp hp1 (weightedBaseToPair w φ) h.even_potential M χ)
    (n : ℤ) (hn : N < n.natAbs) (hm : M < n.natAbs) (hlt : (ξ n).re < (η n).re) :
    (ξ n).re < (χ n).re ∧ (χ n).re < (η n).re := by
  have hs := h.distant n hn
  obtain ⟨hxi,hyi⟩ := h.roots_im_eq_zero_of_realType hp1 hreal n
  have hx : ((ξ n).re : ℂ) = ξ n := by apply Complex.ext <;> simp [hxi]
  have hy : ((η n).re : ℂ) = η n := by apply Complex.ext <;> simp [hyi]
  obtain ⟨hxv,hyv⟩ := h.discriminant_at_roots hp1 n
  exact hχ.distant_between_real_equal_values hreal n hm _ _ hlt
    (by rw [hx]; exact hs.left_mem) (by rw [hy]; exact hs.right_mem)
    (by rw [hx,hy]; exact hxv.trans hyv.symm)

/-- The critical point belongs to the closed actual distant gap, for either ordering of its slots. -/
theorem CompletePeriodicParityPairs.critical_mem_gap
    (h : CompletePeriodicParityPairs hp w φ N ξ η) (hp1 : 1 < p)
    (hreal : IsRealType (weightedBaseToPair w φ)) {M : ℕ} {χ : ℤ → ℂ}
    (hχ : CriticalPointLabeling hp hp1 (weightedBaseToPair w φ) h.even_potential M χ)
    (n : ℤ) (hn : N < n.natAbs) (hm : M < n.natAbs) :
    min (ξ n).re (η n).re ≤ (χ n).re ∧ (χ n).re ≤ max (ξ n).re (η n).re := by
  rcases lt_trichotomy (ξ n).re (η n).re with hlt | he | hgt
  · have hb := h.critical_between_of_re_lt hp1 hreal hχ n hn hm hlt
    exact ⟨(min_le_left _ _).trans hb.1.le,hb.2.le.trans (le_max_right _ _)⟩
  · obtain ⟨hxi,hyi⟩ := h.roots_im_eq_zero_of_realType hp1 hreal n
    have hec : ξ n = η n := by apply Complex.ext; exact he; rw [hxi,hyi]
    rw [h.critical_eq_of_collapsed_gap hp1 hχ n hn hm hec, he]
    simp
  · have hs := h.distant n hn
    obtain ⟨hxi,hyi⟩ := h.roots_im_eq_zero_of_realType hp1 hreal n
    have hx : ((ξ n).re : ℂ) = ξ n := by apply Complex.ext <;> simp [hxi]
    have hy : ((η n).re : ℂ) = η n := by apply Complex.ext <;> simp [hyi]
    obtain ⟨hxv,hyv⟩ := h.discriminant_at_roots hp1 n
    have hb := hχ.distant_between_real_equal_values hreal n hm _ _ hgt
      (by rw [hy]; exact hs.right_mem) (by rw [hx]; exact hs.left_mem)
      (by rw [hy,hx]; exact hyv.trans hxv.symm)
    exact ⟨(min_le_right _ _).trans hb.1.le,hb.2.le.trans (le_max_left _ _)⟩

/-- The fixed canonical critical coordinates interlace every sufficiently distant actual real gap. -/
theorem CompletePeriodicParityPairs.exists_cutoff_canonicalCriticalPoints_mem_gap
    (h : CompletePeriodicParityPairs hp w φ N ξ η) (hp1 : 1 < p)
    (hreal : IsRealType (weightedBaseToPair w φ)) :
    ∃ K : ℕ, N ≤ K ∧ ∀ n : ℤ, K < n.natAbs →
      min (ξ n).re (η n).re ≤
        (canonicalCriticalPoints hp hp1 (weightedBaseToPair w φ) h.even_potential n).re ∧
      (canonicalCriticalPoints hp hp1 (weightedBaseToPair w φ) h.even_potential n).re ≤
        max (ξ n).re (η n).re := by
  let M := canonicalCriticalCutoff hp hp1 (weightedBaseToPair w φ) h.even_potential
  refine ⟨max N M,le_max_left _ _,fun n hn => ?_⟩
  exact h.critical_mem_gap hp1 hreal
    (canonicalCriticalPoints_spec hp hp1 (weightedBaseToPair w φ) h.even_potential).1 n
    (lt_of_le_of_lt (le_max_left _ _) hn) (lt_of_le_of_lt (le_max_right _ _) hn)

end NLS.ZakharovShabat
