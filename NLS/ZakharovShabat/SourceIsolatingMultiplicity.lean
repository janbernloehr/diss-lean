import NLS.ZakharovShabat.SourceIsolatingContourGeometry
import NLS.ZakharovShabat.PeriodicEndpointCutoffGrowth

/-!
# Rank-two periodic contours on the source isolating domain

A complete canonical endpoint sequence enumerates original algebraic
multiplicities. Pairwise disjoint assigned discs isolate each index's two
multiset slots, so every corresponding Cauchy–Riesz range has rank two.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- At any periodic eigenvalue inside an assigned disc, original algebraic
multiplicity equals its number of occurrences in the indexed endpoint pair. -/
theorem periodicMultiplicity_eq_sourceIsolatingPair_count
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ ψ : CoeffPair p) (N : ℕ) (ε : ℝ)
    (hcluster : ∀ m : ℤ, sourceSpectralCluster hp hp1 ψ m ⊆
      sourceIsolatingDisc hp hp1 φ N ε m)
    (hdisjoint : ∀ i j : ℤ, i ≠ j →
      Disjoint (sourceIsolatingDisc hp hp1 φ N ε i)
        (sourceIsolatingDisc hp hp1 φ N ε j))
    (n : ℤ) {z : ℂ}
    (hz : z ∈ sourceIsolatingDisc hp hp1 φ N ε n)
    (hspec : z ∈ periodicSpectrum hp (periodOnePotential ψ)) :
    periodicAlgebraicMultiplicity hp (periodOnePotential ψ) z =
      ({canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n,
        canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n} : Multiset ℂ).count z := by
  classical
  let L := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ)
  let R := canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ)
  let C := canonicalPeriodicCutoff hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ)
  let K := max C n.natAbs
  have hlabel := (canonicalPeriodicEndpoints_spec hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ)).1
  have hcentral := hlabel.central_at_larger_cutoff K (le_max_left _ _)
  have hnK : n ∈ Finset.Icc (-(K : ℤ)) (K : ℤ) := by
    simp only [Finset.mem_Icc]
    have hnat : n.natAbs ≤ K := le_max_right C n.natAbs
    omega
  have hroot := (source_periodicSpectrum_in_isolatingDisc_iff hp hp1 φ ψ N ε
    hcluster hdisjoint n hz).mp hspec
  have hzcentral : z ∈ centralPeriodicSpectrum hp (periodOnePotential ψ) K :=
    (hcentral.root_iff z).mp ⟨n, by omega, by simpa only [eq_comm] using hroot⟩
  have hzero (m : ℤ) (hmn : m ≠ n) : ({L m, R m} : Multiset ℂ).count z = 0 := by
    have hL : L m ≠ z := by
      intro he
      have hzm : z ∈ sourceIsolatingDisc hp hp1 φ N ε m := he ▸ hcluster m (Or.inl rfl)
      exact Set.disjoint_left.mp (hdisjoint n m (Ne.symm hmn)) hz hzm
    have hR : R m ≠ z := by
      intro he
      have hzm : z ∈ sourceIsolatingDisc hp hp1 φ N ε m := he ▸ hcluster m (Or.inr (Or.inl rfl))
      exact Set.disjoint_left.mp (hdisjoint n m (Ne.symm hmn)) hz hzm
    apply Multiset.count_eq_zero.mpr
    intro hm
    have hm' : z = L m ∨ z = R m := by
      simpa only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] using hm
    rcases hm' with he | he
    · exact hL he.symm
    · exact hR he.symm
  have hsum :
      (∑ m ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), ({L m, R m} : Multiset ℂ).count z) =
        ({L n, R n} : Multiset ℂ).count z := by
    apply Finset.sum_eq_single n
    · intro m hm hmn
      exact hzero m hmn
    · intro hn
      exact False.elim (hn hnK)
  have hcount := hcentral.count_eq z
  rw [hsum, if_pos hzcentral] at hcount
  exact hcount.symm

/-- The Cauchy–Riesz projection around every assigned source disc has
complex rank two, including when its two periodic endpoints coincide. -/
theorem sourceIsolatingContour_rank_two
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ ψ : CoeffPair p) (N : ℕ) (ε : ℝ) (hε : 0 < ε)
    (hcluster : ∀ m : ℤ, sourceSpectralCluster hp hp1 ψ m ⊆
      sourceIsolatingDisc hp hp1 φ N ε m)
    (hdisjoint : ∀ i j : ℤ, i ≠ j →
      Disjoint (sourceIsolatingDisc hp hp1 φ N ε i)
        (sourceIsolatingDisc hp hp1 φ N ε j))
    (n : ℤ) :
    Module.finrank ℂ
      (resolventCircleIntegral hp (periodOnePotential ψ)
        (sourceIsolatingCenter hp hp1 φ N n)
        (sourceIsolatingRadius hp hp1 φ N ε n)).range = 2 := by
  let a := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  let b := canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  have hr := (sourceIsolatingRadius_pos hp hp1 φ N ε hε n).le
  have hc := sourceIsolatingSphere_subset_resolventSet hp hp1 φ ψ N ε hε hcluster hdisjoint n
  have hs := enclosedPeriodicSpectrum_sourceIsolating_eq_pair hp hp1 φ ψ N ε hcluster hdisjoint n
  have haMem : a ∈ sourceIsolatingDisc hp hp1 φ N ε n := hcluster n (Or.inl rfl)
  have hbMem : b ∈ sourceIsolatingDisc hp hp1 φ N ε n := hcluster n (Or.inr (Or.inl rfl))
  have haSpec := (canonicalPeriodicEndpoints_mem_spectrum hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) n).1
  have hbSpec := (canonicalPeriodicEndpoints_mem_spectrum hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) n).2
  have ha := periodicMultiplicity_eq_sourceIsolatingPair_count hp hp1 φ ψ N ε
    hcluster hdisjoint n haMem haSpec
  have hb := periodicMultiplicity_eq_sourceIsolatingPair_count hp hp1 φ ψ N ε
    hcluster hdisjoint n hbMem hbSpec
  change periodicAlgebraicMultiplicity hp (periodOnePotential ψ) a =
    ({a, b} : Multiset ℂ).count a at ha
  change periodicAlgebraicMultiplicity hp (periodOnePotential ψ) b =
    ({a, b} : Multiset ℂ).count b at hb
  rw [finrank_range_resolventCircleIntegral hp (periodOnePotential ψ) _ _ hr hc, hs]
  change (∑ z ∈ ({a, b} : Finset ℂ),
    periodicAlgebraicMultiplicity hp (periodOnePotential ψ) z) = 2
  by_cases hab : a = b
  · have hba : b = a := hab.symm
    rw [hba] at ha ⊢
    have ha2 : periodicAlgebraicMultiplicity hp (periodOnePotential ψ) a = 2 := by
      simpa using ha
    simpa [ha2]
  · have ha1 : periodicAlgebraicMultiplicity hp (periodOnePotential ψ) a = 1 := by
      simpa [hab] using ha
    have hb1 : periodicAlgebraicMultiplicity hp (periodOnePotential ψ) b = 1 := by
      simpa [hab, Ne.symm hab] using hb
    simp only [Finset.sum_insert (by simp [hab] : a ∉ ({b} : Finset ℂ)), Finset.sum_singleton]
    rw [ha1, hb1]

end NLS.ZakharovShabat
