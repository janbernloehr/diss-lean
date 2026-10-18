import NLS.ZakharovShabat.SourceStandardRootMixedBounds
import NLS.ZakharovShabat.SourceStandardRootCentralBounded
import NLS.ZakharovShabat.SourceIsolatingContourGeometry

/-! # Index-scale separation of localized source-disc points

Central half-margin discs and the refined tail discs give a common lower
bound proportional to the index distance. This geometric lemma is shared
by the midpoint and arbitrary-periodic-segment estimates.
-/

noncomputable section
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- One geometric constant controls every point in the central half-margin or refined tail discs. -/
theorem exists_source_disc_point_index_separation
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (N : ℕ) (ε : ℝ) (hε : 0 < ε) (hεmax : ε ≤ Real.pi/4)
    (houterL : canonicalPeriodicLeft hp hp1 (periodOnePotential φ)
      (periodOnePotential_mem φ) (-(N : ℤ)) ∈ refinedResonantDisk (-(N : ℤ)))
    (houterR : canonicalPeriodicRight hp hp1 (periodOnePotential φ)
      (periodOnePotential_mem φ) (N : ℤ) ∈ refinedResonantDisk (N : ℤ))
    (hgap : ∀ i j : ℤ, i.natAbs ≤ N → j.natAbs ≤ N → i < j →
      2*ε ≤
        (canonicalPeriodicLeft hp hp1 (periodOnePotential φ)
          (periodOnePotential_mem φ) j).re -
        (canonicalPeriodicRight hp hp1 (periodOnePotential φ)
          (periodOnePotential_mem φ) i).re)
    : ∃ C : ℝ, 1 ≤ C ∧ ∀ i j : ℤ, i ≠ j →
        ∀ z ∈ sourceIsolatingDisc hp hp1 φ N ε i,
        ∀ w ∈ (if j.natAbs ≤ N then sourceClusterDisc hp hp1 φ (fun _ => ε/2) j
          else refinedResonantDisk j),
          |((i-j : ℤ) : ℝ)| ≤ C * ‖w-z‖ := by
  obtain ⟨R,hR,hcenter⟩ :=
    exists_central_disc_lattice_offset_bound hp hp1 φ N ε
  let B : ℝ := 1+4*R+Real.pi
  let C : ℝ := max 1 (max ((4*(N:ℝ)+2)/ε) B)
  have hC : 1 ≤ C := le_max_left _ _
  have hC0 : 0 ≤ C := by linarith
  have hCB : B ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  have hCc : (4*(N:ℝ)+2)/ε ≤ C :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hscale : 4*(N:ℝ)+2 ≤ C*ε := by
    exact (div_le_iff₀ hε).mp hCc
  refine ⟨C,hC,?_⟩
  intro i j hij z hz w hwloc
  have hdist : dist z w = ‖w-z‖ := by simp only [dist_eq_norm, norm_sub_rev]
  have hd : 0 ≤ |((i-j : ℤ) : ℝ)| := abs_nonneg _
  by_cases hi : i.natAbs ≤ N
  · have hzi : z ∈ sourceClusterDisc hp hp1 φ (fun _ => ε) i := by
      simpa only [sourceIsolatingDisc, if_pos hi] using hz
    by_cases hj : j.natAbs ≤ N
    · have hw : w ∈ sourceClusterDisc hp hp1 φ (fun _ => ε/2) j :=
        by simpa only [if_pos hj] using hwloc
      have hsep : ε/2 ≤ dist z w := by
        rcases lt_or_gt_of_ne hij with hlt | hgt
        · exact sourceCentralDisc_pointwise_separation hp hp1 φ ε hε
            (hgap i j hi hj hlt) hzi hw
        · exact sourceCentralDisc_pointwise_separation_rev hp hp1 φ ε hε
            (hgap j i hj hi hgt) hzi hw
      have hdmax : |((i-j : ℤ) : ℝ)| ≤ 2*(N:ℝ) := by
        have hii : -(N:ℤ) ≤ i ∧ i ≤ (N:ℤ) := by omega
        have hjj : -(N:ℤ) ≤ j ∧ j ≤ (N:ℤ) := by omega
        have hreal1 : -(2*(N:ℝ)) ≤ ((i-j:ℤ):ℝ) := by exact_mod_cast (show -(2*(N:ℤ)) ≤ i-j by omega)
        have hreal2 : ((i-j:ℤ):ℝ) ≤ 2*(N:ℝ) := by exact_mod_cast (show i-j ≤ 2*(N:ℤ) by omega)
        exact abs_le.mpr ⟨hreal1,hreal2⟩
      rw [← hdist]
      nlinarith [mul_nonneg hC0 (sub_nonneg.mpr hsep)]
    · have hj' : N < j.natAbs := by omega
      have hw : w ∈ refinedResonantDisk j := by simpa only [if_neg hj] using hwloc
      obtain ⟨_,hpoint⟩ := source_central_tail_pointwise_geometry
        hp hp1 φ hφ N ε hε.le hεmax houterL houterR i j hi hj'
      have hsep : Real.pi/4 ≤ dist z w := hpoint z hzi w hw
      have hb : |((i-j : ℤ) : ℝ)| ≤ B*dist z w :=
        central_tail_pointwise_index_lower i j R hR
          (hcenter i hi z hzi) hw hsep
      rw [← hdist]
      exact hb.trans (mul_le_mul_of_nonneg_right hCB (dist_nonneg))
  · have hi' : N < i.natAbs := by omega
    have hzi : z ∈ refinedResonantDisk i := by
      simpa only [sourceIsolatingDisc, if_neg hi] using hz
    by_cases hj : j.natAbs ≤ N
    · have hwSmall : w ∈ sourceClusterDisc hp hp1 φ (fun _ => ε/2) j :=
        by simpa only [if_pos hj] using hwloc
      have hw : w ∈ sourceClusterDisc hp hp1 φ (fun _ => ε) j :=
        sourceClusterDisc_mono_constant_margin hp hp1 φ (ε/2) ε (by linarith) j hwSmall
      obtain ⟨_,hpoint⟩ := source_central_tail_pointwise_geometry
        hp hp1 φ hφ N ε hε.le hεmax houterL houterR j i hj hi'
      have hsep : Real.pi/4 ≤ dist w z := hpoint w hw z hzi
      have hb : |((j-i : ℤ) : ℝ)| ≤ B*dist w z :=
        central_tail_pointwise_index_lower j i R hR
          (hcenter j hj w hw) hzi hsep
      have habs : |((j-i : ℤ) : ℝ)| = |((i-j : ℤ) : ℝ)| := by
        rw [show j-i = -(i-j) by ring, Int.cast_neg, abs_neg]
      rw [habs, dist_comm] at hb
      rw [← hdist]
      exact hb.trans (mul_le_mul_of_nonneg_right hCB (dist_nonneg))
    · have hj' : N < j.natAbs := by omega
      have hw : w ∈ refinedResonantDisk j := by simpa only [if_neg hj] using hwloc
      have ht := (refinedResonantDisk_pointwise_separation hij hzi hw).1
      have hπ : (1:ℝ) ≤ Real.pi/2 := by linarith [Real.pi_gt_three]
      rw [← hdist]
      nlinarith [mul_nonneg (sub_nonneg.mpr hπ) hd,
        mul_nonneg (sub_nonneg.mpr hC) (dist_nonneg : 0 ≤ dist z w)]


end NLS.ZakharovShabat
