import NLS.ZakharovShabat.SourceStandardRootNegativeTail

/-!
# Index-scale upper bounds for mixed central and tail roots

A finite central block has bounded offsets from its free lattice centers.
The fixed quarter-π tail discs and a triangle inequality give a common
upper bound proportional to the signed index difference, which transfers
to the canonical standard-root norm in both index orientations.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- A central point with bounded lattice offset and a tail-disc point
have distance at most a constant times their index difference. -/
theorem central_tail_pointwise_upper_of_lattice_offset
    (i j : ℤ) (hij : i ≠ j) (R : ℝ) (hR : 0 ≤ R)
    {z w : ℂ}
    (hz : ‖z-(Real.pi:ℂ)*i‖ ≤ R)
    (hw : w ∈ refinedResonantDisk j) :
    dist z w ≤ (R+5*Real.pi/4)*|((i-j : ℤ) : ℝ)| := by
  let d : ℝ := |((i-j : ℤ) : ℝ)|
  have hd : 1 ≤ d := by
    dsimp [d]
    exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hij)
  have hw' : dist w ((Real.pi:ℂ)*j) < Real.pi/4 := by
    simpa only [refinedResonantDisk, mem_ball] using hw
  have hcenter : dist ((Real.pi:ℂ)*i) ((Real.pi:ℂ)*j) = Real.pi*d := by
    simpa only [dist_eq_norm, d] using norm_free_center_sub i j
  have htri := dist_triangle4 z ((Real.pi:ℂ)*i) ((Real.pi:ℂ)*j) w
  rw [hcenter] at htri
  have hz' : dist z ((Real.pi:ℂ)*i) ≤ R := by simpa only [dist_eq_norm] using hz
  have hdiff : 0 ≤ R+Real.pi/4 := by positivity
  have hmul := mul_nonneg hdiff (sub_nonneg.mpr hd)
  rw [dist_comm ((Real.pi:ℂ)*j) w] at htri
  dsimp [d] at *
  nlinarith

/-- The offsets of all points in finitely many central discs from their
respective free lattice centers have one common bound. -/
theorem exists_central_disc_lattice_offset_bound
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (N : ℕ) (ε : ℝ) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ i : ℤ, i.natAbs ≤ N →
      ∀ z ∈ sourceClusterDisc hp hp1 φ (fun _ => ε) i,
        ‖z-(Real.pi:ℂ)*i‖ ≤ R := by
  let s : Finset ℤ := Finset.Icc (-(N:ℤ)) (N:ℤ)
  let C : ℤ → ℂ := fun i =>
    (((canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) i).re +
      (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) i).re)/2 : ℝ)
  let ρ : ℤ → ℝ := fun i =>
    ((canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) i).re -
      (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) i).re)/2 + ε
  let f : ℤ → ℝ := fun i => ‖C i-(Real.pi:ℂ)*i‖ + ρ i
  have hs : s.Nonempty := ⟨0, by simp [s]⟩
  obtain ⟨i₀, hi₀, hmax⟩ := Finset.exists_max_image s f hs
  let R : ℝ := max 0 (f i₀)
  refine ⟨R, le_max_left _ _, ?_⟩
  intro i hi z hz
  have his : i ∈ s := by simp only [s, Finset.mem_Icc]; omega
  have hzi : z ∈ ball (C i) (ρ i) := by simpa only [sourceClusterDisc, C, ρ] using hz
  have hdist : ‖z-C i‖ < ρ i := by
    simpa only [mem_ball, dist_eq_norm] using hzi
  have htri : ‖z-(Real.pi:ℂ)*i‖ ≤ ‖z-C i‖ + ‖C i-(Real.pi:ℂ)*i‖ := by
    have hsum : (z-C i)+(C i-(Real.pi:ℂ)*i) = z-(Real.pi:ℂ)*i := by abel
    simpa only [hsum] using norm_add_le (z-C i) (C i-(Real.pi:ℂ)*i)
  have hfi : f i ≤ R := (hmax i his).trans (le_max_right _ _)
  dsimp [f] at hfi
  linarith

/-- One constant gives the `|m−n|` upper standard-root bound for every
central/tail pair in both orientations, off the indexed gap segment. -/
theorem exists_source_central_tail_root_upper
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (N : ℕ) (ε : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ (ψ : CoeffPair p) (i j : ℤ), i.natAbs ≤ N → N < j.natAbs →
        ∀ z ∈ sourceClusterDisc hp hp1 φ (fun _ => ε) i,
          canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
            (periodOnePotential_mem ψ) j ∈ refinedResonantDisk j →
          canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
            (periodOnePotential_mem ψ) j ∈ refinedResonantDisk j →
          z ∉ sourcePeriodicSegment hp hp1 ψ j →
            ‖sourceStandardRoot hp hp1 ψ j z‖ ≤
              C*|((i-j : ℤ) : ℝ)|) ∧
      (∀ (ψ : CoeffPair p) (i j : ℤ), i.natAbs ≤ N → N < j.natAbs →
        ∀ z ∈ refinedResonantDisk j,
          canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
            (periodOnePotential_mem ψ) i ∈ sourceClusterDisc hp hp1 φ (fun _ => ε) i →
          canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
            (periodOnePotential_mem ψ) i ∈ sourceClusterDisc hp hp1 φ (fun _ => ε) i →
          z ∉ sourcePeriodicSegment hp hp1 ψ i →
            ‖sourceStandardRoot hp hp1 ψ i z‖ ≤
              C*|((i-j : ℤ) : ℝ)|) := by
  obtain ⟨R, hR, hcenter⟩ :=
    exists_central_disc_lattice_offset_bound hp hp1 φ N ε
  let C : ℝ := R+5*Real.pi/4
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_, ?_⟩
  · intro ψ i j hi hj z hz hL hR' hznot
    have hij : i ≠ j := by omega
    have hLdist : ‖canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) j-z‖ ≤ C*|((i-j : ℤ) : ℝ)| := by
      simpa only [dist_eq_norm, norm_sub_rev] using
        central_tail_pointwise_upper_of_lattice_offset i j hij R hR
          (hcenter i hi z hz) hL
    have hRdist : ‖canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) j-z‖ ≤ C*|((i-j : ℤ) : ℝ)| := by
      simpa only [dist_eq_norm, norm_sub_rev] using
        central_tail_pointwise_upper_of_lattice_offset i j hij R hR
          (hcenter i hi z hz) hR'
    exact (sourceStandardRoot_norm_bounds_of_endpoint_bounds hp hp1 ψ j z hznot
      0 (C*|((i-j : ℤ) : ℝ)|) (by positivity) (by positivity)
      (norm_nonneg _) (norm_nonneg _) hLdist hRdist).2
  · intro ψ i j hi hj z hz hL hR' hznot
    have hij : i ≠ j := by omega
    have hLdist : ‖canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) i-z‖ ≤ C*|((i-j : ℤ) : ℝ)| := by
      simpa only [dist_eq_norm] using
        central_tail_pointwise_upper_of_lattice_offset i j hij R hR
          (hcenter i hi _ hL) hz
    have hRdist : ‖canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) i-z‖ ≤ C*|((i-j : ℤ) : ℝ)| := by
      simpa only [dist_eq_norm] using
        central_tail_pointwise_upper_of_lattice_offset i j hij R hR
          (hcenter i hi _ hR') hz
    exact (sourceStandardRoot_norm_bounds_of_endpoint_bounds hp hp1 ψ i z hznot
      0 (C*|((i-j : ℤ) : ℝ)|) (by positivity) (by positivity)
      (norm_nonneg _) (norm_nonneg _) hLdist hRdist).2

end NLS.ZakharovShabat
