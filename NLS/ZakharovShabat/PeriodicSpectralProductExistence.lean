import NLS.ZakharovShabat.PeriodicSpectralProducts

/-!
# Existence of products for the actual periodic spectrum

The proved displacement estimates and counting data give one cutoff and one
open convex neighborhood on which every potential has a convergent product
with exactly its spectral zeros off the free lattice. Convergence here is
pointwise in both parameters; local uniform convergence and analyticity are
separate steps.
-/

noncomputable section
open Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Summability of the paired displacement tail gives full membership for each sequence. -/
theorem memℓp_pair_displacements_of_summable_tail (hp : p ≠ ⊤) (N : ℕ) (ξ η : ℤ → ℂ)
    (hs : Summable (rootDisplacementPowerTail p N ξ η)) :
    Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p ∧
      Memℓp (fun n => η n-(Real.pi : ℂ)*n) p := by
  have hP : 1 ≤ p.toReal :=
    (ENNReal.toReal_le_toReal (by simp) hp).mpr (show 1 ≤ p from Fact.out)
  have hleft (n : ℤ) : spectralDisplacementPowerTail p N ξ n ≤ rootDisplacementPowerTail p N ξ η n := by
    unfold spectralDisplacementPowerTail rootDisplacementPowerTail
    split_ifs
    · exact le_add_of_nonneg_right (by positivity)
    · exact le_rfl
  have hright (n : ℤ) : spectralDisplacementPowerTail p N η n ≤ rootDisplacementPowerTail p N ξ η n := by
    unfold spectralDisplacementPowerTail rootDisplacementPowerTail
    split_ifs
    · exact le_add_of_nonneg_left (by positivity)
    · exact le_rfl
  exact ⟨memℓp_displacement_of_summable_tail (zero_lt_one.trans_le hP) N ξ
    (spectralDisplacementPowerTail_summable_and_le p N ξ _ hs hleft).1,
    memℓp_displacement_of_summable_tail (zero_lt_one.trans_le hP) N η
    (spectralDisplacementPowerTail_summable_and_le p N η _ hs hright).1⟩

/-- Every finite `p>1` potential has an actual periodic spectral product off the free lattice.
One open convex neighborhood and one threshold support the construction for
all larger central cutoffs. No root-label continuity is assumed. -/
theorem exists_uniform_periodicSpectralProducts (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧ ∀ ψ ∈ U,
        ∃ ξ η : ℤ → ℂ,
          Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p ∧
          Memℓp (fun n => η n-(Real.pi : ℂ)*n) p ∧
          (∀ n : ℤ, N₀ < n.natAbs → PeriodicResonantPair hp w ψ n (ξ n) (η n)) ∧
          ∀ N : ℕ, N₀ ≤ N → PeriodicCountingData hp (weightedBaseToPair w ψ) N ∧
            ∀ z : {z : ℂ // z ∉ freeLattice},
              Tendsto (periodicSpectralProductCutoff hp (weightedBaseToPair w ψ) N ξ η z) atTop
                (𝓝 (periodicSpectralProductOffLattice hp (weightedBaseToPair w ψ) N ξ η z)) ∧
              (periodicSpectralProductOffLattice hp (weightedBaseToPair w ψ) N ξ η z = 0 ↔
                z.val ∈ periodicSpectrum hp (weightedBaseToPair w ψ)) := by
  obtain ⟨Nr,hNr,Ur,hor,hcr,hφr,h0r,hroots⟩ :=
    exists_uniform_periodicRoots_with_power_sums hp hp1 w φ
  obtain ⟨Nc,Uc,_,hoc,hcc,hφc,h0c,_,_,hcount⟩ :=
    exists_uniform_periodicCountingData hp (weightedBaseToPair w φ)
  let V := (weightedBaseToPair (p := p) w) ⁻¹' Uc
  have hoV : IsOpen V := hoc.preimage (weightedBaseToPair w).continuous
  have hcV : Convex ℝ V :=
    hcc.linear_preimage ((weightedBaseToPair (p := p) w).restrictScalars ℝ).toLinearMap
  refine ⟨max Nr Nc,hNr.trans (le_max_left _ _),Ur ∩ V,hor.inter hoV,hcr.inter hcV,
    ⟨hφr,hφc⟩,⟨h0r,by simpa [V] using h0c⟩,?_⟩
  intro ψ hψ
  obtain ⟨ξ,η,hr,htail⟩ := hroots ψ hψ.1
  obtain ⟨hξ,hη⟩ := memℓp_pair_displacements_of_summable_tail hp Nr ξ η (htail Nr le_rfl).1
  refine ⟨ξ,η,hξ,hη,fun n hn => hr n (by omega),?_⟩
  intro N hN
  have hc := hcount (weightedBaseToPair w ψ) hψ.2 N (by omega)
  refine ⟨hc,fun z => ⟨tendsto_periodicSpectralProductCutoff hp _ N ξ η hξ hη z,?_⟩⟩
  exact periodicSpectralProductOffLattice_eq_zero_iff hp w ψ N ξ η hξ hη hc
    (fun n hn => hr n (by omega)) z

end NLS.ZakharovShabat
