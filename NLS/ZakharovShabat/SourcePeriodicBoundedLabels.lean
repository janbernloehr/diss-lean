import NLS.ZakharovShabat.SourcePeriodicCounting
import NLS.ZakharovShabat.CentralPeriodicOrdering

/-! # Complete periodic labels with bounded displacement

The initial Section 6 assertion needs only a finite Banach exponent, including
`p = 1`. These labels exhaust the actual original periodic spectrum, retain
the central root multiset and distant algebraic multiplicities, and lie within
`π / 4` of `nπ` outside a common local cutoff. No summable displacement or
continuity of individual labels is asserted at the endpoint exponent.
-/

noncomputable section
open scoped ENNReal Classical
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- An actual central and distant periodic labeling, retaining algebraic multiplicities. -/
structure SourcePeriodicBoundedLabeling (hp : p ≠ ⊤) (φ : CoeffPair p) (N : ℕ) (ξ η : ℤ → ℂ) : Prop where
  counting : SourcePeriodicCountingData hp φ N
  central : CentralPeriodicLabeling hp (CoeffPair.toMax p φ) N ξ η
  distant : ∀ n : ℤ, N < n.natAbs →
    enclosedPeriodicSpectrum hp (CoeffPair.toMax p φ) ((Real.pi : ℂ)*n) (Real.pi/4) = {ξ n,η n} ∧
      (if ξ n = η n then periodicAlgebraicMultiplicity hp (CoeffPair.toMax p φ) (ξ n) = 2 else
        periodicAlgebraicMultiplicity hp (CoeffPair.toMax p φ) (ξ n) = 1 ∧
        periodicAlgebraicMultiplicity hp (CoeffPair.toMax p φ) (η n) = 1)

/-- The two sequences exhaust exactly the original periodic spectrum. -/
theorem SourcePeriodicBoundedLabeling.exhaustive {hp : p ≠ ⊤} {φ : CoeffPair p} {N : ℕ} {ξ η : ℤ → ℂ}
    (h : SourcePeriodicBoundedLabeling hp φ N ξ η) (z : ℂ) :
    z ∉ sourceResolventSet hp φ ↔ ∃ n : ℤ, ξ n = z ∨ η n = z := by
  constructor
  · intro hz
    rcases (h.counting.mem_spectrum_iff_central_or_disk z).mp hz with hc | hd
    · obtain ⟨n,_,hn⟩ := (h.central.root_iff z).mpr hc
      exact ⟨n,hn⟩
    · obtain ⟨n,⟨hn,hzn⟩,_⟩ := hd
      rw [(h.distant n hn).1] at hzn
      exact ⟨n,by simpa only [Finset.mem_insert,Finset.mem_singleton,eq_comm] using hzn⟩
  · rintro ⟨n,hn⟩
    rw [sourceResolventSet_eq]
    change z ∈ periodicSpectrum hp (CoeffPair.toMax p φ)
    by_cases hf : N < n.natAbs
    · have hz : z ∈ enclosedPeriodicSpectrum hp (CoeffPair.toMax p φ) ((Real.pi : ℂ)*n) (Real.pi/4) := by
        rw [(h.distant n hf).1]
        simpa only [Finset.mem_insert,Finset.mem_singleton,eq_comm] using hn
      exact ((mem_enclosedPeriodicSpectrum hp _ _ z _).mp hz).1
    · exact ((mem_centralPeriodicSpectrum hp _ N z).mp
        ((h.central.root_iff z).mp ⟨n,by omega,hn⟩)).1

/-- Each distant label has displacement strictly less than π/4. -/
theorem SourcePeriodicBoundedLabeling.displacement_lt {hp : p ≠ ⊤} {φ : CoeffPair p} {N : ℕ} {ξ η : ℤ → ℂ}
    (h : SourcePeriodicBoundedLabeling hp φ N ξ η) (n : ℤ) (hn : N < n.natAbs) :
    ‖ξ n-(Real.pi : ℂ)*n‖ < Real.pi/4 ∧ ‖η n-(Real.pi : ℂ)*n‖ < Real.pi/4 := by
  have hx : ξ n ∈ enclosedPeriodicSpectrum hp (CoeffPair.toMax p φ) ((Real.pi : ℂ)*n) (Real.pi/4) := by
    rw [(h.distant n hn).1]; simp
  have hy : η n ∈ enclosedPeriodicSpectrum hp (CoeffPair.toMax p φ) ((Real.pi : ℂ)*n) (Real.pi/4) := by
    rw [(h.distant n hn).1]; simp
  exact ⟨by simpa only [Metric.mem_ball,dist_eq_norm] using ((mem_enclosedPeriodicSpectrum hp _ _ _ _).mp hx).2,
    by simpa only [Metric.mem_ball,dist_eq_norm] using ((mem_enclosedPeriodicSpectrum hp _ _ _ _).mp hy).2⟩

/-- Splice central multiplicity labels with the actual pair in every distant disk. -/
theorem exists_sourcePeriodicBoundedLabeling (hp : p ≠ ⊤) (φ : CoeffPair p) (N : ℕ)
    (hc : SourcePeriodicCountingData hp φ N) : ∃ ξ η : ℤ → ℂ, SourcePeriodicBoundedLabeling hp φ N ξ η := by
  obtain ⟨a,b,hab,_,_⟩ := exists_ordered_centralPeriodicLabeling hp _ N hc.coefficient_counts
  choose x y hxy using fun n : {n : ℤ // N < n.natAbs} =>
    hc.coefficient_counts.disk_eigenvalue_pair n.val n.property
  let ξ (n : ℤ) := if hn : N < n.natAbs then x ⟨n,hn⟩ else a n
  let η (n : ℤ) := if hn : N < n.natAbs then y ⟨n,hn⟩ else b n
  refine ⟨ξ,η,hc,⟨?_⟩,?_⟩
  · rw [← hab.roots]
    apply Finset.sum_congr rfl
    intro n hn
    have hlow : ¬ N < n.natAbs := by simp only [Finset.mem_Icc] at hn; omega
    simp only [ξ,η,dif_neg hlow]
  · intro n hn
    simpa only [ξ,η,dif_pos hn] using hxy ⟨n,hn⟩

/-- One original open convex neighborhood admits complete bounded labels for every larger cutoff. -/
theorem exists_uniform_sourcePeriodicBoundedLabeling (hp : p ≠ ⊤) (φ : CoeffPair p) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∃ U : Set (CoeffPair p), IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, ∀ N : ℕ, N₀ ≤ N → ∃ ξ η : ℤ → ℂ, SourcePeriodicBoundedLabeling hp ψ N ξ η := by
  obtain ⟨N₀,U,hN₀,ho,hc,_,hφ,h0,h⟩ := exists_uniform_sourcePeriodicCountingData hp φ
  exact ⟨N₀,hN₀,U,ho,hc,hφ,h0,fun ψ hψ N hN => exists_sourcePeriodicBoundedLabeling hp ψ N ((h N hN).2.2 ψ hψ)⟩

end NLS.ZakharovShabat
