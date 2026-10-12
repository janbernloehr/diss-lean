import NLS.ZakharovShabat.SourceContourRanks
import NLS.ZakharovShabat.SourceEquation1_4
import NLS.ZakharovShabat.PeriodicCounting
import NLS.ZakharovShabat.RealType
import NLS.ZakharovShabat.PhysicalParity

/-! # The rank and counting conclusions following equation (1.5)

The actual original-norm central rectangle has rank 4N+2, and each distant
circle has rank two. For period-one potentials the typed restrictions have
the printed parity ranks. Counts use the established algebraic multiplicities
of the coefficient operator, with coefficient-preserving norm conversion.
The central box here has height N, as in Corollary 3.5 and equations (1.4–1.5).
This does not remove the separate qualification on the printed norm-dependent height.
-/
noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Uniform counting data for the actual original-norm contour operators.
`coefficient_counts` retains the existing algebraic multiplicities and root-space data. -/
structure SourcePeriodicCountingData (hp : p ≠ ⊤) (φ : CoeffPair p) (N : ℕ) : Prop where
  coefficient_counts : PeriodicCountingData hp (CoeffPair.toMax p φ) N
  central_rank : Module.finrank ℂ (sourceCentralRectangleIntegral hp φ N).range = 4*N+2
  disk_rank : ∀ n : ℤ, N < n.natAbs →
    Module.finrank ℂ (sourceResolventCircleIntegral hp φ ((Real.pi : ℂ)*n) (Real.pi/4)).range = 2
  central_parity : φ ∈ sourceParitySubspace 0 → ∀ r : ℤ,
    Module.finrank ℂ (sourceParityCentralProjection hp φ N r).range =
      if (N : ℤ)%2 = r%2 then 2*N+2 else 2*N
  disk_parity : φ ∈ sourceParitySubspace 0 → ∀ n : ℤ, N < n.natAbs → ∀ r : ℤ,
    Module.finrank ℂ (sourceParityCircleProjection hp φ ((Real.pi : ℂ)*n) (Real.pi/4) r).range =
      if n%2 = r%2 then 2 else 0

/-- Transfer the existing counts to the actual source integrals and typed restrictions. -/
theorem sourcePeriodicCountingData_of_coefficients (hp : p ≠ ⊤) (φ : CoeffPair p) (N : ℕ)
    (h : PeriodicCountingData hp (CoeffPair.toMax p φ) N) : SourcePeriodicCountingData hp φ N := by
  have hb : centralRectangleBoundary N ⊆ sourceResolventSet hp φ := by
    rw [sourceResolventSet_eq]
    exact h.central_boundary
  have hd (n : ℤ) (hn : N < n.natAbs) :
      Metric.sphere ((Real.pi : ℂ)*n) (Real.pi/4) ⊆ sourceResolventSet hp φ := by
    rw [sourceResolventSet_eq]
    exact h.disk_resolvent n hn
  refine ⟨h,?_,?_,?_,?_⟩
  · rw [finrank_range_sourceCentralRectangleIntegral hp φ N hb]
    exact h.central_rank
  · intro n hn
    rw [finrank_range_sourceResolventCircleIntegral hp φ _ _ (by positivity) (hd n hn)]
    exact h.disk_rank n hn
  · intro hφ r
    rw [finrank_range_sourceParityCentralProjection hp φ hφ N r hb]
    exact h.central_parity hφ r
  · intro hφ n hn r
    rw [finrank_range_sourceParityCircleProjection hp φ hφ _ _ r (by positivity) (hd n hn),
      finrank_inf_pairParitySubspace_of_le _ n r (h.disk_parity hφ n hn),h.disk_rank n hn]

namespace SourcePeriodicCountingData
variable {hp : p ≠ ⊤} {φ : CoeffPair p} {N : ℕ}

theorem cutoff_pos (h : SourcePeriodicCountingData hp φ N) : 0 < N := h.coefficient_counts.cutoff_pos

theorem central_boundary (h : SourcePeriodicCountingData hp φ N) :
    centralRectangleBoundary N ⊆ sourceResolventSet hp φ := by
  rw [sourceResolventSet_eq]
  exact h.coefficient_counts.central_boundary

theorem disk_resolvent (h : SourcePeriodicCountingData hp φ N) (n : ℤ) (hn : N < n.natAbs) :
    Metric.sphere ((Real.pi : ℂ)*n) (Real.pi/4) ⊆ sourceResolventSet hp φ := by
  rw [sourceResolventSet_eq]
  exact h.coefficient_counts.disk_resolvent n hn

theorem exterior_resolvent (h : SourcePeriodicCountingData hp φ N) :
    spectralExterior N (Real.pi/4) ⊆ sourceResolventSet hp φ := by
  rw [sourceResolventSet_eq]
  exact h.coefficient_counts.exterior_resolvent

/-- These sums count algebraic multiplicities, not merely distinct spectral values. -/
theorem central_multiplicity (h : SourcePeriodicCountingData hp φ N) :
    (∑ z ∈ centralPeriodicSpectrum hp (CoeffPair.toMax p φ) N,
      periodicAlgebraicMultiplicity hp (CoeffPair.toMax p φ) z) = 4*N+2 :=
  h.coefficient_counts.central_multiplicity

theorem disk_multiplicity (h : SourcePeriodicCountingData hp φ N) (n : ℤ) (hn : N < n.natAbs) :
    (∑ z ∈ enclosedPeriodicSpectrum hp (CoeffPair.toMax p φ) ((Real.pi : ℂ)*n) (Real.pi/4),
      periodicAlgebraicMultiplicity hp (CoeffPair.toMax p φ) z) = 2 :=
  h.coefficient_counts.disk_multiplicity n hn

/-- Every vector in the actual distant-circle range has the parity of its index. -/
theorem disk_range_parity (h : SourcePeriodicCountingData hp φ N) (hφ : φ ∈ sourceParitySubspace 0)
    (n : ℤ) (hn : N < n.natAbs) :
    (sourceResolventCircleIntegral hp φ ((Real.pi : ℂ)*n) (Real.pi/4)).range ≤ sourceParitySubspace n := by
  intro a ha
  change CoeffPair.toMax p a ∈ pairParitySubspace n
  apply h.coefficient_counts.disk_parity hφ n hn
  apply (ConjugatedRanges.mem_range (CoeffPair.toMax p) _ a).mp
  rwa [sourceResolventCircleIntegral_eq_conj hp φ _ _ (by positivity) (h.disk_resolvent n hn)] at ha

/-- Eigenvectors in the actual original-norm domain have the disk's parity. -/
theorem disk_eigenvector_parity (h : SourcePeriodicCountingData hp φ N)
    (hφ : φ ∈ sourceParitySubspace 0) (n : ℤ) (hn : N < n.natAbs) (z : ℂ)
    (hz : z ∈ Metric.ball ((Real.pi : ℂ)*n) (Real.pi/4))
    (a : WeightedCoeffPair (Weight.sobolev 1) p)
    (ha : sourceOperator hp φ a = z • sourceDomainInclusion a) :
    a ∈ sourceDomainParitySubspace n := by
  change WeightedCoeffPair.toMax (Weight.sobolev 1) p a ∈ domainParitySubspace n
  apply h.coefficient_counts.disk_eigenvector_parity hφ n hn z hz
  have he := congrArg (CoeffPair.toMax p) ha
  change (CoeffPair.toMax p) ((CoeffPair.toMax p).symm
    (operator hp (CoeffPair.toMax p φ) (WeightedCoeffPair.toMax (Weight.sobolev 1) p a))) =
    (CoeffPair.toMax p) (z • (CoeffPair.toMax p).symm
      (domainInclusion (WeightedCoeffPair.toMax (Weight.sobolev 1) p a))) at he
  simpa only [map_smul,ContinuousLinearEquiv.apply_symm_apply] using he

/-- The physical eigenfunction is periodic for even n and antiperiodic for odd n. -/
theorem disk_eigenvector_unit_translation (h : SourcePeriodicCountingData hp φ N)
    (hφ : φ ∈ sourceParitySubspace 0) (n : ℤ) (hn : N < n.natAbs) (z : ℂ)
    (hz : z ∈ Metric.ball ((Real.pi : ℂ)*n) (Real.pi/4))
    (a : WeightedCoeffPair (Weight.sobolev 1) p)
    (ha : sourceOperator hp φ a = z • sourceDomainInclusion a) (x : ℝ) :
    Fourier.sobolevSynthesis hp a.fst ((x+1 : ℝ) : AddCircle (2 : ℝ)) =
      Fourier.wave n 1 * Fourier.sobolevSynthesis hp a.fst (x : AddCircle (2 : ℝ)) ∧
    Fourier.sobolevSynthesis hp a.snd ((x+1 : ℝ) : AddCircle (2 : ℝ)) =
      Fourier.wave n 1 * Fourier.sobolevSynthesis hp a.snd (x : AddCircle (2 : ℝ)) := by
  have hpar : WeightedCoeffPair.toMax (Weight.sobolev 1) p a ∈ domainParitySubspace n :=
    h.disk_eigenvector_parity hφ n hn z hz a ha
  exact ⟨Fourier.sobolevSynthesis_add_one_of_parity hp a.fst n (fun k hk => (hpar k hk).1) x,
    Fourier.sobolevSynthesis_add_one_of_parity hp a.snd n (fun k hk => (hpar k hk).2) x⟩

/-- No original-norm spectral values occur outside the stated central box and high disks. -/
theorem spectrum_subset (h : SourcePeriodicCountingData hp φ N) :
    (sourceResolventSet hp φ)ᶜ ⊆ centralSpectralBox N ∪ highSpectralDisks N (Real.pi/4) := by
  rw [sourceResolventSet_eq]
  exact h.coefficient_counts.spectrum_subset

/-- Each spectral value lies in the central cluster or in exactly one high disk. -/
theorem mem_spectrum_iff_central_or_disk (h : SourcePeriodicCountingData hp φ N) (z : ℂ) :
    z ∉ sourceResolventSet hp φ ↔
      z ∈ centralPeriodicSpectrum hp (CoeffPair.toMax p φ) N ∨
      ∃! n : ℤ, N < n.natAbs ∧ z ∈ enclosedPeriodicSpectrum hp (CoeffPair.toMax p φ)
        ((Real.pi : ℂ)*n) (Real.pi/4) := by
  rw [sourceResolventSet_eq]
  exact h.coefficient_counts.mem_spectrum_iff_central_or_disk z

theorem analyticOnNhd_exterior (h : SourcePeriodicCountingData hp φ N) :
    AnalyticOnNhd ℂ (sourceResolvent hp φ) (spectralExterior N (Real.pi/4)) :=
  (analyticOnNhd_sourceResolvent hp φ).mono h.exterior_resolvent

end SourcePeriodicCountingData

/-- The real-type conclusion on the full original-norm spectrum, at every finite exponent. -/
theorem sourcePeriodicSpectrum_im_eq_zero_of_realType (hp : p ≠ ⊤) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (z : ℂ) (hz : z ∉ sourceResolventSet hp φ) : z.im = 0 :=
  periodicSpectrum_im_eq_zero_of_realType hp (CoeffPair.toMax p φ) hφ z
    (by rwa [sourceResolventSet_eq] at hz)

/-- One common source neighborhood supports the ranks, algebraic counts,
parity assertions, and analytic actual projectors at every larger cutoff. -/
theorem exists_uniform_sourcePeriodicCountingData (hp : p ≠ ⊤) (φ : CoeffPair p) :
    ∃ N₀ : ℕ, ∃ U : Set (CoeffPair p), 0 < N₀ ∧ IsOpen U ∧ Convex ℝ U ∧ IsConnected U ∧
      φ ∈ U ∧ 0 ∈ U ∧ ∀ N : ℕ, N₀ ≤ N →
      AnalyticOnNhd ℂ (fun ψ => sourceCentralRectangleIntegral hp ψ N) U ∧
      (∀ n : ℤ, N < n.natAbs → AnalyticOnNhd ℂ
        (fun ψ => sourceResolventCircleIntegral hp ψ ((Real.pi : ℂ)*n) (Real.pi/4)) U) ∧
      ∀ ψ ∈ U, SourcePeriodicCountingData hp ψ N := by
  obtain ⟨K,V,hK,hVo,hVc,hφV,h0V,_,_,hcounts⟩ :=
    exists_uniform_periodicCountingData hp (CoeffPair.toMax p φ)
  obtain ⟨L,W,_,hWo,hWc,_,hφW,h0W,han⟩ := sourceEquation1_4 hp φ
  let U : Set (CoeffPair p) := ((CoeffPair.toMax p) ⁻¹' V) ∩ W
  have hc : Convex ℝ U :=
    (hVc.linear_preimage ((CoeffPair.toMax p).toContinuousLinearMap.restrictScalars ℝ).toLinearMap).inter hWc
  have h0U : (0 : CoeffPair p) ∈ U := ⟨by simpa only [Set.mem_preimage,map_zero] using h0V,h0W⟩
  refine ⟨max K L,U,hK.trans_le (le_max_left _ _),
    (hVo.preimage (CoeffPair.toMax p).continuous).inter hWo,hc,⟨⟨0,h0U⟩,hc.isPreconnected⟩,
    ⟨hφV,hφW⟩,h0U,?_⟩
  intro N hN
  have hKN : K ≤ N := (le_max_left _ _).trans hN
  have hLN : L ≤ N := (le_max_right _ _).trans hN
  refine ⟨((han N hLN).1.1).mono Set.inter_subset_right,?_,?_⟩
  · intro n hn
    exact (((han N hLN).2 n hn).1).mono Set.inter_subset_right
  · intro ψ hψ
    exact sourcePeriodicCountingData_of_coefficients hp ψ N (hcounts _ hψ.1 N hKN)

/-- The same complete counts on an open neighborhood in period-one coordinates,
with analytic actual endomorphisms of every parity subspace. -/
theorem exists_uniform_sourcePeriodOneCountingData (hp : p ≠ ⊤) (φ : CoeffPair p) :
    ∃ N₀ : ℕ, ∃ U : Set (CoeffPair p), 0 < N₀ ∧ IsOpen U ∧ Convex ℝ U ∧ IsConnected U ∧
      φ ∈ U ∧ 0 ∈ U ∧ ∀ N : ℕ, N₀ ≤ N →
      (∀ ψ ∈ U, SourcePeriodicCountingData hp (periodOnePair ψ) N) ∧
      ∀ r : ℤ,
        AnalyticOnNhd ℂ (fun ψ => sourceParityCentralProjection hp (periodOnePair ψ) N r) U ∧
        ∀ n : ℤ, N < n.natAbs → AnalyticOnNhd ℂ
          (fun ψ => sourceParityCircleProjection hp (periodOnePair ψ) ((Real.pi : ℂ)*n) (Real.pi/4) r) U := by
  obtain ⟨N₀,V,hN₀,hVo,hVc,_,hφ,h0,h⟩ := exists_uniform_sourcePeriodicCountingData hp (periodOnePair φ)
  let U : Set (CoeffPair p) := periodOnePair ⁻¹' V
  have ho : IsOpen U := hVo.preimage (periodOnePair (p := p)).continuous
  have hc : Convex ℝ U := hVc.linear_preimage
    ((periodOnePair (p := p)).toContinuousLinearMap.restrictScalars ℝ).toLinearMap
  have h0U : (0 : CoeffPair p) ∈ U := by simpa only [U,Set.mem_preimage,map_zero] using h0
  refine ⟨N₀,U,hN₀,ho,hc,⟨⟨0,h0U⟩,hc.isPreconnected⟩,hφ,h0U,?_⟩
  intro N hN
  refine ⟨fun ψ hψ => (h N hN).2.2 _ hψ,?_⟩
  intro r
  refine ⟨?_,?_⟩
  · intro ψ hψ
    exact (analyticAt_sourceParityCompression r _).comp
      (((h N hN).1 _ hψ).comp ((periodOnePair (p := p)).toContinuousLinearMap.analyticAt ψ))
  · intro n hn ψ hψ
    exact analyticAt_sourceParityCircleProjection hp ψ _ _ r (by positivity)
      (((h N hN).2.2 _ hψ).disk_resolvent n hn)

end NLS.ZakharovShabat
