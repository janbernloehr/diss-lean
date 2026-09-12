import NLS.ZakharovShabat.CentralDeformation
import NLS.ZakharovShabat.DiskParity

/-!
# Parity components of the central spectral projection

The even/odd central projectors deform continuously within the even potentials.
Their free ranks are obtained by filtering the signed free spectral indices.
Rank stability proves the `2N+2` versus `2N` split in Proposition 1.1(ii),
uniformly on a common neighborhood for every sufficiently large cutoff.
-/

noncomputable section
open Complex Metric Topology
open scoped ENNReal

namespace NLS.ZakharovShabat

/-- The signed central indices with the indicated parity. -/
def centralParityIndices (N : ℕ) (r : ℤ) : Finset ℤ :=
  (Finset.Icc (-(N : ℤ)) N).filter (fun n => n % 2 = r % 2)

/-- Counting signed indices gives one additional index precisely in the parity
of the cutoff. -/
theorem card_centralParityIndices (N : ℕ) (r : ℤ) :
    (centralParityIndices N r).card = N + if (N : ℤ) % 2 = r % 2 then 1 else 0 := by
  induction N with
  | zero =>
    simp only [centralParityIndices, Nat.cast_zero, neg_zero, Finset.Icc_self,
      Finset.filter_singleton, Int.zero_emod]
    split_ifs <;> simp
  | succ N ih =>
    have he : Finset.Icc (-((N + 1 : ℕ) : ℤ)) ((N + 1 : ℕ) : ℤ) =
        insert (-((N + 1 : ℕ) : ℤ)) (insert ((N + 1 : ℕ) : ℤ) (Finset.Icc (-(N : ℤ)) N)) := by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_insert, Nat.cast_add, Nat.cast_one]
      omega
    have hp : ((N + 1 : ℕ) : ℤ) ∉ Finset.Icc (-(N : ℤ)) N := by simp
    have hm : -((N + 1 : ℕ) : ℤ) ∉ insert ((N + 1 : ℕ) : ℤ) (Finset.Icc (-(N : ℤ)) N) := by
      simp only [Finset.mem_insert, Finset.mem_Icc, Nat.cast_add, Nat.cast_one]
      omega
    have hneg : (-((N + 1 : ℕ) : ℤ)) % 2 = ((N + 1 : ℕ) : ℤ) % 2 := by omega
    unfold centralParityIndices at ih ⊢
    rw [he, Finset.filter_insert, Finset.filter_insert, hneg]
    split_ifs with h
    · have hmfilter : -((N + 1 : ℕ) : ℤ) ∉ insert ((N + 1 : ℕ) : ℤ)
          ((Finset.Icc (-(N : ℤ)) N).filter (fun n => n % 2 = r % 2)) := by
        intro hn
        rcases Finset.mem_insert.mp hn with heq | hmem
        · exact hm (Finset.mem_insert.mpr (Or.inl heq))
        · exact hm (Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mp hmem).1))
      rw [Finset.card_insert_of_notMem hmfilter,
        Finset.card_insert_of_notMem (fun hn => hp (Finset.mem_filter.mp hn).1), ih]
      split_ifs <;> omega
    · rw [ih]
      split_ifs <;> omega

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The parity component of the central algebraic projection on the full base
space. Under commutation its range equals the corresponding parity intersection. -/
def centralParityProjection (hp : p ≠ ⊤) (φ : PairSpace p) (N : ℕ) (r : ℤ) :
    PairSpace p →L[ℂ] PairSpace p :=
  pairParityProjection r * centralSpectralProjection hp φ N

/-- The parity mask selects or kills both signed free modes together. -/
theorem pairParityProjection_freeModeEmbedding (r n : ℤ) (a : ℂ × ℂ) :
    pairParityProjection r (freeModeEmbedding (p := p) n a) =
      if n % 2 = r % 2 then freeModeEmbedding n a else 0 := by
  by_cases h : n % 2 = r % 2
  · have hn : (-n) % 2 = r % 2 := by omega
    simp [pairParityProjection_apply, Coeff.parityProjection_single, h, hn]
  · simp [pairParityProjection_apply, Coeff.parityProjection_single, h]

/-- The same selection law holds for the whole free spectral projector. -/
theorem pairParityProjection_freeSpectralProjection (hp : p ≠ ⊤) (r n : ℤ) :
    pairParityProjection r * periodicSpectralProjection (p := p) hp 0 ((Real.pi : ℂ) * n) =
      if n % 2 = r % 2 then periodicSpectralProjection hp 0 ((Real.pi : ℂ) * n) else 0 := by
  apply ContinuousLinearMap.ext
  intro x
  have hx : periodicSpectralProjection hp 0 ((Real.pi : ℂ) * n) x ∈ (freeModeEmbedding n).range := by
    rw [← periodicRootSpaceTop_zero_eq_range hp n, ← range_periodicSpectralProjection]
    exact ⟨x, rfl⟩
  obtain ⟨a, ha⟩ := hx
  change freeModeEmbedding n a = periodicSpectralProjection hp 0 ((Real.pi : ℂ) * n) x at ha
  change pairParityProjection r (periodicSpectralProjection hp 0 ((Real.pi : ℂ) * n) x) = _
  rw [← ha, pairParityProjection_freeModeEmbedding]
  split_ifs with h
  · exact ha
  · rfl

private theorem free_index_injective : Function.Injective (fun n : ℤ => (Real.pi : ℂ) * n) := by
  intro a b h
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  exact_mod_cast mul_left_cancel₀ hπ h

/-- The free central parity projector is exactly the cluster of the free indices
with the requested residue. -/
theorem centralParityProjection_zero_eq_cluster (hp : p ≠ ⊤) (N : ℕ) (r : ℤ) :
    centralParityProjection (p := p) hp 0 N r = periodicClusterProjection hp 0
      ((centralParityIndices N r).image (fun n : ℤ => (Real.pi : ℂ) * n)) := by
  classical
  unfold centralParityProjection centralSpectralProjection periodicClusterProjection
  rw [centralPeriodicSpectrum_zero, Finset.sum_image (fun _ _ _ _ h => free_index_injective h),
    Finset.sum_image (fun _ _ _ _ h => free_index_injective h), Finset.mul_sum]
  simp only [pairParityProjection_freeSpectralProjection, centralParityIndices, Finset.sum_filter]

/-- Free central parity ranks give the `2N+2` versus `2N` split. -/
theorem finrank_range_centralParityProjection_zero (hp : p ≠ ⊤) (N : ℕ) (r : ℤ) :
    Module.finrank ℂ (centralParityProjection (p := p) hp 0 N r).range =
      if (N : ℤ) % 2 = r % 2 then 2 * N + 2 else 2 * N := by
  classical
  rw [centralParityProjection_zero_eq_cluster, finrank_range_periodicClusterProjection,
    Finset.sum_image (fun _ _ _ _ h => free_index_injective h)]
  simp only [periodicAlgebraicMultiplicity_zero, Finset.sum_const, smul_eq_mul, card_centralParityIndices]
  split_ifs <;> omega

/-- Each central parity component has finite rank, even before imposing invariance. -/
theorem finiteDimensional_range_centralParityProjection (hp : p ≠ ⊤) (φ : PairSpace p)
    (N : ℕ) (r : ℤ) : FiniteDimensional ℂ (centralParityProjection hp φ N r).range := by
  let P := centralSpectralProjection hp φ N
  let A := pairParityProjection (p := p) r
  let : FiniteDimensional ℂ P.range := by
    change FiniteDimensional ℂ (periodicClusterProjection hp φ (centralPeriodicSpectrum hp φ N)).range
    rw [range_periodicClusterProjection]
    exact finiteDimensional_periodicClusterSpace hp φ _
  have he : (centralParityProjection hp φ N r).range = P.range.map A.toLinearMap := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨P x, ⟨x, rfl⟩, rfl⟩
    · rintro ⟨x, ⟨u, hu⟩, hy⟩
      refine ⟨u, ?_⟩
      change A (P u) = y
      change P u = x at hu
      rw [hu]
      exact hy
  rw [he]
  infer_instance

/-- Commuting central and parity projections give a projection onto precisely
the corresponding part of the central spectral space. -/
theorem range_centralParityProjection (hp : p ≠ ⊤) (φ : PairSpace p) (N : ℕ) (r : ℤ)
    (hc : Commute (pairParityProjection r) (centralSpectralProjection hp φ N)) :
    (centralParityProjection hp φ N r).range =
      (centralSpectralProjection hp φ N).range ⊓ pairParitySubspace r := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨⟨pairParityProjection r x, ?_⟩, pairParityProjection_mem r _⟩
    exact (DFunLike.congr_fun hc.eq x).symm
  · rintro ⟨⟨x, hx⟩, hy⟩
    refine ⟨x, ?_⟩
    change pairParityProjection r (centralSpectralProjection hp φ N x) = y
    change centralSpectralProjection hp φ N x = y at hx
    rw [hx]
    exact (pairParityProjection_eq_self_iff r y).mpr hy

/-- Parity components inherit the central projection's ambient analyticity. -/
theorem analyticAt_centralParityProjection (hp : p ≠ ⊤) (φ : PairSpace p) (N : ℕ) (r : ℤ)
    (ha : AnalyticAt ℂ (fun ψ => centralSpectralProjection hp ψ N) φ) :
    AnalyticAt ℂ (fun ψ => centralParityProjection hp ψ N r) φ :=
  analyticAt_const.mul ha

/-- Proposition 1.1(ii)'s parity count: for every sufficiently large cutoff and
all even potentials in one convex neighborhood, the cutoff's parity has rank
`2N+2` and the other parity has rank `2N`. The ranges are exactly the parity
intersections with the full central spectral space. -/
theorem exists_uniform_central_parity_ranks (hp : p ≠ ⊤) (φ : PairSpace p) :
    ∃ N₀ : ℕ, ∃ U : Set (PairSpace p), 0 < N₀ ∧ IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, ψ ∈ pairParitySubspace 0 → ∀ N : ℕ, N₀ ≤ N → ∀ r : ℤ,
        Module.finrank ℂ (centralParityProjection hp ψ N r).range =
          (if (N : ℤ) % 2 = r % 2 then 2 * N + 2 else 2 * N) ∧
        (centralParityProjection hp ψ N r).range =
          (centralSpectralProjection hp ψ N).range ⊓ pairParitySubspace r := by
  obtain ⟨N₀, U, hN₀, ho, hconv, hφ, h0, hcircle⟩ := exists_uniform_centralCircle hp φ
  refine ⟨N₀, U, hN₀, ho, hconv, hφ, h0, ?_⟩
  intro ψ hψ heven N hN r
  let V := U ∩ (pairParitySubspace (p := p) 0 : Set (PairSpace p))
  have hV : Convex ℝ V := hconv.inter ((pairParitySubspace (p := p) 0).restrictScalars ℝ).convex
  have hcomm (a : PairSpace p) (ha : a ∈ V) :
      Commute (pairParityProjection r) (centralSpectralProjection hp a N) := by
    rw [(hcircle a ha.1 N hN).2.2.2]
    exact pairParityProjection_commute_contour hp a ha.2 r 0 _
      (centralCircleRadius_pos N).le (hcircle a ha.1 N hN).2.1
  have hcontCircle : ContinuousOn (fun a => resolventCircleIntegral hp a 0 (centralCircleRadius N)) V := by
    intro a ha
    exact (analyticAt_resolventCircleIntegral hp a 0 _ (centralCircleRadius_pos N).le
      (hcircle a ha.1 N hN).2.1).continuousAt.continuousWithinAt
  have hcont : ContinuousOn (fun a => centralParityProjection hp a N r) V := by
    apply (continuousOn_const.mul hcontCircle).congr
    intro a ha
    exact congrArg (fun P => pairParityProjection r * P) (hcircle a ha.1 N hN).2.2.2
  have hid (a : PairSpace p) (ha : a ∈ V) : IsIdempotentElem (centralParityProjection hp a N r) :=
    IsIdempotentElem.mul_of_commute (hcomm a ha) (pairParityProjection_idempotent r)
      (centralSpectralProjection_idempotent hp a N)
  have heq := NLS.ProjectionRank.finrank_eq_on_preconnected hV.isPreconnected
    (fun a => centralParityProjection hp a N r) hcont hid
    (fun a _ => finiteDimensional_range_centralParityProjection hp a N r)
    (show ψ ∈ V from ⟨hψ, heven⟩) (show (0 : PairSpace p) ∈ V from ⟨h0, Submodule.zero_mem _⟩)
  exact ⟨heq.trans (finrank_range_centralParityProjection_zero hp N r),
    range_centralParityProjection hp ψ N r (hcomm ψ ⟨hψ, heven⟩)⟩

/-- The full central count and its parity split share one cutoff and one open
convex neighborhood. Both the central and parity-component projections are
analytic, and the parity dimensions count the corresponding central root spaces. -/
theorem exists_uniform_central_counts (hp : p ≠ ⊤) (φ : PairSpace p) :
    ∃ N₀ : ℕ, ∃ U : Set (PairSpace p), 0 < N₀ ∧ IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      (∀ N : ℕ, N₀ ≤ N → AnalyticOnNhd ℂ (fun ψ => centralSpectralProjection hp ψ N) U ∧
        ∀ r : ℤ, AnalyticOnNhd ℂ (fun ψ => centralParityProjection hp ψ N r) U) ∧
      ∀ ψ ∈ U, ∀ N : ℕ, N₀ ≤ N → centralRectangleBoundary N ⊆ resolventSet hp ψ ∧
        Module.finrank ℂ (centralSpectralProjection hp ψ N).range = 4 * N + 2 ∧
        (∑ z ∈ centralPeriodicSpectrum hp ψ N, periodicAlgebraicMultiplicity hp ψ z) = 4 * N + 2 ∧
        (ψ ∈ pairParitySubspace 0 → ∀ r : ℤ,
          Module.finrank ℂ ↥((centralSpectralProjection hp ψ N).range ⊓ pairParitySubspace r) =
            if (N : ℤ) % 2 = r % 2 then 2 * N + 2 else 2 * N) := by
  obtain ⟨Nc, Uc, hNc, hoc, hcc, hφc, h0c, han, hc⟩ := exists_uniform_central_multiplicity hp φ
  obtain ⟨Np, Up, _, hop, hcp, hφp, h0p, hpcount⟩ := exists_uniform_central_parity_ranks hp φ
  refine ⟨max Nc Np, Uc ∩ Up, hNc.trans_le (le_max_left _ _), hoc.inter hop,
    hcc.inter hcp, ⟨hφc, hφp⟩, ⟨h0c, h0p⟩, ?_, ?_⟩
  · intro N hN
    have hNcN := (le_max_left Nc Np).trans hN
    refine ⟨(han N hNcN).mono Set.inter_subset_left, ?_⟩
    intro r ψ hψ
    exact analyticAt_centralParityProjection hp ψ N r (han N hNcN ψ hψ.1)
  · intro ψ hψ N hN
    obtain ⟨hb, hrank, hsum⟩ := hc ψ hψ.1 N ((le_max_left Nc Np).trans hN)
    refine ⟨hb, hrank, hsum, ?_⟩
    intro heven r
    obtain ⟨hpar, heq⟩ := hpcount ψ hψ.2 heven N ((le_max_right Nc Np).trans hN) r
    rw [← heq]
    exact hpar

end NLS.ZakharovShabat
