import NLS.Articles.KdVPseudomeasures.SpectralComplexRoots
import NLS.SequenceSpaces.OrderedOneSidedEnumeration

/-! Globally ordered actual complex singular labels with the source's exact high slots. -/
noncomputable section
open Set
open scoped ENNReal Classical
namespace NLS.Articles.KdVPseudomeasures
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue NLS.KdV NLS.ComplexAnalysis

/-- The entire original complex physical spectrum has a lexicographic enumeration
with actual central algebraic repetitions and high pairs in slots2n-1,2n. -/
theorem exists_sourceHillComplexLabels (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (N : ℕ) (hN : 2 ≤ N)
    (hs : ∀ n : ℕ, N ≤ n → 13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2)
    (hc : sourceCentralAlgebraicCount r hr q N = 2*N-1) :
    ∃ ell : ℕ → ℂ, (∀ i j : ℕ, i ≤ j → complexLexLE (ell i) (ell j)) ∧
      (∀ z : ℂ, z ∈ sourceHillSpectrum r hr q ↔ ∃ j : ℕ, z = ell j) ∧
      (∀ n : ℕ, N ≤ n → ∃ p : SourceHillComplexPair r hr q n,
        ell (2*n-1) = p.left ∧ ell (2*n) = p.right) ∧
      (∀ z : ℂ, (∑ j ∈ Finset.range (2*N-1), if ell j = z then 1 else 0) =
        if z ∈ sourceCentralSpectrum r hr q N then sourceHillAlgebraicMultiplicity r hr q z else 0) ∧
      ∀ j < 2*N-1, (ell j).re < freeHillValue N-12*(N:ℝ) := by
  obtain ⟨ξ, hξ, hord, hcount⟩ := exists_ordered_sourceComplexCentralRoots r hr q N hc
  have hnarrow (n : ℕ) (hn : N ≤ n) : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2 := by
    have h := endpointHill_small_of_wide_small r hr.2 n (sourceEndpointCoefficients r q)
      (by simpa only [norm_sourceEndpointCoefficients] using hs n hn)
    simpa only [norm_sourceEndpointCoefficients] using h
  let P (k : ℕ) : SourceHillComplexPair r hr q (N+k) :=
    sourceHillComplexPair r hr (N+k) (by omega) q (hnarrow _ (by omega))
  let ell := NLS.appendPairedTail (2*N-1) ξ (fun k => (P k).left) (fun k => (P k).right)
  have hcentral (j : ℕ) (hj : j < 2*N-1) : ξ j ∈ sourceCentralSpectrum r hr q N := by
    apply (mem_sourceComplexCentralRoots_iff r hr q N _).mp
    rw [← hξ]
    simp only [Multiset.mem_sum, Multiset.mem_singleton]
    exact ⟨j, Finset.mem_range.mpr hj, rfl⟩
  have hmono : ∀ i j : ℕ, i ≤ j → complexLexLE (ell i) (ell j) := by
    let key := NLS.appendPairedTail (2*N-1) (fun j => complexLexKey (ξ j))
      (fun k => complexLexKey (P k).left) (fun k => complexLexKey (P k).right)
    have he (j : ℕ) : complexLexKey (ell j) = key j := by
      dsimp [ell, key, NLS.appendPairedTail]
      split_ifs <;> rfl
    have hm : Monotone key := by
      apply NLS.monotone_appendPairedTail
      · exact hord
      · exact fun k => (P k).ordered
      · intro k
        exact complexLexLE_of_re_lt
          (SourceHillComplexPair.right_re_lt_left r hr q (N+k) (by omega) (N+(k+1))
            (by omega) (P k) (P (k+1)))
      · intro j hj
        have hb := ((mem_sourceCentralSpectrum r hr q N _).mp (hcentral j hj)).2
        have hp := SourceHillComplexPair.above_own_separator r hr q N (by omega) (P 0)
        exact complexLexLE_of_re_lt (hb.trans hp)
    intro i j hij
    change complexLexKey (ell i) ≤ complexLexKey (ell j)
    rw [he i, he j]
    exact hm hij
  have hspec (j : ℕ) : ell j ∈ sourceHillSpectrum r hr q := by
    by_cases hj : j < 2*N-1
    · rw [show ell j = ξ j from NLS.appendPairedTail_prefix _ _ _ _ _ hj]
      exact ((mem_sourceCentralSpectrum r hr q N _).mp (hcentral j hj)).1
    · dsimp only [ell, NLS.appendPairedTail]
      rw [if_neg hj]
      split_ifs
      · rw [sourceHillSpectrum_eq]
        exact (P _).left_spectral
      · rw [sourceHillSpectrum_eq]
        exact (P _).right_spectral
  refine ⟨ell, hmono, ?_, ?_, ?_, ?_⟩
  · intro z
    constructor
    · intro hz
      by_cases hb : z.re < freeHillValue N-12*(N:ℝ)
      · have hm : z ∈ sourceComplexCentralRoots r hr q N :=
          (mem_sourceComplexCentralRoots_iff r hr q N z).mpr
            ((mem_sourceCentralSpectrum r hr q N z).mpr ⟨hz, hb⟩)
        rw [← hξ] at hm
        simp only [Multiset.mem_sum, Multiset.mem_singleton] at hm
        obtain ⟨j, hj, hjz⟩ := hm
        refine ⟨j, ?_⟩
        rw [show ell j = ξ j from NLS.appendPairedTail_prefix _ _ _ _ _ (Finset.mem_range.mp hj)]
        exact hjz
      · obtain ⟨n, hn, hstrip, _⟩ := sourceHillSpectrum_complex_high_cover r hr q N hN hs z hz (le_of_not_gt hb)
        have hnk : N+(n-N) = n := by omega
        have hp := (SourceHillComplexPair.spectrum_iff r hr q (N+(n-N)) (P (n-N)) z
          (by rwa [hnk])).mp hz
        rcases hp with hp | hp
        · refine ⟨(2*N-1)+2*(n-N), ?_⟩
          have hj : ell ((2*N-1)+2*(n-N)) = (P (n-N)).left :=
            NLS.appendPairedTail_even _ _ _ _ (n-N)
          exact hp.trans hj.symm
        · refine ⟨(2*N-1)+2*(n-N)+1, ?_⟩
          have hj : ell ((2*N-1)+2*(n-N)+1) = (P (n-N)).right :=
            NLS.appendPairedTail_odd _ _ _ _ (n-N)
          exact hp.trans hj.symm
    · rintro ⟨j, rfl⟩
      exact hspec j
  · intro n hn
    obtain ⟨k, hk⟩ : ∃ k : ℕ, n = N+k := ⟨n-N, by omega⟩
    subst n
    refine ⟨P k, ?_, ?_⟩
    · have hj : 2*(N+k)-1 = (2*N-1)+2*k := by omega
      change NLS.appendPairedTail _ _ _ _ _ = _
      rw [hj, NLS.appendPairedTail_even]
    · have hj : 2*(N+k) = (2*N-1)+2*k+1 := by omega
      change NLS.appendPairedTail _ _ _ _ _ = _
      rw [hj, NLS.appendPairedTail_odd]
  · intro z
    rw [← hcount z]
    apply Finset.sum_congr rfl
    intro j hj
    rw [show ell j = ξ j from NLS.appendPairedTail_prefix _ _ _ _ _ (Finset.mem_range.mp hj)]
  · intro j hj
    rw [show ell j = ξ j from NLS.appendPairedTail_prefix _ _ _ _ _ hj]
    exact ((mem_sourceCentralSpectrum r hr q N _).mp (hcentral j hj)).2

/-- A physical labeling with actual multiplicities and source lexicographic order. -/
structure SourceHillComplexLabeling (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (N : ℕ) (ell : ℕ → ℂ) : Prop where
  cutoff_ge_two : 2 ≤ N
  cutoff_small : ∀ n : ℕ, N ≤ n → 13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2
  monotone : ∀ i j : ℕ, i ≤ j → complexLexLE (ell i) (ell j)
  spectrum : ∀ z : ℂ, z ∈ sourceHillSpectrum r hr q ↔ ∃ j : ℕ, z = ell j
  high_pair : ∀ n : ℕ, N ≤ n → ∃ p : SourceHillComplexPair r hr q n,
    ell (2*n-1) = p.left ∧ ell (2*n) = p.right
  central_counts : ∀ z : ℂ, (∑ j ∈ Finset.range (2*N-1), if ell j = z then 1 else 0) =
    if z ∈ sourceCentralSpectrum r hr q N then sourceHillAlgebraicMultiplicity r hr q z else 0
  central_below : ∀ j < 2*N-1, (ell j).re < freeHillValue N-12*(N:ℝ)

/-- One cutoff BEFORE an original complex norm ball constructs global actual labelings
without a supplied spectral list or a supplied counting hypothesis. -/
theorem source_uniform_complex_labeling (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ q : FourierLebesgueSpace (2:ℝ) (-r) ⊤, ‖q‖ ≤ R →
      ∃ ell : ℕ → ℂ, SourceHillComplexLabeling r hr q N ell := by
  obtain ⟨N, hN, hs, hc⟩ := source_uniform_all_complex_central_counts r hr R
  refine ⟨N, hN, fun q hq => ?_⟩
  have hsmall (n : ℕ) (hn : N ≤ n) : 13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2 :=
    (mul_le_mul_of_nonneg_left hq (by positivity [endpointHillConstant_pos r hr.2])).trans (hs n hn)
  obtain ⟨ell, hm, hsp, hp, hcnt, hb⟩ := exists_sourceHillComplexLabels r hr q N hN hsmall (hc q hq N le_rfl)
  exact ⟨ell, ⟨hN, hsmall, hm, hsp, hp, hcnt, hb⟩⟩

end NLS.Articles.KdVPseudomeasures
