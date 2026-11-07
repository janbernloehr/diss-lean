import NLS.Articles.KdVPseudomeasures.SpectralCentralRoots
import NLS.SequenceSpaces.OrderedOneSidedEnumeration
import NLS.SequenceSpaces.OrderedEnumerationFiniteException

/-! Globally ordered actual singular spectral labels, retaining the physical multiplicities. -/
noncomputable section
open Set
open scoped ENNReal Classical
namespace NLS.Articles.KdVPseudomeasures
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue NLS.KdV

/-- The first high pair is strictly above the central separator. -/
theorem SourceHillRealPair.above_own_separator (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : Potential r) (n : ℕ) (hn : 1 ≤ n) (p : SourceHillRealPair r hr q n) :
    freeHillValue n-12*(n:ℝ) < p.left := by
  have hp : |p.left-freeHillValue n| ≤ 6*(n:ℝ) := p.left_mem
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  linarith [(abs_le.mp hp).1]

/-- The actual physical spectrum has an ordered global enumeration with the exact central repetitions
and each high pair in the source slots 2n-1 and 2n. -/
theorem exists_sourceHillRealLabels (r : ℝ) (hr : AdmissiblePredualOrder r) (q : Potential r)
    (N : ℕ) (hN : 2 ≤ N)
    (hs : ∀ n : ℕ, N ≤ n → 13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q.val‖ ≤ 1/2) :
    ∃ ell : ℕ → ℝ, Monotone ell ∧
      (∀ z : ℂ, z ∈ sourceHillSpectrum r hr q.val ↔ ∃ j : ℕ, z = (ell j:ℂ)) ∧
      (∀ n : ℕ, N ≤ n → ∃ p : SourceHillRealPair r hr q n,
        ell (2*n-1) = p.left ∧ ell (2*n) = p.right) ∧
      (∀ x : ℝ, (∑ j ∈ Finset.range (2*N-1), if ell j = x then 1 else 0) =
        if (x:ℂ) ∈ sourceCentralSpectrum r hr q.val N then sourceHillAlgebraicMultiplicity r hr q.val x else 0) ∧
      ∀ j < 2*N-1, ell j < freeHillValue N-12*(N:ℝ) := by
  obtain ⟨ξ,hξ,hord,hcount⟩ := exists_ordered_sourceCentralRoots r hr q N hN (hs N le_rfl)
  have hnarrow (n : ℕ) (hn : N ≤ n) : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q.val‖ ≤ 1/2 := by
    have h := endpointHill_small_of_wide_small r hr.2 n (sourceEndpointCoefficients r q.val)
      (by simpa only [norm_sourceEndpointCoefficients] using hs n hn)
    simpa only [norm_sourceEndpointCoefficients] using h
  let P (k : ℕ) : SourceHillRealPair r hr q (N+k) :=
    sourceHillRealPair r hr (N+k) (by omega) q (hnarrow _ (by omega))
  let ell := NLS.appendPairedTail (2*N-1) ξ (fun k => (P k).left) (fun k => (P k).right)
  have hcentral (j : ℕ) (hj : j < 2*N-1) :
      (ξ j:ℂ) ∈ sourceCentralSpectrum r hr q.val N := by
    apply (mem_sourceRealCentralRoots_iff r hr q N _).mp
    rw [← hξ]
    simp only [Multiset.mem_sum,Multiset.mem_singleton]
    exact ⟨j,Finset.mem_range.mpr hj,rfl⟩
  have hmono : Monotone ell := by
    apply NLS.monotone_appendPairedTail (2*N-1) ξ (fun k => (P k).left) (fun k => (P k).right) hord
    · exact fun k => (P k).ordered
    · intro k
      exact (SourceHillRealPair.right_lt_left r hr q (N+k) (by omega) (N+(k+1))
        (by omega) (P k) (P (k+1))).le
    · intro j hj
      have hb := ((mem_sourceCentralSpectrum r hr q.val N _).mp (hcentral j hj)).2
      have hp := SourceHillRealPair.above_own_separator r hr q N (by omega) (P 0)
      exact hb.le.trans hp.le
  have hspec (j : ℕ) : (ell j:ℂ) ∈ sourceHillSpectrum r hr q.val := by
    by_cases hj : j < 2*N-1
    · rw [show ell j = ξ j from NLS.appendPairedTail_prefix _ _ _ _ _ hj]
      exact ((mem_sourceCentralSpectrum r hr q.val N _).mp (hcentral j hj)).1
    · dsimp only [ell,NLS.appendPairedTail]
      rw [if_neg hj]
      split_ifs
      · rw [sourceHillSpectrum_eq]
        exact (P _).left_spectral
      · rw [sourceHillSpectrum_eq]
        exact (P _).right_spectral
  refine ⟨ell,hmono,?_,?_,?_,?_⟩
  · intro z
    constructor
    · intro hz
      have him := sourceHillSpectrum_ofPotential_real r hr q z hz
      have he : (z.re:ℂ) = z := by apply Complex.ext <;> simp [him]
      by_cases hb : z.re < freeHillValue N-12*(N:ℝ)
      · have hm : z.re ∈ sourceRealCentralRoots r hr q N :=
          (mem_sourceRealCentralRoots_iff r hr q N z.re).mpr
            ((mem_sourceCentralSpectrum r hr q.val N _).mpr ⟨he.symm ▸ hz,hb⟩)
        rw [← hξ] at hm
        simp only [Multiset.mem_sum,Multiset.mem_singleton] at hm
        obtain ⟨j,hj,hjz⟩ := hm
        refine ⟨j,?_⟩
        rw [show ell j = ξ j from NLS.appendPairedTail_prefix _ _ _ _ _ (Finset.mem_range.mp hj)]
        rw [← hjz,he]
      · obtain ⟨n,hn,hstrip,_⟩ := sourceHillSpectrum_real_high_cover r hr q N hN hs z hz (le_of_not_gt hb)
        have hnk : N+(n-N) = n := by omega
        have hp := (SourceHillRealPair.spectrum_iff r hr q (N+(n-N)) (P (n-N)) z
          (by rwa [hnk])).mp hz
        rcases hp with hp | hp
        · refine ⟨(2*N-1)+2*(n-N),?_⟩
          have hj : ell ((2*N-1)+2*(n-N)) = (P (n-N)).left :=
            NLS.appendPairedTail_even _ _ _ _ (n-N)
          exact hp.trans (congrArg Complex.ofReal hj).symm
        · refine ⟨(2*N-1)+2*(n-N)+1,?_⟩
          have hj : ell ((2*N-1)+2*(n-N)+1) = (P (n-N)).right :=
            NLS.appendPairedTail_odd _ _ _ _ (n-N)
          exact hp.trans (congrArg Complex.ofReal hj).symm
    · rintro ⟨j,rfl⟩
      exact hspec j
  · intro n hn
    obtain ⟨k,hk⟩ : ∃ k : ℕ, n = N+k := ⟨n-N,by omega⟩
    subst n
    refine ⟨P k,?_,?_⟩
    · have hj : 2*(N+k)-1 = (2*N-1)+2*k := by omega
      change NLS.appendPairedTail _ _ _ _ _ = _
      rw [hj,NLS.appendPairedTail_even]
    · have hj : 2*(N+k) = (2*N-1)+2*k+1 := by omega
      change NLS.appendPairedTail _ _ _ _ _ = _
      rw [hj,NLS.appendPairedTail_odd]
  · intro x
    rw [← hcount x]
    apply Finset.sum_congr rfl
    intro j hj
    rw [show ell j = ξ j from NLS.appendPairedTail_prefix _ _ _ _ _ (Finset.mem_range.mp hj)]
  · intro j hj
    rw [show ell j = ξ j from NLS.appendPairedTail_prefix _ _ _ _ _ hj]
    exact ((mem_sourceCentralSpectrum r hr q.val N _).mp (hcentral j hj)).2

/-- A global physical labeling records actual spectrum and multiplicities; no list is supplied by the caller. -/
structure SourceHillRealLabeling (r : ℝ) (hr : AdmissiblePredualOrder r) (q : Potential r)
    (N : ℕ) (ell : ℕ → ℝ) : Prop where
  cutoff_ge_two : 2 ≤ N
  cutoff_small : ∀ n : ℕ, N ≤ n → 13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q.val‖ ≤ 1/2
  monotone : Monotone ell
  spectrum : ∀ z : ℂ, z ∈ sourceHillSpectrum r hr q.val ↔ ∃ j : ℕ, z = (ell j:ℂ)
  high_pair : ∀ n : ℕ, N ≤ n → ∃ p : SourceHillRealPair r hr q n,
    ell (2*n-1) = p.left ∧ ell (2*n) = p.right
  central_counts : ∀ x : ℝ, (∑ j ∈ Finset.range (2*N-1), if ell j = x then 1 else 0) =
    if (x:ℂ) ∈ sourceCentralSpectrum r hr q.val N then sourceHillAlgebraicMultiplicity r hr q.val x else 0
  central_below : ∀ j < 2*N-1, ell j < freeHillValue N-12*(N:ℝ)

theorem exists_sourceHillRealLabeling (r : ℝ) (hr : AdmissiblePredualOrder r) (q : Potential r)
    (N : ℕ) (hN : 2 ≤ N)
    (hs : ∀ n : ℕ, N ≤ n → 13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q.val‖ ≤ 1/2) :
    ∃ ell : ℕ → ℝ, SourceHillRealLabeling r hr q N ell := by
  obtain ⟨ell,hm,hsp,hp,hc,hb⟩ := exists_sourceHillRealLabels r hr q N hN hs
  exact ⟨ell,⟨hN,hs,hm,hsp,hp,hc,hb⟩⟩

end NLS.Articles.KdVPseudomeasures
