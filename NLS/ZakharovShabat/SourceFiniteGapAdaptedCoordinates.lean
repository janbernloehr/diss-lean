import NLS.ZakharovShabat.SourceClosedGapCenter
import NLS.ZakharovShabat.SourceFiniteGapClosingCriterion
import NLS.ZakharovShabat.SourceAdaptedClosingMapDerivative
import NLS.SequenceSpaces.Truncation

/-! # Finite-gap sources have finite adapted spectral coordinates

The original source need not have finite Fourier support. The actual
adapted closing map, however, is exactly its low Fourier truncation
at every sufficiently large cutoff. This is the spectral input to
recovering regularity through the adapted inverse.
-/

noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Finite spectral support is equivalent to eventual vanishing of
both actual off-diagonal equations at the moving diagonal centers. -/
theorem sourceFiniteGapLocus_iff_eventually_center_closed
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceLocus p) :
    φ ∈ sourceFiniteGapLocus hp hp1 ↔
      ∃ N : ℕ, ∀ n : ℤ, N ≤ n.natAbs →
        let ζ := weightedResonantDiagonalCenter hp SpectralWeight.one (sourceWeightedPeriodOne φ.val) n
        weightedResonantBPlusExtension hp SpectralWeight.one (sourceWeightedPeriodOne φ.val) n ζ = 0 ∧
        weightedResonantBMinusExtension hp SpectralWeight.one (sourceWeightedPeriodOne φ.val) n ζ = 0 := by
  classical
  constructor
  · intro hfinite
    obtain ⟨N,hN,hclose⟩ := exists_sourceClosedGap_center_equations hp hp1 φ.val φ.property
    let S := hfinite.toFinset
    refine ⟨max N (S.sup Int.natAbs+1),?_⟩
    intro n hn
    have hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n = 0 := by
      by_contra hne
      have hmem : n ∈ S := hfinite.mem_toFinset.mpr hne
      have hle := Finset.le_sup (f := Int.natAbs) hmem
      omega
    exact (hclose n (by omega) hgap).2
  · rintro ⟨N,hclosed⟩
    obtain ⟨M,_,U,_,hφ,hclosing⟩ := exists_uniform_sourceResonantCenterClosing hp hp1 φ.val
    apply mem_sourceFiniteGapLocus_of_singleton_strips hp hp1 φ (max N M)
      (fun n => weightedResonantDiagonalCenter hp SpectralWeight.one (sourceWeightedPeriodOne φ.val) n)
    intro n hn
    exact (hclosing φ.val hφ n (by omega) (hclosed n (by omega)).1 (hclosed n (by omega)).2).1

/-- A common closed-gap tail gives finite adapted coordinates throughout
one open source neighborhood, at every sufficiently large cutoff. -/
theorem exists_uniform_sourceAdaptedClosingMap_eq_truncate
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ₀ : CoeffPair p) :
    ∃ N : ℕ, 2 ≤ N ∧ ∃ U : Set (CoeffPair p), IsOpen U ∧ φ₀ ∈ U ∧
      ∀ φ ∈ U, IsRealType (CoeffPair.toMax p φ) → ∀ M : ℕ, N ≤ M →
        (∀ n : ℤ, M ≤ n.natAbs →
          canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n = 0) →
        sourceAdaptedClosingMap hp φ M = (CoeffPair.toMax p).symm
          (Coeff.truncate (Finset.Ioo (-(M : ℤ)) M) φ.fst,
           Coeff.truncate (Finset.Ioo (-(M : ℤ)) M) φ.snd) := by
  obtain ⟨N,hN,U,ho,hφ,hclose⟩ := exists_uniform_sourceClosedGap_center_equations hp hp1 φ₀
  obtain ⟨r,hr,K,hK,hdata⟩ := exists_fixedBall_sourceAdaptedClosingMap_derivative hp hp1 φ₀ 1 (by norm_num)
  refine ⟨max N K,by omega,U ∩ ball φ₀ (4*r),ho.inter isOpen_ball,
    ⟨hφ,mem_ball_self (by positivity)⟩,?_⟩
  intro φ hφ hreal M hM hgap
  have hmem := ((hdata M (by omega)).2.1 φ hφ.2).1
  have hclosed (n : ℤ) (hn : M ≤ n.natAbs) :=
    (hclose φ hφ.1 hreal n (by omega) (hgap n hn)).2
  have hcoord := sourceAdaptedClosingMap_apply_of_mem hp φ M hmem
  apply (CoeffPair.toMax p).injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  apply Prod.ext <;> ext n
  · change (sourceAdaptedClosingMap hp φ M).fst n = _
    rw [(hcoord n).1]
    by_cases hn : M ≤ n.natAbs
    · rw [if_pos hn, (hclosed (-n) (by simpa only [Int.natAbs_neg] using hn)).2]
      simp only [Coeff.truncate_apply]
      rw [if_neg (by simp only [Finset.mem_Ioo]; omega)]
    · rw [if_neg hn]
      simp only [Coeff.truncate_apply]
      rw [if_pos (by simp only [Finset.mem_Ioo]; omega)]
  · change (sourceAdaptedClosingMap hp φ M).snd n = _
    rw [(hcoord n).2]
    by_cases hn : M ≤ n.natAbs
    · rw [if_pos hn, (hclosed n hn).1]
      simp only [Coeff.truncate_apply]
      rw [if_neg (by simp only [Finset.mem_Ioo]; omega)]
    · rw [if_neg hn]
      simp only [Coeff.truncate_apply]
      rw [if_pos (by simp only [Finset.mem_Ioo]; omega)]

/-- At every sufficiently large cutoff the entire adapted map equals
the finite low-frequency truncation of the original source. -/
theorem sourceAdaptedClosingMap_eq_truncate_of_finiteGap
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceLocus p)
    (hfinite : φ ∈ sourceFiniteGapLocus hp hp1) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ M : ℕ, N ≤ M →
      sourceAdaptedClosingMap hp φ.val M = (CoeffPair.toMax p).symm
        (Coeff.truncate (Finset.Ioo (-(M : ℤ)) M) φ.val.fst,
         Coeff.truncate (Finset.Ioo (-(M : ℤ)) M) φ.val.snd) := by
  classical
  obtain ⟨N,hN,U,_,hφ,h⟩ := exists_uniform_sourceAdaptedClosingMap_eq_truncate hp hp1 φ.val
  let S := hfinite.toFinset
  refine ⟨max N (S.sup Int.natAbs+1),by omega,?_⟩
  intro M hM
  apply h φ.val hφ φ.property M (by omega)
  intro n hn
  by_contra hne
  have hmem : n ∈ S := hfinite.mem_toFinset.mpr hne
  have hle := Finset.le_sup (f := Int.natAbs) hmem
  omega

end NLS.ZakharovShabat
