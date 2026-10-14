import NLS.ZakharovShabat.UniformCanonicalCriticalPoints
import NLS.ZakharovShabat.FiniteSourceRealization

/-!
# Lemma 8.3 in the original source space

One original open convex neighborhood and one cutoff control all critical
roots of the actual discriminant, for every finite p > 1. Distant roots are
unique and simple; central roots retain their analytic multiplicities.
The same assertions hold at every larger cutoff, and real-type sources
have only real critical roots. The central circle used in the source proof
and the earlier central box select the same roots after enlarging the cutoff.
-/

noncomputable section
open Set Complex Metric NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Locally uniform critical-root counts, canonical labels, exhaustion, and reality. -/
structure SourceLemma8_3Data (hp : p ≠ ⊤) (hp1 : 1 < p)
    (U : Set (CoeffPair p)) (N : ℕ) : Prop where
  distant : ∀ ψ ∈ U, ∀ n : ℤ, N < n.natAbs →
    let ξ := canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n
    ξ ∈ ball ((Real.pi : ℂ)*n) (Real.pi/4) ∧
    deriv (canonicalDiscriminant hp (periodOnePotential ψ)) ξ = 0 ∧
    analyticOrderAt (deriv (canonicalDiscriminant hp (periodOnePotential ψ))) ξ = 1 ∧
    ∀ z ∈ closedBall ((Real.pi : ℂ)*n) (Real.pi/4),
      deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z = 0 ↔ z = ξ
  distant_counts : ∀ ψ ∈ U, ∀ n : ℤ, N < n.natAbs →
    analyticZeroCount (deriv (canonicalDiscriminant hp (periodOnePotential ψ)))
      (closedBall ((Real.pi : ℂ)*n) (Real.pi/4)) = 1 ∧
    ∀ z ∈ sphere ((Real.pi : ℂ)*n) (Real.pi/4), deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z ≠ 0
  central_counts : ∀ ψ ∈ U, ∀ K : ℕ, N ≤ K →
    analyticZeroCount (deriv (canonicalDiscriminant hp (periodOnePotential ψ)))
      (closedBall 0 (centralCircleRadius K)) = 2*K+1 ∧
    ∀ z ∈ sphere 0 (centralCircleRadius K), deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z ≠ 0
  central_labels : ∀ ψ ∈ U, ∀ K : ℕ, N ≤ K →
    (∑ n ∈ Finset.Icc (-(K : ℤ)) K,
      ({canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n} : Multiset ℂ)) =
      centralCriticalRoots hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) K
  exhaustive : ∀ ψ ∈ U, ∀ K : ℕ, N ≤ K → ∀ z : ℂ,
    deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z = 0 →
      z ∈ ball 0 (centralCircleRadius K) ∨
      ∃ n : ℤ, K < n.natAbs ∧ z ∈ ball ((Real.pi : ℂ)*n) (Real.pi/4)
  imag_bound : ∀ ψ ∈ U, ∀ z : ℂ,
    deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z = 0 → |z.im| < (N : ℝ)
  real_roots : ∀ ψ ∈ U, IsRealType (CoeffPair.toMax p ψ) → ∀ z : ℂ,
    deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z = 0 → z.im = 0

/-- Lemma 8.3, with one original neighborhood valid for every larger central cutoff. -/
theorem sourceLemma8_3 (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    ∃ N : ℕ, 0 < N ∧ ∃ U : Set (CoeffPair p), IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      SourceLemma8_3Data hp hp1 U N := by
  obtain ⟨Nc,hNc,C,hCo,hCc,hCφ,hC0,hc⟩ := exists_uniform_discriminant_critical_counts hp hp1
    (periodOnePotential φ) (by positivity : 0 < Real.pi/4) le_rfl
  obtain ⟨Nl,_,L,hLo,hLc,hLφ,hL0,R,_,hl⟩ := exists_uniform_canonicalCriticalPoints_all_cutoffs hp hp1 (periodOnePotential φ)
  obtain ⟨Nr,hNr⟩ := exists_nat_gt R
  let N := max Nc (max Nl Nr)
  have hNcN : Nc ≤ N := le_max_left _ _
  have hNlN : Nl ≤ N := (le_max_left _ _).trans (le_max_right _ _)
  have hNrN : Nr ≤ N := (le_max_right _ _).trans (le_max_right _ _)
  let U : Set (CoeffPair p) := periodOnePotential ⁻¹' (C ∩ L)
  have hN : 0 < N := hNc.trans_le hNcN
  refine ⟨N,hN,U,(hCo.inter hLo).preimage (periodOnePotential (p := p)).continuous,
    (hCc.inter hLc).linear_preimage ((periodOnePotential (p := p)).restrictScalars ℝ).toLinearMap,
    ⟨hCφ,hLφ⟩,?_,?_⟩
  · simpa only [U,mem_preimage,map_zero,mem_inter_iff] using (show (0 : PairSpace p) ∈ C ∧ 0 ∈ L from ⟨hC0,hL0⟩)
  · exact {
      distant := fun ψ hψ n hn =>
        ((hl _ hψ.2 (periodOnePotential_mem ψ)).2 N hNlN).distant n hn
      distant_counts := fun ψ hψ n hn => (hc _ hψ.1 (periodOnePotential_mem ψ)).1 n
        (hNcN.trans hn.le)
      central_counts := fun ψ hψ K hK => (hc _ hψ.1 (periodOnePotential_mem ψ)).2.1 K
        (hNcN.trans hK)
      central_labels := fun ψ hψ K hK =>
        ((hl _ hψ.2 (periodOnePotential_mem ψ)).2 K (hNlN.trans hK)).central
      exhaustive := fun ψ hψ K hK => (hc _ hψ.1 (periodOnePotential_mem ψ)).2.2 K
        (hNcN.trans hK)
      imag_bound := by
        intro ψ hψ z hz
        obtain ⟨n,rfl⟩ := (canonicalCriticalPoints_exhaustive hp hp1 _ (periodOnePotential_mem ψ) z).mp hz
        have him : (canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n).im =
            (canonicalCriticalDisplacement hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n).im := by
          simp [canonicalCriticalDisplacement_apply]
        rw [him]
        exact (Complex.abs_im_le_norm _).trans_lt
          ((lp.norm_apply_le_norm ((zero_lt_one.trans hp1).ne') _ n).trans_lt
            (((hl _ hψ.2 (periodOnePotential_mem ψ)).1).trans_lt
              (hNr.trans_le (by exact_mod_cast hNrN))))
      real_roots := fun ψ _ hψ _ hz => discriminant_critical_im_eq_zero_of_realType hp hp1 _
        (periodOnePotential_mem ψ) (isRealType_periodOnePotential ψ hψ) hz }


/-- The central multiset has the asserted size and contains exactly the roots in the open disc. -/
theorem SourceLemma8_3Data.central_roots {hp : p ≠ ⊤} {hp1 : 1 < p}
    {U : Set (CoeffPair p)} {N : ℕ} (D : SourceLemma8_3Data hp hp1 U N)
    (ψ : CoeffPair p) (hψ : ψ ∈ U) (K : ℕ) (hK : N ≤ K) :
    (centralCriticalRoots hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) K).card = 2*K+1 ∧
    ∀ z : ℂ, z ∈ centralCriticalRoots hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) K ↔
      z ∈ ball 0 (centralCircleRadius K) ∧ deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z = 0 := by
  refine ⟨(card_centralCriticalRoots hp hp1 _ (periodOnePotential_mem ψ) K).trans (D.central_counts ψ hψ K hK).1,?_⟩
  intro z
  rw [mem_centralCriticalRoots]
  constructor
  · rintro ⟨hz,hroot⟩
    refine ⟨?_,hroot⟩
    rw [mem_ball]
    rcases lt_or_eq_of_le (mem_closedBall.mp hz) with hlt | he
    · exact hlt
    · exact ((D.central_counts ψ hψ K hK).2 z (mem_sphere.mpr he) hroot).elim
  · rintro ⟨hz,hroot⟩
    exact ⟨ball_subset_closedBall hz,hroot⟩

/-- Each central canonical label is counted with the actual analytic multiplicity. -/
theorem SourceLemma8_3Data.central_multiplicity {hp : p ≠ ⊤} {hp1 : 1 < p}
    {U : Set (CoeffPair p)} {N : ℕ} (D : SourceLemma8_3Data hp hp1 U N)
    (ψ : CoeffPair p) (hψ : ψ ∈ U) (K : ℕ) (hK : N ≤ K) (z : ℂ) :
    (∑ n ∈ Finset.Icc (-(K : ℤ)) K,
      ({canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n} : Multiset ℂ)).count z =
      if z ∈ ball 0 (centralCircleRadius K) then
        analyticOrderNatAt (deriv (canonicalDiscriminant hp (periodOnePotential ψ))) z else 0 := by
  rw [D.central_labels ψ hψ K hK]
  by_cases hz : z ∈ ball 0 (centralCircleRadius K)
  · rw [count_centralCriticalRoots,if_pos (ball_subset_closedBall hz),if_pos hz]
  · rw [if_neg hz]
    exact Multiset.count_eq_zero.mpr (fun hm => hz (((D.central_roots ψ hψ K hK).2 z).mp hm).1)

/-- The central disc and the earlier height-K box select exactly the same critical roots. -/
theorem SourceLemma8_3Data.central_box_selection {hp : p ≠ ⊤} {hp1 : 1 < p}
    {U : Set (CoeffPair p)} {N : ℕ} (D : SourceLemma8_3Data hp hp1 U N)
    (hN : 0 < N) (ψ : CoeffPair p) (hψ : ψ ∈ U) (K : ℕ) (hK : N ≤ K)
    {z : ℂ} (hz : deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z = 0) :
    z ∈ ball 0 (centralCircleRadius K) ↔ z ∈ centralSpectralBox K := by
  constructor
  · intro hb
    exact ⟨(Complex.abs_re_le_norm z).trans_lt (by simpa [centralCircleRadius] using hb),
      (D.imag_bound ψ hψ z hz).le.trans (by exact_mod_cast hK)⟩
  · intro hb
    rcases D.exhaustive ψ hψ K hK z hz with hc | ⟨n,hn,hd⟩
    · exact hc
    · have hrK : Real.pi/4 ≤ (K : ℝ) := by
        have h1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast (hN.trans_le hK)
        linarith [Real.pi_le_four]
      exact (hn.not_ge ((smallDisk_central_selection K n le_rfl hrK hd).2.mp hb)).elim

/-- The earlier central box has the same exact count, retaining all analytic multiplicities. -/
theorem SourceLemma8_3Data.central_box_count {hp : p ≠ ⊤} {hp1 : 1 < p}
    {U : Set (CoeffPair p)} {N : ℕ} (D : SourceLemma8_3Data hp hp1 U N)
    (hN : 0 < N) (ψ : CoeffPair p) (hψ : ψ ∈ U) (K : ℕ) (hK : N ≤ K) :
    analyticZeroCount (deriv (canonicalDiscriminant hp (periodOnePotential ψ))) (centralSpectralBox K) = 2*K+1 := by
  rw [← (D.central_counts ψ hψ K hK).1]
  unfold analyticZeroCount
  apply finsum_congr
  intro z
  by_cases hz : deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z = 0
  · have hs : z ∈ closedBall 0 (centralCircleRadius K) ↔ z ∈ centralSpectralBox K := by
      rw [← D.central_box_selection hN ψ hψ K hK hz]
      constructor
      · intro hc
        exact ((D.central_roots ψ hψ K hK).2 z).mp
          ((mem_centralCriticalRoots hp hp1 _ (periodOnePotential_mem ψ) K z).mpr ⟨hc,hz⟩) |>.1
      · intro hb
        exact ball_subset_closedBall hb
    rw [hs]
  · have ho : analyticOrderNatAt (deriv (canonicalDiscriminant hp (periodOnePotential ψ))) z = 0 :=
      not_ne_iff.mp (fun hn => hz (apply_eq_zero_of_analyticOrderNatAt_ne_zero hn))
    simp only [ho,ite_self]

end NLS.ZakharovShabat
