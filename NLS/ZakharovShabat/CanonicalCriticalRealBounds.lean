import NLS.ZakharovShabat.CriticalRealBarriers
import NLS.SequenceSpaces.OrderedCountBounds

/-!
# Canonical real-part bounds from stable counts

A zero-free real-diameter circle preserves the size of a prefix or suffix
of the real critical sequence. Ordered counting bounds then control the
same canonical coordinate for nearby complex even potentials.
-/

noncomputable section
open Set Complex Filter Topology Metric
open NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A zero-free left barrier gives a nearby upper bound on a canonical real part. -/
theorem eventually_canonicalCriticalPoints_re_le_of_barrier (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : pairParitySubspace (p := p) 0) (hreal : IsRealType φ.val) (K : ℕ)
    (hK : ∀ᶠ ψ : pairParitySubspace (p := p) 0 in 𝓝 φ,
      CriticalPointLabeling hp hp1 ψ.val ψ.property K (canonicalCriticalPoints hp hp1 ψ.val ψ.property))
    (n : ℤ) (hn : n.natAbs ≤ K) (a : ℝ)
    (ha : -centralCircleRadius K < a) (haR : a ≤ centralCircleRadius K)
    (hxa : (canonicalCriticalPoints hp hp1 φ.val φ.property n).re ≤ a)
    (hne : ∀ z ∈ sphere (((-centralCircleRadius K+a)/2 : ℝ) : ℂ)
      ((a+centralCircleRadius K)/2), deriv (canonicalDiscriminant hp φ.val) z ≠ 0) :
    ∀ᶠ ψ : pairParitySubspace (p := p) 0 in 𝓝 φ,
      (canonicalCriticalPoints hp hp1 ψ.val ψ.property n).re ≤ a := by
  let R := centralCircleRadius K
  let D := closedBall (((-R+a)/2 : ℝ) : ℂ) ((a+R)/2)
  let s := Finset.Icc (-(K : ℤ)) K
  let ξ := fun ψ : pairParitySubspace (p := p) 0 => canonicalCriticalPoints hp hp1 ψ.val ψ.property
  have hφ := hK.self_of_nhds
  have hsub : D ⊆ closedBall 0 R := by
    simpa only [sub_neg_eq_add] using realDiameterDisc_subset_closedBall (-R) a R le_rfl haR
  have hpref : s.filter (fun j => j ≤ n) ⊆ s.filter (fun j => ξ φ j ∈ D) := by
    intro j hj
    obtain ⟨hjs,hjn⟩ := Finset.mem_filter.mp hj
    have hjK : j.natAbs ≤ K := by dsimp [s] at hjs; simp only [Finset.mem_Icc] at hjs; omega
    refine Finset.mem_filter.mpr ⟨hjs,?_⟩
    have hr := (abs_le.mp (hφ.abs_re_central_le j hjK)).1
    have hm := re_le_of_complexLexLE ((monotone_canonicalCriticalPoints hp hp1 φ.val φ.property) hjn)
    have him := canonicalCriticalPoints_im_eq_zero hp hp1 φ.val φ.property hreal j
    apply (show ξ φ j ∈ D ↔ -R ≤ (ξ φ j).re ∧ (ξ φ j).re ≤ a from by
      simpa only [sub_neg_eq_add] using mem_realDiameterDisc_iff (-R) a (ξ φ j) him).mpr
    exact ⟨hr,hm.trans hxa⟩
  have he := eventually_discriminant_critical_count_eq hp hp1 φ
    (((-R+a)/2 : ℝ) : ℂ) ((a+R)/2) (by dsimp [R]; linarith) hne
  filter_upwards [hK,he] with ψ hψ hc
  have heq : (s.filter (fun j => ξ ψ j ∈ D)).card = (s.filter (fun j => ξ φ j ∈ D)).card := by
    rw [hψ.analyticZeroCount_eq_card_filter D hsub, hφ.analyticZeroCount_eq_card_filter D hsub] at hc
    exact hc
  apply NLS.le_of_prefix_card_le s (s.filter (fun j => ξ ψ j ∈ D)) (fun j => (ξ ψ j).re)
    (fun _ _ _ _ hij => re_le_of_complexLexLE ((monotone_canonicalCriticalPoints hp hp1 ψ.val ψ.property) hij))
    n (by dsimp [s]; simp only [Finset.mem_Icc]; omega) a (Finset.filter_subset _ _) ?_ ?_
  · intro j hj
    have hd := (Finset.mem_filter.mp hj).2
    exact (re_mem_Icc_of_mem_realDiameterDisc (-R) a (ξ ψ j) (by simpa only [sub_neg_eq_add] using hd)).2
  · rw [heq]
    exact Finset.card_le_card hpref

/-- A zero-free right barrier gives a nearby lower bound on a canonical real part. -/
theorem eventually_le_canonicalCriticalPoints_re_of_barrier (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : pairParitySubspace (p := p) 0) (hreal : IsRealType φ.val) (K : ℕ)
    (hK : ∀ᶠ ψ : pairParitySubspace (p := p) 0 in 𝓝 φ,
      CriticalPointLabeling hp hp1 ψ.val ψ.property K (canonicalCriticalPoints hp hp1 ψ.val ψ.property))
    (n : ℤ) (hn : n.natAbs ≤ K) (a : ℝ)
    (ha : -centralCircleRadius K ≤ a) (haR : a < centralCircleRadius K)
    (hax : a ≤ (canonicalCriticalPoints hp hp1 φ.val φ.property n).re)
    (hne : ∀ z ∈ sphere (((a+centralCircleRadius K)/2 : ℝ) : ℂ)
      ((centralCircleRadius K-a)/2), deriv (canonicalDiscriminant hp φ.val) z ≠ 0) :
    ∀ᶠ ψ : pairParitySubspace (p := p) 0 in 𝓝 φ,
      a ≤ (canonicalCriticalPoints hp hp1 ψ.val ψ.property n).re := by
  let R := centralCircleRadius K
  let D := closedBall (((a+R)/2 : ℝ) : ℂ) ((R-a)/2)
  let s := Finset.Icc (-(K : ℤ)) K
  let ξ := fun ψ : pairParitySubspace (p := p) 0 => canonicalCriticalPoints hp hp1 ψ.val ψ.property
  have hφ := hK.self_of_nhds
  have hsub : D ⊆ closedBall 0 R := realDiameterDisc_subset_closedBall a R R ha le_rfl
  have hsuff : s.filter (fun j => n ≤ j) ⊆ s.filter (fun j => ξ φ j ∈ D) := by
    intro j hj
    obtain ⟨hjs,hnj⟩ := Finset.mem_filter.mp hj
    have hjK : j.natAbs ≤ K := by dsimp [s] at hjs; simp only [Finset.mem_Icc] at hjs; omega
    refine Finset.mem_filter.mpr ⟨hjs,?_⟩
    have hr := (abs_le.mp (hφ.abs_re_central_le j hjK)).2
    have hm := re_le_of_complexLexLE ((monotone_canonicalCriticalPoints hp hp1 φ.val φ.property) hnj)
    have him := canonicalCriticalPoints_im_eq_zero hp hp1 φ.val φ.property hreal j
    exact (mem_realDiameterDisc_iff a R (ξ φ j) him).mpr ⟨hax.trans hm,hr⟩
  have he := eventually_discriminant_critical_count_eq hp hp1 φ
    (((a+R)/2 : ℝ) : ℂ) ((R-a)/2) (by dsimp [R]; linarith) hne
  filter_upwards [hK,he] with ψ hψ hc
  have heq : (s.filter (fun j => ξ ψ j ∈ D)).card = (s.filter (fun j => ξ φ j ∈ D)).card := by
    rw [hψ.analyticZeroCount_eq_card_filter D hsub, hφ.analyticZeroCount_eq_card_filter D hsub] at hc
    exact hc
  apply NLS.le_of_suffix_card_le s (s.filter (fun j => ξ ψ j ∈ D)) (fun j => (ξ ψ j).re)
    (fun _ _ _ _ hij => re_le_of_complexLexLE ((monotone_canonicalCriticalPoints hp hp1 ψ.val ψ.property) hij))
    n (by dsimp [s]; simp only [Finset.mem_Icc]; omega) a (Finset.filter_subset _ _) ?_ ?_
  · intro j hj
    exact (re_mem_Icc_of_mem_realDiameterDisc a R (ξ ψ j) (Finset.mem_filter.mp hj).2).1
  · rw [heq]
    exact Finset.card_le_card hsuff

end NLS.ZakharovShabat
