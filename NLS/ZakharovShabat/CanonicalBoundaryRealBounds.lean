import NLS.ZakharovShabat.BoundaryRootCounts
import NLS.ZakharovShabat.CanonicalBoundaryStability
import NLS.SequenceSpaces.OrderedCountBounds

/-!
# Canonical real-part bounds from stable counts

A zero-free real-diameter circle preserves the size of a prefix or suffix
of the real boundary sequence. Ordered counting bounds then control the
same canonical coordinate for nearby complex reflected potentials.
-/

noncomputable section
open Set Complex Filter Topology Metric
open NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A zero-free left barrier gives a nearby upper bound on a canonical real part. -/
theorem eventually_canonicalBoundaryRoots_re_le_of_barrier (hp : p ≠ ⊤) (hp1 : 1 < p)
    (b : BoundaryCondition) (φ : dirichletSubspace (p := p)) (hreal : IsRealType φ.val) (K : ℕ)
    (hK : ∀ᶠ ψ : dirichletSubspace (p := p) in 𝓝 φ,
      BoundaryRootLabeling b hp ψ.val ψ.property K (b.canonicalRoots hp hp1 ψ.val ψ.property))
    (n : ℤ) (hn : n.natAbs ≤ K) (a : ℝ)
    (ha : -centralCircleRadius K < a) (haR : a ≤ centralCircleRadius K)
    (hxa : (b.canonicalRoots hp hp1 φ.val φ.property n).re ≤ a)
    (hne : ∀ z ∈ sphere (((-centralCircleRadius K+a)/2 : ℝ) : ℂ)
      ((a+centralCircleRadius K)/2), b.characteristic hp φ.val φ.property z ≠ 0) :
    ∀ᶠ ψ : dirichletSubspace (p := p) in 𝓝 φ,
      (b.canonicalRoots hp hp1 ψ.val ψ.property n).re ≤ a := by
  let R := centralCircleRadius K
  let D := closedBall (((-R+a)/2 : ℝ) : ℂ) ((a+R)/2)
  let s := Finset.Icc (-(K : ℤ)) K
  let ξ := fun ψ : dirichletSubspace (p := p) => b.canonicalRoots hp hp1 ψ.val ψ.property
  have hφ := hK.self_of_nhds
  have hsub : ∀ z ∈ D, |z.re| ≤ R := by
    intro z hz
    have hr := re_mem_Icc_of_mem_realDiameterDisc (-R) a z (by simpa only [sub_neg_eq_add] using hz)
    exact abs_le.mpr ⟨hr.1,hr.2.trans haR⟩
  have hpref : s.filter (fun j => j ≤ n) ⊆ s.filter (fun j => ξ φ j ∈ D) := by
    intro j hj
    obtain ⟨hjs,hjn⟩ := Finset.mem_filter.mp hj
    have hjK : j.natAbs ≤ K := by dsimp [s] at hjs; simp only [Finset.mem_Icc] at hjs; omega
    refine Finset.mem_filter.mpr ⟨hjs,?_⟩
    have hr := (abs_le.mp (hφ.abs_re_central_le j hjK)).1
    have hm := re_le_of_complexLexLE ((b.monotone_canonicalRoots hp hp1 φ.val φ.property) hjn)
    have him := b.canonicalRoots_im_eq_zero hp hp1 φ.val φ.property hreal j
    apply (show ξ φ j ∈ D ↔ -R ≤ (ξ φ j).re ∧ (ξ φ j).re ≤ a from by
      simpa only [sub_neg_eq_add] using mem_realDiameterDisc_iff (-R) a (ξ φ j) him).mpr
    exact ⟨hr,hm.trans hxa⟩
  have he := eventually_boundaryCharacteristic_count_eq hp hp1 b φ
    (((-R+a)/2 : ℝ) : ℂ) ((a+R)/2) (by dsimp [R]; linarith) hne
  filter_upwards [hK,he] with ψ hψ hc
  have heq : (s.filter (fun j => ξ ψ j ∈ D)).card = (s.filter (fun j => ξ φ j ∈ D)).card := by
    rw [hψ.analyticZeroCount_eq_card_filter hp1 D hsub, hφ.analyticZeroCount_eq_card_filter hp1 D hsub] at hc
    exact hc
  apply NLS.le_of_prefix_card_le s (s.filter (fun j => ξ ψ j ∈ D)) (fun j => (ξ ψ j).re)
    (fun _ _ _ _ hij => re_le_of_complexLexLE ((b.monotone_canonicalRoots hp hp1 ψ.val ψ.property) hij))
    n (by dsimp [s]; simp only [Finset.mem_Icc]; omega) a (Finset.filter_subset _ _) ?_ ?_
  · intro j hj
    have hd := (Finset.mem_filter.mp hj).2
    exact (re_mem_Icc_of_mem_realDiameterDisc (-R) a (ξ ψ j) (by simpa only [sub_neg_eq_add] using hd)).2
  · rw [heq]
    exact Finset.card_le_card hpref

/-- A zero-free right barrier gives a nearby lower bound on a canonical real part. -/
theorem eventually_le_canonicalBoundaryRoots_re_of_barrier (hp : p ≠ ⊤) (hp1 : 1 < p)
    (b : BoundaryCondition) (φ : dirichletSubspace (p := p)) (hreal : IsRealType φ.val) (K : ℕ)
    (hK : ∀ᶠ ψ : dirichletSubspace (p := p) in 𝓝 φ,
      BoundaryRootLabeling b hp ψ.val ψ.property K (b.canonicalRoots hp hp1 ψ.val ψ.property))
    (n : ℤ) (hn : n.natAbs ≤ K) (a : ℝ)
    (ha : -centralCircleRadius K ≤ a) (haR : a < centralCircleRadius K)
    (hax : a ≤ (b.canonicalRoots hp hp1 φ.val φ.property n).re)
    (hne : ∀ z ∈ sphere (((a+centralCircleRadius K)/2 : ℝ) : ℂ)
      ((centralCircleRadius K-a)/2), b.characteristic hp φ.val φ.property z ≠ 0) :
    ∀ᶠ ψ : dirichletSubspace (p := p) in 𝓝 φ,
      a ≤ (b.canonicalRoots hp hp1 ψ.val ψ.property n).re := by
  let R := centralCircleRadius K
  let D := closedBall (((a+R)/2 : ℝ) : ℂ) ((R-a)/2)
  let s := Finset.Icc (-(K : ℤ)) K
  let ξ := fun ψ : dirichletSubspace (p := p) => b.canonicalRoots hp hp1 ψ.val ψ.property
  have hφ := hK.self_of_nhds
  have hsub : ∀ z ∈ D, |z.re| ≤ R := by
    intro z hz
    have hr := re_mem_Icc_of_mem_realDiameterDisc a R z hz
    exact abs_le.mpr ⟨ha.trans hr.1,hr.2⟩
  have hsuff : s.filter (fun j => n ≤ j) ⊆ s.filter (fun j => ξ φ j ∈ D) := by
    intro j hj
    obtain ⟨hjs,hnj⟩ := Finset.mem_filter.mp hj
    have hjK : j.natAbs ≤ K := by dsimp [s] at hjs; simp only [Finset.mem_Icc] at hjs; omega
    refine Finset.mem_filter.mpr ⟨hjs,?_⟩
    have hr := (abs_le.mp (hφ.abs_re_central_le j hjK)).2
    have hm := re_le_of_complexLexLE ((b.monotone_canonicalRoots hp hp1 φ.val φ.property) hnj)
    have him := b.canonicalRoots_im_eq_zero hp hp1 φ.val φ.property hreal j
    exact (mem_realDiameterDisc_iff a R (ξ φ j) him).mpr ⟨hax.trans hm,hr⟩
  have he := eventually_boundaryCharacteristic_count_eq hp hp1 b φ
    (((a+R)/2 : ℝ) : ℂ) ((R-a)/2) (by dsimp [R]; linarith) hne
  filter_upwards [hK,he] with ψ hψ hc
  have heq : (s.filter (fun j => ξ ψ j ∈ D)).card = (s.filter (fun j => ξ φ j ∈ D)).card := by
    rw [hψ.analyticZeroCount_eq_card_filter hp1 D hsub, hφ.analyticZeroCount_eq_card_filter hp1 D hsub] at hc
    exact hc
  apply NLS.le_of_suffix_card_le s (s.filter (fun j => ξ ψ j ∈ D)) (fun j => (ξ ψ j).re)
    (fun _ _ _ _ hij => re_le_of_complexLexLE ((b.monotone_canonicalRoots hp hp1 ψ.val ψ.property) hij))
    n (by dsimp [s]; simp only [Finset.mem_Icc]; omega) a (Finset.filter_subset _ _) ?_ ?_
  · intro j hj
    exact (re_mem_Icc_of_mem_realDiameterDisc a R (ξ ψ j) (Finset.mem_filter.mp hj).2).1
  · rw [heq]
    exact Finset.card_le_card hsuff

end NLS.ZakharovShabat
