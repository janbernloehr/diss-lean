import NLS.ZakharovShabat.CanonicalBoundaryRoots
import NLS.ComplexAnalysis.RealDiameterDiscs

/-! # Central boundary labels selected by their real parts
The closed vertical strip through the central box contains precisely the
central labels. This allows real-diameter counting discs with arbitrary
imaginary height without mistaking the central box for a disc.
-/

noncomputable section
open Set Complex Metric
open NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.ZakharovShabat.BoundaryRootLabeling
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {b : BoundaryCondition} {hp : p ≠ ⊤}
variable {φ : PairSpace p} {hφ : φ ∈ dirichletSubspace} {N : ℕ} {ξ : ℤ → ℂ}

/-- Central real parts lie strictly inside the central strip. -/
theorem abs_re_central_lt (h : BoundaryRootLabeling b hp φ hφ N ξ)
    (n : ℤ) (hn : n.natAbs ≤ N) : |(ξ n).re| < centralCircleRadius N :=
  (h.central_mem n hn).1

/-- A label lies in the closed central vertical strip exactly when its index is central. -/
theorem abs_re_le_iff (h : BoundaryRootLabeling b hp φ hφ N ξ) (n : ℤ) :
    |(ξ n).re| ≤ centralCircleRadius N ↔ n.natAbs ≤ N := by
  refine ⟨fun hz => ?_,fun hn => (h.abs_re_central_lt n hn).le⟩
  by_contra hn
  have hd := abs_lt.mp (h.abs_re_distant_sub_lt n (by omega))
  have hb := abs_le.mp hz
  unfold centralCircleRadius at hb
  by_cases hn0 : 0 ≤ n
  · have hN : (N : ℝ)+1 ≤ (n : ℝ) := by exact_mod_cast (show (N : ℤ)+1 ≤ n by omega)
    nlinarith [Real.pi_pos]
  · have hN : (n : ℝ) ≤ -(N : ℝ)-1 := by exact_mod_cast (show n ≤ -(N : ℤ)-1 by omega)
    nlinarith [Real.pi_pos]

/-- Among actual boundary roots, central-strip membership is the exact central spectral selection. -/
theorem mem_centralSpectrum_iff_abs_re_le (h : BoundaryRootLabeling b hp φ hφ N ξ)
    (z : ℂ) (hz : z ∈ b.spectrum hp φ hφ) :
    z ∈ b.centralSpectrum hp φ hφ N ↔ |z.re| ≤ centralCircleRadius N := by
  obtain ⟨n,rfl⟩ := (h.exhaustive z).mp hz
  constructor
  · intro hc
    exact ((b.mem_centralSpectrum hp φ hφ N _).mp hc).2.1.le
  · intro hn
    exact (h.central_iff _).mpr ⟨n,(h.abs_re_le_iff n).mp hn,rfl⟩

/-- Real endpoints avoiding central labels give a zero-free characteristic circle at real type. -/
theorem realDiameterSphere_nonzero_of_realType (h : BoundaryRootLabeling b hp φ hφ N ξ)
    (hp1 : 1 < p) (hreal : IsRealType φ) (a c : ℝ)
    (ha : -centralCircleRadius N ≤ a) (hc : c ≤ centralCircleRadius N)
    (hneA : ∀ n : ℤ, n.natAbs ≤ N → (ξ n).re ≠ a)
    (hneC : ∀ n : ℤ, n.natAbs ≤ N → (ξ n).re ≠ c) :
    ∀ z ∈ sphere (((a+c)/2 : ℝ) : ℂ) ((c-a)/2), b.characteristic hp φ hφ z ≠ 0 := by
  intro z hz hzero
  have hspec := (b.characteristic_eq_zero_iff hp hp1 φ hφ z).mp hzero
  have hr := re_mem_Icc_of_mem_realDiameterDisc a c z (sphere_subset_closedBall hz)
  obtain ⟨n,rfl⟩ := (h.exhaustive z).mp hspec
  have hn := (h.abs_re_le_iff n).mp (abs_le.mpr ⟨ha.trans hr.1,hr.2.trans hc⟩)
  have him := periodicSpectrum_im_eq_zero_of_realType hp φ hreal _ (b.spectrum_subset_periodic hp φ hφ hspec)
  rcases re_eq_endpoints_of_mem_realDiameterSphere a c (ξ n) him hz with he | he
  · exact hneA n hn he
  · exact hneC n hn he

end NLS.ZakharovShabat.BoundaryRootLabeling
