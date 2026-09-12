import NLS.ZakharovShabat.CentralSpectrum
import NLS.ZakharovShabat.DiskMultiplicity

/-!
# Deformation and multiplicity of the central spectral projection

A sufficiently large circle of half-integer lattice radius encloses exactly the
same spectrum as the corresponding central rectangle. This is an equality of
spectral selections, proved from localization: the circle need not contain the
corners of that rectangle. The resulting equality of whole spectral projections
transfers circle analyticity and rank stability to the central projection.
-/

noncomputable section
open Complex Metric Topology
open scoped ENNReal

namespace NLS.ZakharovShabat

/-- Radius halfway between the free spectral values with indices `K` and `K+1`. -/
def centralCircleRadius (K : ℕ) : ℝ := (K : ℝ) * Real.pi + Real.pi / 2

theorem centralCircleRadius_pos (K : ℕ) : 0 < centralCircleRadius K := by
  unfold centralCircleRadius
  positivity

private theorem norm_free_lattice (n : ℤ) : ‖(Real.pi : ℂ) * n‖ = Real.pi * (n.natAbs : ℝ) := by
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
    Complex.norm_intCast, Nat.cast_natAbs, Int.cast_abs]

/-- Every point on a half-integer-radius circle stays at least `π/2` from every
free lattice point, independently of its argument. -/
theorem centralCircle_lattice_gap (K : ℕ) {z : ℂ}
    (hz : z ∈ sphere 0 (centralCircleRadius K)) (n : ℤ) :
    Real.pi / 2 ≤ ‖z - (Real.pi : ℂ) * n‖ := by
  have hnorm : ‖z‖ = centralCircleRadius K := by simpa using hz
  by_cases hn : n.natAbs ≤ K
  · have h := norm_sub_norm_le z ((Real.pi : ℂ) * n)
    rw [hnorm, norm_free_lattice] at h
    have hn' : (n.natAbs : ℝ) ≤ (K : ℝ) := by exact_mod_cast hn
    unfold centralCircleRadius at h
    nlinarith [Real.pi_pos]
  · have h := norm_sub_norm_le ((Real.pi : ℂ) * n) z
    rw [hnorm, norm_free_lattice, norm_sub_rev] at h
    have hn' : (K : ℝ) + 1 ≤ (n.natAbs : ℝ) := by exact_mod_cast (show K + 1 ≤ n.natAbs by omega)
    unfold centralCircleRadius at h
    nlinarith [Real.pi_pos]

/-- Taking a sufficiently larger index puts the original closed box strictly
inside the new circle. -/
theorem closedCentralRectangle_subset_centralCircleBall (N K : ℕ) (hK : 2 * N + 1 ≤ K) :
    closedCentralRectangle N ⊆ ball 0 (centralCircleRadius K) := by
  intro z hz
  rw [mem_ball, dist_zero_right]
  have hn := (norm_le_abs_re_add_abs_im z).trans (add_le_add hz.1 hz.2)
  have hK' : 2 * (N : ℝ) + 1 ≤ (K : ℝ) := by exact_mod_cast hK
  have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  unfold centralCircleRadius
  nlinarith [Real.two_le_pi]

/-- A quarter-pi disk is selected by the outer circle and by its central box
exactly when its signed index is at most the cutoff in absolute value. -/
theorem smallDisk_central_selection (K : ℕ) (n : ℤ) {r : ℝ}
    (hrπ : r ≤ Real.pi / 4) (hrK : r ≤ (K : ℝ)) {z : ℂ}
    (hz : z ∈ ball ((Real.pi : ℂ) * n) r) :
    (z ∈ ball 0 (centralCircleRadius K) ↔ n.natAbs ≤ K) ∧
    (z ∈ centralSpectralBox K ↔ n.natAbs ≤ K) := by
  have hdiff : ‖z - (Real.pi : ℂ) * n‖ < r := by simpa only [mem_ball, dist_eq_norm] using hz
  have htri := norm_le_norm_sub_add z ((Real.pi : ℂ) * n)
  rw [norm_free_lattice] at htri
  have him : |z.im| ≤ (K : ℝ) := by
    have h := Complex.abs_im_le_norm (z - (Real.pi : ℂ) * n)
    have he : (z - (Real.pi : ℂ) * n).im = z.im := by simp
    rw [he] at h
    exact (h.trans hdiff.le).trans hrK
  have hforward (hn : n.natAbs ≤ K) : z ∈ ball 0 (centralCircleRadius K) ∧ z ∈ centralSpectralBox K := by
    have hn' : (n.natAbs : ℝ) ≤ (K : ℝ) := by exact_mod_cast hn
    have hnorm : ‖z‖ < centralCircleRadius K := by
      unfold centralCircleRadius
      nlinarith [Real.pi_pos]
    exact ⟨by simpa using hnorm, ⟨(Complex.abs_re_le_norm z).trans_lt hnorm, him⟩⟩
  have hback (hre : |z.re| < centralCircleRadius K) : n.natAbs ≤ K := by
    by_contra hn
    have hn' : (K : ℝ) + 1 ≤ (n.natAbs : ℝ) := by exact_mod_cast (show K + 1 ≤ n.natAbs by omega)
    have hreal : Real.pi * (n.natAbs : ℝ) ≤ |z.re| + ‖z - (Real.pi : ℂ) * n‖ := by
      have h := abs_add_le z.re (Real.pi * (n : ℝ) - z.re)
      have he : z.re + (Real.pi * (n : ℝ) - z.re) = Real.pi * (n : ℝ) := by ring
      rw [he, abs_mul, abs_of_pos Real.pi_pos] at h
      have hnorm := Complex.abs_re_le_norm (z - (Real.pi : ℂ) * n)
      have he' : |(n : ℝ)| = (n.natAbs : ℝ) := by simp only [Nat.cast_natAbs, Int.cast_abs]
      rw [he'] at h
      have hd : |Real.pi * (n : ℝ) - z.re| ≤ ‖z - (Real.pi : ℂ) * n‖ := by
        simpa only [sub_re, mul_re, ofReal_re, intCast_re, ofReal_im, intCast_im,
          mul_zero, sub_zero, abs_sub_comm] using hnorm
      exact h.trans (add_le_add le_rfl hd)
    unfold centralCircleRadius at hre
    nlinarith [Real.pi_pos]
  exact ⟨⟨fun hz => hback ((Complex.abs_re_le_norm z).trans_lt (by simpa using hz)),
      fun hn => (hforward hn).1⟩,
    ⟨fun hz => hback hz.1, fun hn => (hforward hn).2⟩⟩

/-- Under the original localization, a larger circle and its associated box
select exactly the same spectral parameters. -/
theorem centralCircle_spectral_selection (N K : ℕ) (hK : 2 * N + 1 ≤ K)
    {r : ℝ} (hrπ : r ≤ Real.pi / 4) (hrK : r ≤ (K : ℝ)) {z : ℂ}
    (hz : z ∈ centralSpectralBox N ∪ highSpectralDisks N r) :
    z ∈ ball 0 (centralCircleRadius K) ↔ z ∈ centralSpectralBox K := by
  rcases hz with hbox | hdisks
  · have hball := closedCentralRectangle_subset_centralCircleBall N K hK ⟨hbox.1.le, hbox.2⟩
    have hNK : (N : ℝ) ≤ (K : ℝ) := by exact_mod_cast (show N ≤ K by omega)
    have hboxK : z ∈ centralSpectralBox K := by
      constructor
      · have hπ := mul_le_mul_of_nonneg_right hNK Real.pi_pos.le
        exact hbox.1.trans_le (add_le_add hπ le_rfl)
      · exact hbox.2.trans hNK
    exact iff_of_true hball hboxK
  · obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hdisks
    obtain ⟨_, hn⟩ := Set.mem_iUnion.mp hn
    have h := smallDisk_central_selection K n hrπ hrK hn
    exact h.1.trans h.2.symm

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Uniform localization supplies a common cutoff above which every large circle
has exactly the central algebraic projection throughout one open convex neighborhood. -/
theorem exists_uniform_centralCircle (hp : p ≠ ⊤) (φ : PairSpace p) :
    ∃ K₀ : ℕ, ∃ U : Set (PairSpace p), 0 < K₀ ∧ IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, ∀ K : ℕ, K₀ ≤ K →
        centralRectangleBoundary K ⊆ resolventSet hp ψ ∧
        sphere 0 (centralCircleRadius K) ⊆ resolventSet hp ψ ∧
        enclosedPeriodicSpectrum hp ψ 0 (centralCircleRadius K) = centralPeriodicSpectrum hp ψ K ∧
        centralSpectralProjection hp ψ K = resolventCircleIntegral hp ψ 0 (centralCircleRadius K) := by
  obtain ⟨N, U, _, ho, hconv, hφ, h0, hregion⟩ :=
    exists_uniform_centralRectangle_resolvent hp φ (r := Real.pi / 4) (by positivity) le_rfl
  let K₀ := 2 * N + 1
  have hK₀ : 0 < K₀ := by dsimp [K₀]; omega
  refine ⟨K₀, U, hK₀, ho, hconv, hφ, h0, ?_⟩
  intro ψ hψ K hK
  have hNK : N ≤ K := by dsimp [K₀] at hK; omega
  have hrK : Real.pi / 4 ≤ (K : ℝ) := by
    have h1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast (hK₀.trans_le hK)
    linarith [Real.pi_le_four]
  have hExt := (hregion ψ hψ N le_rfl).2.1
  have hcircle : sphere 0 (centralCircleRadius K) ⊆ resolventSet hp ψ := by
    intro z hz
    apply hExt
    rw [mem_spectralExterior]
    refine ⟨?_, fun n _ => (show Real.pi / 4 ≤ Real.pi / 2 by linarith [Real.pi_pos]).trans
      (centralCircle_lattice_gap K hz n)⟩
    intro hbox
    have hb := closedCentralRectangle_subset_centralCircleBall N K hK ⟨hbox.1.le, hbox.2⟩
    exact sphere_disjoint_ball.le_bot ⟨hz, hb⟩
  have he : enclosedPeriodicSpectrum hp ψ 0 (centralCircleRadius K) = centralPeriodicSpectrum hp ψ K := by
    ext z
    rw [mem_enclosedPeriodicSpectrum, mem_centralPeriodicSpectrum]
    by_cases hz : z ∈ periodicSpectrum hp ψ
    · exact and_congr_right fun _ => centralCircle_spectral_selection N K hK le_rfl hrK
        (periodicSpectrum_subset_box_union_disks hp ψ N (Real.pi / 4) hExt hz)
    · simp [hz]
  refine ⟨(hregion ψ hψ K hNK).1, hcircle, he, ?_⟩
  rw [resolventCircleIntegral_eq_clusterProjection hp ψ 0 _ (centralCircleRadius_pos K).le hcircle, he]
  rfl

/-- Proposition 1.1(ii)'s total central count, uniformly for all sufficiently
large cutoffs: the central projection is analytic on a convex neighborhood
joining the given potential to zero, and its rank and multiplicity are `4K+2`. -/
theorem exists_uniform_central_multiplicity (hp : p ≠ ⊤) (φ : PairSpace p) :
    ∃ K₀ : ℕ, ∃ U : Set (PairSpace p), 0 < K₀ ∧ IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      (∀ K : ℕ, K₀ ≤ K → AnalyticOnNhd ℂ (fun ψ => centralSpectralProjection hp ψ K) U) ∧
      ∀ ψ ∈ U, ∀ K : ℕ, K₀ ≤ K → centralRectangleBoundary K ⊆ resolventSet hp ψ ∧
        Module.finrank ℂ (centralSpectralProjection hp ψ K).range = 4 * K + 2 ∧
        (∑ z ∈ centralPeriodicSpectrum hp ψ K, periodicAlgebraicMultiplicity hp ψ z) = 4 * K + 2 := by
  obtain ⟨K₀, U, hK₀, ho, hconv, hφ, h0, h⟩ := exists_uniform_centralCircle hp φ
  have han (K : ℕ) (hK : K₀ ≤ K) : AnalyticOnNhd ℂ (fun ψ => centralSpectralProjection hp ψ K) U := by
    intro ψ hψ
    apply (analyticAt_resolventCircleIntegral hp ψ 0 _ (centralCircleRadius_pos K).le
      (h ψ hψ K hK).2.1).congr
    filter_upwards [ho.mem_nhds hψ] with a ha
    exact (h a ha K hK).2.2.2.symm
  refine ⟨K₀, U, hK₀, ho, hconv, hφ, h0, han, ?_⟩
  intro ψ hψ K hK
  have hrank : Module.finrank ℂ (centralSpectralProjection hp ψ K).range = 4 * K + 2 := by
    rw [(h ψ hψ K hK).2.2.2]
    calc
      _ = Module.finrank ℂ (resolventCircleIntegral hp 0 0 (centralCircleRadius K)).range :=
        finrank_contour_eq_on_preconnected hp 0 _ (centralCircleRadius_pos K).le
          hconv.isPreconnected (fun a ha => (h a ha K hK).2.1) hψ h0
      _ = _ := by rw [← (h 0 h0 K hK).2.2.2, finrank_range_centralSpectralProjection_zero]
  refine ⟨(h ψ hψ K hK).1, hrank, ?_⟩
  rw [← finrank_range_centralSpectralProjection]
  exact hrank

end NLS.ZakharovShabat
