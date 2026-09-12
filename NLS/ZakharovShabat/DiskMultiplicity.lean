import NLS.ZakharovShabat.FreeMultiplicity
import NLS.ZakharovShabat.ContourAnalytic
import NLS.ZakharovShabat.FrequencyLocalization
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Multiplicity in high-frequency spectral disks

Contour rank is constant on any preconnected set of potentials for which the
circle stays in the resolvent set. The uniform convex neighborhoods from
Lemma 3.4 connect every potential to zero, where each isolated free value has
algebraic multiplicity two. This proves the disk count in Proposition 1.1(i).
-/

noncomputable section
open Complex Metric Topology
open scoped ENNReal

namespace NLS.ZakharovShabat

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Rank cannot change along a preconnected family with a common resolvent circle. -/
theorem finrank_contour_eq_on_preconnected (hp : p ≠ ⊤) (c : ℂ) (r : ℝ)
    (hr : 0 ≤ r) {U : Set (PairSpace p)} (hU : IsPreconnected U)
    (hc : ∀ ψ ∈ U, sphere c r ⊆ resolventSet hp ψ)
    {φ ψ : PairSpace p} (hφ : φ ∈ U) (hψ : ψ ∈ U) :
    Module.finrank ℂ (resolventCircleIntegral hp φ c r).range =
      Module.finrank ℂ (resolventCircleIntegral hp ψ c r).range := by
  let : PreconnectedSpace U := Subtype.preconnectedSpace hU
  have hl : IsLocallyConstant (fun a : U =>
      Module.finrank ℂ (resolventCircleIntegral hp a.val c r).range) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro a
    have he := eventually_finrank_resolventCircleIntegral_eq hp a.val c r hr
      (hc a.val a.property)
    have ht := continuous_subtype_val.continuousAt.eventually he
    filter_upwards [ht] with b hb using hb.2
  exact hl.apply_eq_of_preconnectedSpace ⟨φ, hφ⟩ ⟨ψ, hψ⟩

/-- Total algebraic multiplicity is unchanged along the same family. -/
theorem sum_enclosed_multiplicity_eq_on_preconnected (hp : p ≠ ⊤) (c : ℂ) (r : ℝ)
    (hr : 0 ≤ r) {U : Set (PairSpace p)} (hU : IsPreconnected U)
    (hc : ∀ ψ ∈ U, sphere c r ⊆ resolventSet hp ψ)
    {φ ψ : PairSpace p} (hφ : φ ∈ U) (hψ : ψ ∈ U) :
    ∑ z ∈ enclosedPeriodicSpectrum hp φ c r, periodicAlgebraicMultiplicity hp φ z =
      ∑ z ∈ enclosedPeriodicSpectrum hp ψ c r, periodicAlgebraicMultiplicity hp ψ z := by
  rw [← finrank_range_resolventCircleIntegral hp φ c r hr (hc φ hφ),
    ← finrank_range_resolventCircleIntegral hp ψ c r hr (hc ψ hψ)]
  exact finrank_contour_eq_on_preconnected hp c r hr hU hc hφ hψ

/-- A disk of radius at most `π` about a free eigenvalue contains only that value. -/
theorem enclosedPeriodicSpectrum_zero (hp : p ≠ ⊤) (n : ℤ) {r : ℝ}
    (hr : 0 < r) (hrπ : r ≤ Real.pi) :
    enclosedPeriodicSpectrum (p := p) hp 0 ((Real.pi : ℂ) * n) r =
      {((Real.pi : ℂ) * n)} := by
  classical
  ext z
  rw [mem_enclosedPeriodicSpectrum, Finset.mem_singleton]
  constructor
  · rintro ⟨hspec, hball⟩
    have hzlat : z ∈ freeLattice := by
      by_contra hzoff
      exact hspec (mem_resolventSet_zero_of_notMem hp z hzoff)
    obtain ⟨k, rfl⟩ := hzlat
    have hd := Metric.mem_ball.mp hball
    rw [dist_eq_norm, ← mul_sub] at hd
    have hnorm : ‖(Real.pi : ℂ) * ((k : ℂ) - n)‖ = Real.pi * |((k - n : ℤ) : ℝ)| := by
      rw [← Int.cast_sub]
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos, Complex.norm_intCast]
    rw [hnorm] at hd
    have hkn : k = n := by
      by_contra hkn
      have habs : 1 ≤ |((k - n : ℤ) : ℝ)| := by
        exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hkn)
      nlinarith [Real.pi_pos]
    rw [hkn]
  · intro hz
    subst z
    refine ⟨?_, by simpa using hr⟩
    exact (periodicAlgebraicMultiplicity_pos_iff hp 0 _).mp
      (by rw [periodicAlgebraicMultiplicity_zero]; norm_num)

/-- The total free multiplicity in any such disk is two. -/
theorem sum_enclosed_multiplicity_zero (hp : p ≠ ⊤) (n : ℤ) {r : ℝ}
    (hr : 0 < r) (hrπ : r ≤ Real.pi) :
    ∑ z ∈ enclosedPeriodicSpectrum (p := p) hp 0 ((Real.pi : ℂ) * n) r,
      periodicAlgebraicMultiplicity hp 0 z = 2 := by
  rw [enclosedPeriodicSpectrum_zero hp n hr hrπ, Finset.sum_singleton,
    periodicAlgebraicMultiplicity_zero]

/-- Proposition 1.1(i): uniformly near any potential and all along its deformation
to zero, every sufficiently far disk contains two eigenvalues counted algebraically.
The radius may be any positive number at most `π/4`. -/
theorem exists_uniform_disk_multiplicity_two (hp : p ≠ ⊤) (φ : PairSpace p)
    {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi / 4) :
    ∃ N : ℕ, ∃ U : Set (PairSpace p), IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, ∀ n : ℤ, N ≤ n.natAbs →
        sphere ((Real.pi : ℂ) * n) r ⊆ resolventSet hp ψ ∧
        Module.finrank ℂ (resolventCircleIntegral hp ψ ((Real.pi : ℂ) * n) r).range = 2 ∧
        (∑ z ∈ enclosedPeriodicSpectrum hp ψ ((Real.pi : ℂ) * n) r,
          periodicAlgebraicMultiplicity hp ψ z) = 2 := by
  obtain ⟨N, U, ho, hconv, hφ, h0, _, hstrip⟩ :=
    exists_uniform_highFrequency_resolvent hp φ hr hrπ
  refine ⟨N, U, ho, hconv, hφ, h0, ?_⟩
  intro ψ hψ n hn
  have hc : ∀ a ∈ U, sphere ((Real.pi : ℂ) * n) r ⊆ resolventSet hp a :=
    fun a ha => (sphere_subset_verticalStrip n hrπ).trans (hstrip a ha n hn)
  have hsum : (∑ z ∈ enclosedPeriodicSpectrum hp ψ ((Real.pi : ℂ) * n) r,
      periodicAlgebraicMultiplicity hp ψ z) = 2 :=
    (sum_enclosed_multiplicity_eq_on_preconnected hp _ r hr.le
      hconv.isPreconnected hc hψ h0).trans
        (sum_enclosed_multiplicity_zero hp n hr (by linarith [Real.pi_pos]))
  refine ⟨hc ψ hψ, ?_, hsum⟩
  rw [finrank_range_resolventCircleIntegral hp ψ _ r hr.le (hc ψ hψ)]
  exact hsum

end NLS.ZakharovShabat
