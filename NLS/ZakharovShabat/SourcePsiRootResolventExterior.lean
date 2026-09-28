import NLS.ZakharovShabat.SourcePsiVariationCutoffResolvent
import NLS.ZakharovShabat.RelativeProductsExteriorLimit
import NLS.ZakharovShabat.CentralDeformation
import NLS.ZakharovShabat.UniformThresholds
import NLS.SequenceSpaces.FiniteExponentTail

/-!
# Exterior comparison for the root resolvent

At a fixed `ℓᵖ` displacement sequence, the distant coordinates are
small and the finitely many remaining roots are far from large
spectral parameters. Outside fixed free-lattice discs this makes every
actual-root denominator comparable to its free denominator.
-/

noncomputable section
open Set Filter Topology Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Far enough outside fixed free-lattice discs, every displacement
is at most half the corresponding free denominator. -/
theorem exists_threshold_two_rootDisplacement_le_freeDenominator
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (a : Coeff p)
    {r : ℝ} (hr : 0 < r) :
    ∃ R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ →
      (∀ m : ℤ, r ≤ ‖z - (Real.pi : ℂ) * m‖) →
      ∀ m : ℤ, 2 * ‖a m‖ ≤ ‖z - (Real.pi : ℂ) * m‖ := by
  have hpr : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' hp
  obtain ⟨M,hM⟩ := NLS.Coeff.exists_natAbs_norm_lt hpr a
    (half_pos hr)
  let R : ℝ := 2 * ‖a‖ + Real.pi * (M : ℝ)
  refine ⟨R,?_⟩
  intro z hz hsep m
  by_cases htail : M ≤ m.natAbs
  · have ha := hM m htail
    linarith [hsep m]
  · have ha : ‖a m‖ ≤ ‖a‖ :=
      lp.norm_apply_le_norm
        (ne_of_gt (zero_lt_one.trans_le (Fact.out : 1 ≤ p))) a m
    have hm : (m.natAbs : ℝ) ≤ (M : ℝ) := by
      exact_mod_cast (show m.natAbs ≤ M by omega)
    have hcenter : ‖(Real.pi : ℂ) * m‖ =
        Real.pi * (m.natAbs : ℝ) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos, Complex.norm_intCast]
      simp only [Nat.cast_natAbs, Int.cast_abs]
    have htri := norm_le_norm_sub_add z ((Real.pi : ℂ) * m)
    rw [hcenter] at htri
    dsimp [R] at hz
    nlinarith [Real.pi_pos]

/-- The actual-root denominator is at least half the free one
under the exterior displacement comparison. -/
theorem freeDenominator_le_two_actualRootDenominator
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (a : Coeff p) (z : ℂ) (m : ℤ)
    (hsmall : 2 * ‖a m‖ ≤ ‖z - (Real.pi : ℂ) * m‖) :
    ‖z - (Real.pi : ℂ) * m‖ ≤
      2 * ‖z - displacedRoots a m‖ := by
  have heq : z - (Real.pi : ℂ) * m =
      (z - displacedRoots a m) + a m := by
    simp only [displacedRoots]
    ring
  rw [heq] at hsmall ⊢
  have htri := norm_add_le (z - displacedRoots a m) (a m)
  linarith

/-- The root-resolvent summand is bounded by twice the free
resolvent summand, including complex root displacements. -/
theorem norm_actualRootResolvent_le_twice_free
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (a h : Coeff p) (z : ℂ) (m : ℤ)
    {r : ℝ} (hr : 0 < r)
    (hsep : r ≤ ‖z - (Real.pi : ℂ) * m‖)
    (hsmall : 2 * ‖a m‖ ≤ ‖z - (Real.pi : ℂ) * m‖) :
    ‖h m / (displacedRoots a m - z)‖ ≤
      2 * ‖h m / (z - (Real.pi : ℂ) * m)‖ := by
  have hcomp := freeDenominator_le_two_actualRootDenominator a z m hsmall
  have hfree : 0 < ‖z - (Real.pi : ℂ) * m‖ := hr.trans_le hsep
  have hactual : 0 < ‖z - displacedRoots a m‖ := by
    by_contra hn
    have hz : ‖z - displacedRoots a m‖ = 0 :=
      le_antisymm (le_of_not_gt hn) (norm_nonneg _)
    rw [hz, mul_zero] at hcomp
    exact (not_le_of_gt hfree) hcomp
  rw [norm_div, norm_sub_rev (displacedRoots a m) z, norm_div]
  calc
    ‖h m‖ / ‖z - displacedRoots a m‖ ≤
        (2 * ‖h m‖) / ‖z - (Real.pi : ℂ) * m‖ := by
      apply (div_le_div_iff₀ hactual hfree).mpr
      nlinarith [mul_le_mul_of_nonneg_left hcomp (norm_nonneg (h m))]
    _ = 2 * (‖h m‖ / ‖z - (Real.pi : ℂ) * m‖) := by ring

/-- For fixed root and direction sequences, the actual-root
resolvent is absolutely summable and uniformly small at exterior
spectral parameters separated from the free lattice. -/
theorem exists_threshold_actualRootResolvent_sum_small
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (a h : Coeff p)
    {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi / 4)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ →
      (∀ m : ℤ, r ≤ ‖z - (Real.pi : ℂ) * m‖) →
      Summable (fun m : ℤ =>
        ‖h m / (displacedRoots a m - z)‖) ∧
      (∑' m : ℤ, ‖h m / (displacedRoots a m - z)‖) ≤ ε := by
  obtain ⟨Rgeom,hgeom⟩ :=
    exists_threshold_two_rootDisplacement_le_freeDenominator hp a hr
  let S := {z : ℂ // ∀ m : ℤ,
    r ≤ ‖z - (Real.pi : ℂ) * m‖}
  have hfreeLimit : Tendsto
      (fun z : S => ∑' m : ℤ,
        ‖h m / (z.val - (Real.pi : ℂ) * m)‖)
      (comap (fun z : S => ‖z.val‖) atTop) (𝓝 0) := by
    simpa only [displacedRoots, add_sub_cancel_left] using
      tendsto_tsum_norm_relativeDisplacement_of_separated hp
        (displacedRoots h) (memℓp_displacedRoots h)
        (fun z : S => z.val) tendsto_comap hr hrπ
        (fun z => z.property)
  obtain ⟨Rfree,hRfree⟩ := exists_threshold_of_eventually_comap_atTop
    (fun z : S => ‖z.val‖)
    (hfreeLimit.eventually (gt_mem_nhds (half_pos hε)))
  refine ⟨max Rgeom Rfree,?_⟩
  intro z hz hsep
  have hsmall := hgeom z ((le_max_left _ _).trans hz) hsep
  have hzfree := notMem_freeLattice_of_separated hr hsep
  have hfree : Summable (fun m : ℤ =>
      ‖h m / (z - (Real.pi : ℂ) * m)‖) := by
    simpa only [displacedRoots, add_sub_cancel_left] using
      summable_norm_spectralRelativeDisplacement hp
        (displacedRoots h) (memℓp_displacedRoots h) z hzfree
  have hpoint (m : ℤ) :
      ‖h m / (displacedRoots a m - z)‖ ≤
        2 * ‖h m / (z - (Real.pi : ℂ) * m)‖ :=
    norm_actualRootResolvent_le_twice_free a h z m hr (hsep m) (hsmall m)
  have hactual := (hfree.mul_left 2).of_nonneg_of_le
    (fun _ => norm_nonneg _) hpoint
  refine ⟨hactual,?_⟩
  have hbound := hactual.tsum_le_tsum hpoint (hfree.mul_left 2)
  rw [tsum_mul_left] at hbound
  have hfreeSmall := (hRfree ⟨z,hsep⟩ ((le_max_right _ _).trans hz)).le
  linarith

/-- All actual displaced roots avoid every sufficiently large
spectral point separated from the free lattice. -/
theorem exists_threshold_actualRoots_avoided
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (a : Coeff p)
    {r : ℝ} (hr : 0 < r) :
    ∃ R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ →
      (∀ m : ℤ, r ≤ ‖z - (Real.pi : ℂ) * m‖) →
      ∀ m : ℤ, z ≠ displacedRoots a m := by
  obtain ⟨R,hR⟩ :=
    exists_threshold_two_rootDisplacement_le_freeDenominator hp a hr
  refine ⟨R,?_⟩
  intro z hz hsep m heq
  have hcomp := freeDenominator_le_two_actualRootDenominator a z m
    (hR z hz hsep m)
  have hsep' := hsep m
  rw [heq, sub_self, norm_zero, mul_zero] at hcomp
  rw [heq] at hsep'
  exact (not_le_of_gt (hr.trans_le hsep')) hcomp

/-- On the large exterior, the entire numerator variation is the
psi numerator times an absolutely convergent actual-root resolvent.
The deleted coordinate contributes zero to the full sum. -/
theorem exists_threshold_sourcePsiCandidateVariation_resolvent_small
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (a h : Coeff p) (hdeleted : h n = 0)
    {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi / 4)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ →
      (∀ m : ℤ, r ≤ ‖z - (Real.pi : ℂ) * m‖) →
      sourcePsiCandidateVariation n a h z =
        sourcePsiCandidate n (z,a) *
          ∑' m : ℤ, h m / (displacedRoots a m - z) ∧
      ‖∑' m : ℤ, h m / (displacedRoots a m - z)‖ ≤ ε := by
  obtain ⟨Rsum,hRsum⟩ :=
    exists_threshold_actualRootResolvent_sum_small hp a h hr hrπ hε
  obtain ⟨Ravoid,hRavoid⟩ := exists_threshold_actualRoots_avoided hp a hr
  refine ⟨max Rsum Ravoid,?_⟩
  intro z hz hsep
  have hsum := hRsum z ((le_max_left _ _).trans hz) hsep
  have havoid := hRavoid z ((le_max_right _ _).trans hz) hsep
  let F : ℤ → ℂ := fun m => h m / (displacedRoots a m - z)
  have hF : Summable F := hsum.1.of_norm
  have hFn : F n = 0 := by simp [F,hdeleted]
  have hcut (N : ℕ) :
      (∑ m ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ)).erase n, F m) =
        ∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), F m := by
    by_cases hn : n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ)
    · rw [← Finset.sum_erase_add _ _ hn, hFn, add_zero]
    · rw [Finset.erase_eq_self.mpr hn]
  have hlimit : Tendsto
      (fun N : ℕ =>
        ∑ m ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ)).erase n, F m)
      atTop (𝓝 (∑' m : ℤ, F m)) := by
    simpa only [Function.comp_def, hcut] using
      hF.hasSum.comp Finset.tendsto_Icc_neg
  have hformula := sourcePsiCandidateVariation_eq_mul_resolventLimit
    hp hp1 n a h z (∑' m : ℤ, F m)
      (fun m hmn => havoid m) hlimit
  refine ⟨hformula,?_⟩
  exact (norm_tsum_le_tsum_norm hsum.1).trans hsum.2

/-- On all sufficiently large half-integer-radius circles, the
variation has its exact root-resolvent formula and the resolvent is
uniformly smaller than any prescribed positive tolerance. -/
theorem eventually_centralCircle_sourcePsiCandidateVariation_resolvent_small
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (a h : Coeff p) (hdeleted : h n = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      ∀ z ∈ sphere (0 : ℂ) (centralCircleRadius k),
        sourcePsiCandidateVariation n a h z =
          sourcePsiCandidate n (z,a) *
            ∑' m : ℤ, h m / (displacedRoots a m - z) ∧
        ‖∑' m : ℤ, h m / (displacedRoots a m - z)‖ ≤ ε := by
  obtain ⟨R,hR⟩ :=
    exists_threshold_sourcePsiCandidateVariation_resolvent_small
      hp hp1 n a h hdeleted (by positivity : 0 < Real.pi / 4)
        le_rfl hε
  obtain ⟨K,hK⟩ := exists_nat_gt (R / Real.pi)
  refine ⟨K,?_⟩
  intro k hk z hz
  have hK : R < (K : ℝ) * Real.pi := by
    apply (div_lt_iff₀ Real.pi_pos).mp
    exact_mod_cast hK
  have hkreal : (K : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hRk : R ≤ centralCircleRadius k := by
    unfold centralCircleRadius
    nlinarith [Real.pi_pos]
  have hnorm : ‖z‖ = centralCircleRadius k := by
    simpa only [mem_sphere, dist_zero_right] using hz
  apply hR z (by rw [hnorm]; exact hRk)
  intro m
  have hsep := centralCircle_lattice_gap k hz m
  nlinarith [Real.pi_pos]

end NLS.ZakharovShabat
