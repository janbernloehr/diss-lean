import NLS.KdV.HillCharacteristicZeros
import NLS.KdV.HillRealSpectrum
import NLS.ComplexAnalysis.TracePrimitiveContinuation

/-! # Free-normalized source primitives of the actual L2 Hill trace

The shared analytic trace continuation is instantiated with the actual
rough monodromy trace and its checked free normalization. Both open
nonreal half-planes are covered at every real period-one L2 potential.
Every checked high contour also admits one common complex L2 potential
neighborhood. Extension across real bands and action integrals remain
separate obligations.
-/

noncomputable section
open Set Metric Complex
open NLS.ComplexAnalysis
namespace NLS.KdV

def hillL2SourceFamily : TracePrimitiveFamily (Coeff 2) where
  trace := fun t => hillL2Discriminant t.2 t.1
  analytic_trace := analyticOnNhd_hillL2Discriminant_joint
  freePrimitive := classicalHillFreePrimitive
  freeDomain := slitPlane
  isOpen_freeDomain := isOpen_slitPlane
  analytic_freePrimitive := analyticOnNhd_classicalHillFreePrimitive
  free_trace := fun z => by
    rw [hillL2Discriminant_zero]
    simpa only [classicalHillDiscriminant_zero] using two_cosh_classicalHillFreePrimitive z

def hillL2ContinuationDomain : Set (ℂ × Coeff 2) := hillL2SourceFamily.continuationDomain

def hillL2ContinuedRoot : ℂ × Coeff 2 → ℂ := hillL2SourceFamily.root

def hillL2ContinuedMultiplier : ℂ × Coeff 2 → ℂ := hillL2SourceFamily.multiplier

def hillL2ContinuedPrimitive : ℂ × Coeff 2 → ℂ := hillL2SourceFamily.primitive

theorem isOpen_hillL2ContinuationDomain : IsOpen hillL2ContinuationDomain :=
  hillL2SourceFamily.isOpen_continuationDomain

theorem mem_hillL2ContinuationDomain_iff (t : ℂ × Coeff 2) :
    t ∈ hillL2ContinuationDomain ↔ t.1 ∈ slitPlane ∧
      ∀ s ∈ Icc (0 : ℝ) 1, hillL2Radicand ((s : ℂ) • t.2) t.1 ≠ 0 := by
  constructor
  · intro ht
    refine ⟨(hillL2SourceFamily.continuationDomain_subset ht).1,?_⟩
    intro s hs
    simpa only [TracePrimitiveFamily.rootDomain,TracePrimitiveFamily.radicand,
      hillL2SourceFamily,sourceSegmentMap,zero_add,sub_zero,hillL2Radicand] using (ht s hs).2
  · rintro ⟨hslit,hne⟩ s hs
    refine ⟨hslit,?_⟩
    simpa only [TracePrimitiveFamily.radicand,hillL2SourceFamily,sourceSegmentMap,
      zero_add,sub_zero,hillL2Radicand] using hne s hs

theorem analyticOnNhd_hillL2ContinuedRoot :
    AnalyticOnNhd ℂ hillL2ContinuedRoot hillL2ContinuationDomain := hillL2SourceFamily.analytic_root

theorem analyticOnNhd_hillL2ContinuedPrimitive :
    AnalyticOnNhd ℂ hillL2ContinuedPrimitive hillL2ContinuationDomain :=
  hillL2SourceFamily.analytic_primitive

@[simp] theorem hillL2ContinuedRoot_base (z : ℂ) :
    hillL2ContinuedRoot (z,0) = classicalHillFreeRoot z := hillL2SourceFamily.root_base z

@[simp] theorem hillL2ContinuedPrimitive_base (z : ℂ) :
    hillL2ContinuedPrimitive (z,0) = -I*Complex.sqrt z := hillL2SourceFamily.primitive_base z

theorem hillL2ContinuedRoot_sq (t : ℂ × Coeff 2) (ht : t ∈ hillL2ContinuationDomain) :
    hillL2ContinuedRoot t ^ 2 = hillL2Radicand t.2 t.1 := hillL2SourceFamily.root_sq t ht

theorem hillL2ContinuedRoot_ne_zero (t : ℂ × Coeff 2) (ht : t ∈ hillL2ContinuationDomain) :
    hillL2ContinuedRoot t ≠ 0 := hillL2SourceFamily.root_ne_zero t ht

theorem exp_hillL2ContinuedPrimitive (t : ℂ × Coeff 2) (ht : t ∈ hillL2ContinuationDomain) :
    exp (hillL2ContinuedPrimitive t) = hillL2ContinuedMultiplier t :=
  hillL2SourceFamily.exp_primitive t ht

theorem hillL2ContinuedPrimitive_trace (t : ℂ × Coeff 2) (ht : t ∈ hillL2ContinuationDomain) :
    2*cosh (hillL2ContinuedPrimitive t) = hillL2Discriminant t.2 t.1 ∧
      2*sinh (hillL2ContinuedPrimitive t) = hillL2ContinuedRoot t :=
  hillL2SourceFamily.primitive_trace t ht

theorem hasFDerivAt_hillL2ContinuedPrimitive (t : ℂ × Coeff 2)
    (ht : t ∈ hillL2ContinuationDomain) :
    HasFDerivAt hillL2ContinuedPrimitive
      ((hillL2ContinuedRoot t)⁻¹ •
        fderiv ℂ (fun a : ℂ × Coeff 2 => hillL2Discriminant a.2 a.1) t) t :=
  hillL2SourceFamily.hasFDerivAt_primitive t ht

theorem hasDerivAt_hillL2ContinuedPrimitive (t : ℂ × Coeff 2)
    (ht : t ∈ hillL2ContinuationDomain) :
    HasDerivAt (fun z => hillL2ContinuedPrimitive (z,t.2))
      (deriv (hillL2Discriminant t.2) t.1 / hillL2ContinuedRoot t) t.1 :=
  hillL2SourceFamily.hasDerivAt_primitive t ht

/-- Reality of the actual physical characteristic excludes every source
segment branch point at a nonreal energy. -/
theorem mem_hillL2ContinuationDomain_of_im_ne_zero
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hreal : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (z : ℂ) (him : z.im ≠ 0) :
    (z,SpectralWeight.one.toCoeff q) ∈ hillL2ContinuationDomain := by
  rw [mem_hillL2ContinuationDomain_iff]
  refine ⟨mem_slitPlane_iff.mpr (Or.inr him),?_⟩
  intro s _ hd
  have hp : SpectralWeight.one.toCoeff ((s : ℂ) • q) ∈ Coeff.paritySubspace 0 := by
    rw [map_smul]
    exact (Coeff.paritySubspace 0).smul_mem _ hq
  have hr : IsRealHillPotential (SpectralWeight.one.toCoeff ((s : ℂ) • q)) := by
    simpa only [map_smul] using hreal.smul_real s
  have hd' : hillL2Discriminant (SpectralWeight.one.toCoeff ((s : ℂ) • q)) z ^ 2 = 4 := by
    simpa only [map_smul,hillL2Radicand,sub_eq_zero] using hd
  exact him (hillL2Discriminant_root_im_zero _ hp hr z hd')

theorem analyticOnNhd_hillL2ContinuedPrimitive_off_real
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hreal : IsRealHillPotential (SpectralWeight.one.toCoeff q)) :
    AnalyticOnNhd ℂ (fun z => hillL2ContinuedPrimitive (z,SpectralWeight.one.toCoeff q))
      {z | z.im ≠ 0} := by
  intro z hz
  exact (analyticOnNhd_hillL2ContinuedPrimitive _
    (mem_hillL2ContinuationDomain_of_im_ne_zero q hq hreal z hz)).comp
    (f := fun z : ℂ => (z,SpectralWeight.one.toCoeff q)) (analyticAt_id.prod analyticAt_const)

/-- Each positive free energy disc avoids the principal square-root cut. -/
theorem hillClosedBall_subset_slitPlane (n : ℕ) (hn : 1 ≤ n) :
    closedBall (freeHillValue n : ℂ) (n : ℝ) ⊆ slitPlane := by
  intro z hz
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpi : 9 < Real.pi^2 := by nlinarith [Real.pi_gt_three]
  have hd : |z.re-freeHillValue n| ≤ (n : ℝ) := by
    have h := Complex.abs_re_le_norm (z-(freeHillValue n : ℂ))
    have he : ‖z-(freeHillValue n : ℂ)‖ ≤ (n : ℝ) := by
      simpa only [mem_closedBall,dist_eq_norm] using hz
    have hh : |z.re-freeHillValue n| ≤ ‖z-(freeHillValue n : ℂ)‖ := by
      simpa only [sub_re,ofReal_re] using h
    exact hh.trans he
  have hpos : 0 < z.re := by
    have hf : freeHillValue n = Real.pi^2*(n : ℝ)^2 := by simp only [freeHillValue,Int.cast_natCast]
    rw [hf] at hd
    have hprod := mul_lt_mul_of_pos_right hpi (sq_pos_of_pos (show (0 : ℝ) < n by linarith))
    nlinarith [(abs_le.mp hd).1]
  exact mem_slitPlane_iff.mpr (Or.inl hpos)

/-- The whole checked disc outside the source-localized roots lies on
the free-normalized sheet, uniformly along the potential segment. -/
theorem mem_hillL2ContinuationDomain_of_high_distance
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (n : ℕ) (hn : 1 ≤ n) (hcut : 16*‖q‖ ≤ (n : ℝ))
    (z : ℂ) (hz : z ∈ closedBall (freeHillValue n : ℂ) (n : ℝ))
    (hfar : 4*‖q‖ < ‖z-(freeHillValue n : ℂ)‖) :
    (z,SpectralWeight.one.toCoeff q) ∈ hillL2ContinuationDomain := by
  rw [mem_hillL2ContinuationDomain_iff]
  refine ⟨hillClosedBall_subset_slitPlane n hn hz,?_⟩
  intro s hs hd
  have hnorm : ‖(s : ℂ) • q‖ ≤ ‖q‖ := by
    rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hs.1]
    exact mul_le_of_le_one_left (norm_nonneg q) hs.2
  have hp : SpectralWeight.one.toCoeff ((s : ℂ) • q) ∈ Coeff.paritySubspace 0 := by
    rw [map_smul]
    exact (Coeff.paritySubspace 0).smul_mem _ hq
  have hd' : hillL2Radicand (SpectralWeight.one.toCoeff ((s : ℂ) • q)) z = 0 := by
    simpa only [map_smul] using hd
  have hl := hillL2Radicand_zero_localization ((s : ℂ) • q) hp n hn z
    (openHillStrip_subset n (hillClosedBall_subset_openStrip n hn hz))
    (show 8*‖(s : ℂ) • q‖ ≤ (n : ℝ) by linarith) hd'
  linarith

/-- The complete high contour lies on the same free-normalized source
sheet, including its two real crossings. This also holds for complex q. -/
theorem mem_hillL2ContinuationDomain_high_sphere
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (n : ℕ) (hn : 1 ≤ n) (hcut : 16*‖q‖ ≤ (n : ℝ))
    (z : ℂ) (hz : z ∈ sphere (freeHillValue n : ℂ) (n : ℝ)) :
    (z,SpectralWeight.one.toCoeff q) ∈ hillL2ContinuationDomain := by
  rw [mem_hillL2ContinuationDomain_iff]
  refine ⟨hillClosedBall_subset_slitPlane n hn (sphere_subset_closedBall hz),?_⟩
  intro s hs
  have hnorm : ‖(s : ℂ) • q‖ ≤ ‖q‖ := by
    rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hs.1]
    exact mul_le_of_le_one_left (norm_nonneg q) hs.2
  have hp : SpectralWeight.one.toCoeff ((s : ℂ) • q) ∈ Coeff.paritySubspace 0 := by
    rw [map_smul]
    exact (Coeff.paritySubspace 0).smul_mem _ hq
  have he := hillL2Radicand_ne_zero_on_sphere ((s : ℂ) • q) hp n hn
    (show 16*‖(s : ℂ) • q‖ ≤ (n : ℝ) by linarith) z hz
  simpa only [map_smul] using he

/-- One open complex L2 neighborhood works for the full compact contour. -/
theorem exists_hillL2Continuation_high_contour_neighborhood
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (n : ℕ) (hn : 1 ≤ n) (hcut : 16*‖q‖ ≤ (n : ℝ)) :
    ∃ V : Set (Coeff 2), IsOpen V ∧ SpectralWeight.one.toCoeff q ∈ V ∧
      sphere (freeHillValue n : ℂ) (n : ℝ) ×ˢ V ⊆ hillL2ContinuationDomain :=
  hillL2SourceFamily.exists_continuation_neighborhood _ (isCompact_sphere _ _) _
    (mem_hillL2ContinuationDomain_high_sphere q hq n hn hcut)

end NLS.KdV
