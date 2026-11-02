import NLS.SequenceSpaces.WeightedWeakStarLowerTopology
import NLS.Dynamics.ActionDependentWeightedPhaseFlow

/-!
# Action-dependent phase evolution at the weak-star endpoint

Real frequency sequences may be unbounded. The evolution preserves the full
weighted endpoint norm; its orbit is weak-star continuous, and coordinatewise
continuous realized frequencies give continuous compact-time trajectories on
norm-bounded subsets of the weak dual. No KdV frequency or physical Birkhoff
map is postulated or constructed here.

The parameter r is the Wiener predual order; coefficient order is -r.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.WeightedCoeff

@[simp] theorem weakStarCoeff_wienerDualRealization (r : ℝ)
    (a : WeightedCoeff (Weight.sobolev (-r)) ⊤) :
    weakStarCoeff r (wienerDualRealization r a) = a := by
  change sobolevCotangent (q := ⊤) r (by simp)
    ((sobolevBilinearPairing (p := 1) (q := ⊤) r).flip a) = a
  exact sobolevCotangent_pairing r (by simp) a

@[simp] theorem wienerDualRealization_weakStarCoeff (r : ℝ)
    (f : WeakDual ℂ (WeightedCoeff (Weight.sobolev r) 1)) :
    wienerDualRealization r (weakStarCoeff r f) = f := by
  apply (WeakDual.toStrongDual (𝕜 := ℂ)).injective
  change sobolevDualityIsometry (p := 1) (q := ⊤) r (by simp)
    (sobolevCotangent r (by simp) f.toStrongDual) = f.toStrongDual
  rw [← sobolevDualityIsometry_symm_apply, LinearIsometryEquiv.apply_symm_apply]

@[simp] theorem norm_weakStarCoeff (r : ℝ)
    (f : WeakDual ℂ (WeightedCoeff (Weight.sobolev r) 1)) :
    ‖weakStarCoeff r f‖ = ‖f.toStrongDual‖ :=
  norm_sobolevCotangent r (by simp) f.toStrongDual

@[simp] theorem norm_wienerDualRealization (r : ℝ)
    (a : WeightedCoeff (Weight.sobolev (-r)) ⊤) :
    ‖(wienerDualRealization r a).toStrongDual‖ = ‖a‖ :=
  (sobolevDualityIsometry (p := 1) (q := ⊤) r (by simp)).norm_map a

/-- The actual weighted endpoint realization of the shared nonlinear flow. -/
def weakStarActionPhaseFlow (r : ℝ) (Ω : (ℤ → ℝ) → ℤ → ℝ) (t : ℝ)
    (f : WeakDual ℂ (WeightedCoeff (Weight.sobolev r) 1)) :
    WeakDual ℂ (WeightedCoeff (Weight.sobolev r) 1) :=
  wienerDualRealization r
    (actionPhaseFlow (Weight.sobolev (-r)) Ω t (weakStarCoeff r f))

@[simp] theorem weakStarCoordinates_actionPhaseFlow (r : ℝ)
    (Ω : (ℤ → ℝ) → ℤ → ℝ) (t : ℝ)
    (f : WeakDual ℂ (WeightedCoeff (Weight.sobolev r) 1)) (n : ℤ) :
    weakStarCoordinates r (weakStarActionPhaseFlow r Ω t f) n =
      Complex.exp (((t * Ω (squaredAmplitudes (weakStarCoeff r f)) n : ℝ) : ℂ) * Complex.I) *
        weakStarCoordinates r f n := by
  simp only [weakStarActionPhaseFlow, weakStarCoordinates_wienerDualRealization,
    actionPhaseFlow_apply, weakStarCoeff_val]

/-- Uniform-in-time endpoint boundedness, with the original norm exactly. -/
@[simp] theorem norm_weakStarActionPhaseFlow (r : ℝ)
    (Ω : (ℤ → ℝ) → ℤ → ℝ) (t : ℝ)
    (f : WeakDual ℂ (WeightedCoeff (Weight.sobolev r) 1)) :
    ‖(weakStarActionPhaseFlow r Ω t f).toStrongDual‖ = ‖f.toStrongDual‖ := by
  simp only [weakStarActionPhaseFlow, norm_wienerDualRealization,
    norm_actionPhaseFlow, norm_weakStarCoeff]

@[simp] theorem weakStarActionPhaseFlow_zero (r : ℝ)
    (Ω : (ℤ → ℝ) → ℤ → ℝ)
    (f : WeakDual ℂ (WeightedCoeff (Weight.sobolev r) 1)) :
    weakStarActionPhaseFlow r Ω 0 f = f := by
  simp only [weakStarActionPhaseFlow, actionPhaseFlow_zero, wienerDualRealization_weakStarCoeff]

/-- Conservation of the amplitudes supplies the nonlinear group identity. -/
theorem weakStarActionPhaseFlow_add (r : ℝ)
    (Ω : (ℤ → ℝ) → ℤ → ℝ) (t u : ℝ)
    (f : WeakDual ℂ (WeightedCoeff (Weight.sobolev r) 1)) :
    weakStarActionPhaseFlow r Ω t (weakStarActionPhaseFlow r Ω u f) =
      weakStarActionPhaseFlow r Ω (t+u) f := by
  simp only [weakStarActionPhaseFlow, weakStarCoeff_wienerDualRealization, actionPhaseFlow_add]

/-- A bounded endpoint family is weak-star continuous precisely when all its
Fourier coefficients are continuous. The boundedness is global on the family. -/
theorem continuous_weakStar_of_bounded_coordinates (r : ℝ)
    {X : Type*} [TopologicalSpace X]
    (f : X → WeakDual ℂ (WeightedCoeff (Weight.sobolev r) 1))
    (hb : Bornology.IsBounded (range f))
    (hc : ∀ n : ℤ, Continuous (fun x => weakStarCoordinates r (f x) n)) :
    Continuous f := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply (tendsto_weakStar_iff_coordinates_of_bounded r f (f x) hb).mpr
  exact fun n => (hc n).continuousAt

/-- The nonlinear evolution of a bounded family stays bounded for all times. -/
theorem isBounded_weakStarActionPhaseFlow_family (r : ℝ)
    (Ω : (ℤ → ℝ) → ℤ → ℝ)
    {X : Type*} (f : X → WeakDual ℂ (WeightedCoeff (Weight.sobolev r) 1))
    (hb : Bornology.IsBounded (range f)) :
    Bornology.IsBounded (range (fun x : ℝ × X => weakStarActionPhaseFlow r Ω x.1 (f x.2))) := by
  rw [← WeakDual.isBounded_toWeakDual_preimage_iff_isBounded] at hb ⊢
  obtain ⟨M, hM⟩ := hb.exists_norm_le
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨M, ?_⟩
  intro F hF
  obtain ⟨x, hx⟩ := hF
  have he : F = (weakStarActionPhaseFlow r Ω x.1 (f x.2)).toStrongDual :=
    by simpa only [StrongDual.toStrongDual_toWeakDual] using
      congrArg (WeakDual.toStrongDual (𝕜 := ℂ)) hx.symm
  rw [he, norm_weakStarActionPhaseFlow]
  exact hM _ ⟨x.2, by simp⟩

/-- Joint endpoint continuity on a bounded family follows from continuity of
each realized frequency. No uniform bound over the frequency index is used. -/
theorem continuous_weakStarActionPhaseFlow_family (r : ℝ)
    (Ω : (ℤ → ℝ) → ℤ → ℝ)
    {X : Type*} [TopologicalSpace X]
    (f : X → WeakDual ℂ (WeightedCoeff (Weight.sobolev r) 1))
    (hb : Bornology.IsBounded (range f)) (hf : Continuous f)
    (hΩ : ∀ n : ℤ, Continuous (fun x => Ω (squaredAmplitudes (weakStarCoeff r (f x))) n)) :
    Continuous (fun x : ℝ × X => weakStarActionPhaseFlow r Ω x.1 (f x.2)) := by
  apply continuous_weakStar_of_bounded_coordinates r _
    (isBounded_weakStarActionPhaseFlow_family r Ω f hb)
  intro n
  simp only [weakStarCoordinates_actionPhaseFlow]
  exact (((Complex.continuous_ofReal.comp
    (continuous_fst.mul ((hΩ n).comp continuous_snd))).mul continuous_const).cexp).mul
      (((WeakDual.eval_continuous _).comp hf).comp continuous_snd)

/-- Every orbit is weak-star continuous, even with completely arbitrary Ω. -/
theorem continuous_weakStarActionPhaseFlow_orbit (r : ℝ)
    (Ω : (ℤ → ℝ) → ℤ → ℝ)
    (f : WeakDual ℂ (WeightedCoeff (Weight.sobolev r) 1)) :
    Continuous (fun t : ℝ => weakStarActionPhaseFlow r Ω t f) := by
  have hb : Bornology.IsBounded (range (fun _ : Unit => f)) := by simp
  have hc : Continuous (fun x : ℝ × Unit => weakStarActionPhaseFlow r Ω x.1 f) :=
    continuous_weakStarActionPhaseFlow_family r Ω (fun _ : Unit => f) hb
      continuous_const (fun _ => continuous_const)
  change Continuous ((fun x : ℝ × Unit => weakStarActionPhaseFlow r Ω x.1 f) ∘
    (fun t : ℝ => (t, ())))
  exact hc.comp (continuous_id.prodMk continuous_const)

/-- Compact-time trajectories carry the compact-open weak-star topology. -/
def weakStarActionPhaseTrajectory (r : ℝ) (Ω : (ℤ → ℝ) → ℤ → ℝ) (T : ℝ)
    (f : WeakDual ℂ (WeightedCoeff (Weight.sobolev r) 1)) :
    C(Icc (-T) T, WeakDual ℂ (WeightedCoeff (Weight.sobolev r) 1)) where
  toFun τ := weakStarActionPhaseFlow r Ω τ.val f
  continuous_toFun := (continuous_weakStarActionPhaseFlow_orbit r Ω f).comp continuous_subtype_val

/-- Continuous dependence in the actual compact-time trajectory topology. -/
theorem continuous_weakStarActionPhaseTrajectory_family (r : ℝ)
    (Ω : (ℤ → ℝ) → ℤ → ℝ) (T : ℝ)
    {X : Type*} [TopologicalSpace X]
    (f : X → WeakDual ℂ (WeightedCoeff (Weight.sobolev r) 1))
    (hb : Bornology.IsBounded (range f)) (hf : Continuous f)
    (hΩ : ∀ n : ℤ, Continuous (fun x => Ω (squaredAmplitudes (weakStarCoeff r (f x))) n)) :
    Continuous (fun x => weakStarActionPhaseTrajectory r Ω T (f x)) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun x : X × Icc (-T) T => weakStarActionPhaseFlow r Ω x.2.val (f x.1))
  have hi : Continuous (fun x : X × Icc (-T) T => (x.2.val, x.1)) :=
    (continuous_subtype_val.comp continuous_snd).prodMk continuous_fst
  have hc : Continuous (fun x : ℝ × X => weakStarActionPhaseFlow r Ω x.1 (f x.2)) :=
    continuous_weakStarActionPhaseFlow_family r Ω f hb hf hΩ
  change Continuous ((fun x : ℝ × X => weakStarActionPhaseFlow r Ω x.1 (f x.2)) ∘
    (fun x : X × Icc (-T) T => (x.2.val, x.1)))
  exact hc.comp hi

/-- Odd signed frequencies preserve the real, mean-zero endpoint locus. -/
theorem weakStarActionPhaseFlow_mem_realMeanZero (r : ℝ)
    (Ω : (ℤ → ℝ) → ℤ → ℝ)
    (hΩ : ∀ A n, Ω A (-n) = -Ω A n) (t : ℝ)
    (f : WeakDual ℂ (WeightedCoeff (Weight.sobolev r) 1))
    (hf : f ∈ realMeanZeroWeakStar r) :
    weakStarActionPhaseFlow r Ω t f ∈ realMeanZeroWeakStar r := by
  rcases hf with ⟨hf0, hfs⟩
  constructor
  · simp only [weakStarCoordinates_actionPhaseFlow, hf0, mul_zero]
  · intro n
    rw [weakStarCoordinates_actionPhaseFlow, weakStarCoordinates_actionPhaseFlow,
      hfs n, hΩ _ n]
    change Complex.exp (((t * -Ω (squaredAmplitudes (weakStarCoeff r f)) n : ℝ) : ℂ) * Complex.I) *
      (starRingEnd ℂ) (weakStarCoordinates r f n) =
      (starRingEnd ℂ) (Complex.exp (((t * Ω (squaredAmplitudes (weakStarCoeff r f)) n : ℝ) : ℂ) * Complex.I) *
        weakStarCoordinates r f n)
    rw [map_mul, ← Complex.exp_conj]
    congr 2
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring

/-- The actual orbit restricted to an invariant subset. -/
def weakStarInvariantActionTrajectory (r : ℝ) (Ω : (ℤ → ℝ) → ℤ → ℝ)
    (V : Set (WeakDual ℂ (WeightedCoeff (Weight.sobolev r) 1)))
    (hV : ∀ t f, f ∈ V → weakStarActionPhaseFlow r Ω t f ∈ V)
    (T : ℝ) (f : V) : C(Icc (-T) T, V) where
  toFun τ := ⟨weakStarActionPhaseFlow r Ω τ.val f.val, hV τ.val f.val f.property⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_weakStarActionPhaseFlow_orbit r Ω f.val).comp continuous_subtype_val

/-- Endpoint continuous dependence with the exact invariant-set trajectory
codomain of the article's Theorem 1.3. Physical KdV identification and
continuity of its realized frequencies are separate obligations. -/
theorem continuous_weakStarInvariantActionTrajectory (r : ℝ)
    (Ω : (ℤ → ℝ) → ℤ → ℝ)
    (V : Set (WeakDual ℂ (WeightedCoeff (Weight.sobolev r) 1)))
    (hV : ∀ t f, f ∈ V → weakStarActionPhaseFlow r Ω t f ∈ V)
    (hb : Bornology.IsBounded V)
    (hΩ : ∀ n : ℤ, Continuous (fun f : V => Ω (squaredAmplitudes (weakStarCoeff r f.val)) n))
    (T : ℝ) : Continuous (weakStarInvariantActionTrajectory r Ω V hV T) := by
  have hr : Bornology.IsBounded (range (Subtype.val : V → _)) := by
    simpa only [Subtype.range_coe] using hb
  have hc : Continuous (fun x : ℝ × V => weakStarActionPhaseFlow r Ω x.1 x.2.val) :=
    continuous_weakStarActionPhaseFlow_family r Ω Subtype.val hr continuous_subtype_val hΩ
  apply ContinuousMap.continuous_of_continuous_uncurry
  apply Continuous.subtype_mk
  change Continuous ((fun x : ℝ × V => weakStarActionPhaseFlow r Ω x.1 x.2.val) ∘
    (fun x : V × Icc (-T) T => (x.2.val, x.1)))
  have hi : Continuous (fun x : V × Icc (-T) T => (x.2.val, x.1)) :=
    (continuous_subtype_val.comp continuous_snd).prodMk continuous_fst
  exact hc.comp hi

end NLS.WeightedCoeff
