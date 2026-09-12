import NLS.Fourier.PhysicalIntervalL2

/-!
# The intrinsic interval Sobolev normed space

The underlying elements are actual almost-everywhere `L²` classes with finite
fractional difference energy. The graph embedding into two `L²` spaces gives
the exact physical norm, including at half regularity. No endpoint condition
is imposed. The usual fractional Sobolev interpretation is `0<s<1`; at zero,
the graph energy includes an extra term and is not the ordinary `L²` norm.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace NLS.Fourier

/-- The finite-energy subspace of the normalized interval `L²` quotient. -/
def intrinsicIntervalSubmodule (s L : ℝ) [Fact (0 < L)] : Submodule ℂ CircleL2 where
  carrier := {f | MemLp (fractionalDifferenceQuotient s (intervalPullback L f)) 2 (intervalProductMeasure L)}
  zero_mem' := by
    have h := fractionalDifferenceQuotient_congr (s := s) (intervalPullback_zero (Fact.out : 0 < L))
    rw [fractionalDifferenceQuotient_zero] at h
    exact (memLp_congr_ae h).mpr (MemLp.zero)
  add_mem' := by
    intro f g hf hg
    have h := fractionalDifferenceQuotient_congr (s := s) (intervalPullback_add (Fact.out : 0 < L) f g)
    rw [fractionalDifferenceQuotient_add] at h
    exact (memLp_congr_ae h).mpr (hf.add hg)
  smul_mem' := by
    intro c f hf
    have h := fractionalDifferenceQuotient_congr (s := s) (intervalPullback_smul (Fact.out : 0 < L) c f)
    rw [fractionalDifferenceQuotient_smul] at h
    exact (memLp_congr_ae h).mpr (hf.const_smul c)

/-- Intrinsic fractional Sobolev interval data, modulo almost-everywhere equality. -/
def IntrinsicIntervalSobolev (s L : ℝ) [Fact (0 < L)] := ↥(intrinsicIntervalSubmodule s L)

namespace IntrinsicIntervalSobolev
variable {s L : ℝ} [Fact (0 < L)]

instance : AddCommGroup (IntrinsicIntervalSobolev s L) :=
  inferInstanceAs (AddCommGroup ↥(intrinsicIntervalSubmodule s L))
instance : Module ℂ (IntrinsicIntervalSobolev s L) :=
  inferInstanceAs (Module ℂ ↥(intrinsicIntervalSubmodule s L))

/-- Forgetting the finite-energy condition is an injective linear map. -/
def toL2 : IntrinsicIntervalSobolev s L →ₗ[ℂ] CircleL2 := (intrinsicIntervalSubmodule s L).subtype

@[simp] theorem toL2_apply (f : IntrinsicIntervalSobolev s L) : toL2 f = f.val := rfl

theorem energy_lt_top (f : IntrinsicIntervalSobolev s L) :
    fractionalIntervalEnergy s L (intervalPullback L f.val) < ⊤ :=
  (memLp_fractionalDifferenceQuotient_iff s L _ (measurable_intervalPullback L f.val)).mp f.property

/-- The second component of the graph is the actual `L²` difference quotient. -/
def quotient : IntrinsicIntervalSobolev s L →ₗ[ℂ] Lp ℂ 2 (intervalProductMeasure L) where
  toFun f := f.property.toLp (fractionalDifferenceQuotient s (intervalPullback L f.val))
  map_add' f g := by
    apply Lp.ext
    have h := fractionalDifferenceQuotient_congr (s := s) (intervalPullback_add (Fact.out : 0 < L) f.val g.val)
    rw [fractionalDifferenceQuotient_add] at h
    filter_upwards [(f + g).property.coeFn_toLp, f.property.coeFn_toLp, g.property.coeFn_toLp,
      Lp.coeFn_add (f.property.toLp _) (g.property.toLp _), h] with p hp hf hg ha hh
    simpa only [hp, ha, Pi.add_apply, hf, hg] using! hh
  map_smul' c f := by
    apply Lp.ext
    have h := fractionalDifferenceQuotient_congr (s := s) (intervalPullback_smul (Fact.out : 0 < L) c f.val)
    rw [fractionalDifferenceQuotient_smul] at h
    filter_upwards [(c • f).property.coeFn_toLp, f.property.coeFn_toLp,
      Lp.coeFn_smul c (f.property.toLp _), h] with p hp hf ha hh
    simpa only [RingHom.id_apply, hp, ha, Pi.smul_apply, hf] using! hh

/-- The first component is scaled to the unnormalized physical interval measure. -/
def graph : IntrinsicIntervalSobolev s L →ₗ[ℂ]
    WithLp 2 (CircleL2 × Lp ℂ 2 (intervalProductMeasure L)) where
  toFun f := WithLp.toLp 2 ((Real.sqrt L : ℂ) • f.val, quotient f)
  map_add' f g := by
    change WithLp.toLp 2 ((Real.sqrt L : ℂ) • (f.val + g.val), quotient (f + g)) = _
    simp only [smul_add, map_add]
    rfl
  map_smul' c f := by
    change WithLp.toLp 2 ((Real.sqrt L : ℂ) • (c • f.val), quotient (c • f)) = _
    rw [smul_comm, map_smul]
    rfl

theorem graph_injective : Function.Injective (graph (s := s) (L := L)) := by
  intro f g h
  have he := congrArg (fun x => x.fst) h
  change (Real.sqrt L : ℂ) • f.val = (Real.sqrt L : ℂ) • g.val at he
  apply Subtype.ext
  exact (smul_right_injective _ (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (Fact.out : 0 < L)).ne')) he

instance : NormedAddCommGroup (IntrinsicIntervalSobolev s L) :=
  NormedAddCommGroup.induced _ _ graph graph_injective
instance : NormedSpace ℂ (IntrinsicIntervalSobolev s L) :=
  NormedSpace.induced ℂ _ _ graph

/-- The intrinsic norm is the norm of the actual physical graph. -/
theorem norm_eq_graph (f : IntrinsicIntervalSobolev s L) : ‖f‖ = ‖graph f‖ := rfl

/-- Exact squared graph norm, with the physical interval-length normalization. -/
theorem norm_sq (f : IntrinsicIntervalSobolev s L) :
    ‖f‖ ^ 2 = L * ‖f.val‖ ^ 2 + ‖quotient f‖ ^ 2 := by
  rw [norm_eq_graph, WithLp.prod_norm_sq_eq_of_L2]
  change ‖(Real.sqrt L : ℂ) • f.val‖ ^ 2 + ‖quotient f‖ ^ 2 = _
  rw [norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (le_of_lt (Fact.out : 0 < L))]

/-- The norm square is exactly the sum of the physical square and difference energies. -/
theorem ofReal_norm_sq (f : IntrinsicIntervalSobolev s L) :
    ENNReal.ofReal (‖f‖ ^ 2) = intrinsicIntervalEnergy s L (intervalPullback L f.val) := by
  have hL : 0 < L := Fact.out
  rw [norm_sq, ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_mul (le_of_lt (Fact.out : 0 < L)), intrinsicIntervalEnergy,
    intervalSquareEnergy_intervalPullback (Fact.out : 0 < L)]
  congr 1
  exact ofReal_norm_sq_fractionalDifferenceQuotient_toLp s L _
    (measurable_intervalPullback L f.val) f.property

/-- This norm agrees with the intrinsic size previously used for A.9 estimates. -/
theorem norm_eq_size (f : IntrinsicIntervalSobolev s L) :
    ‖f‖ = intrinsicIntervalSize s L (intervalPullback L f.val) := by
  rw [intrinsicIntervalSize, ← ofReal_norm_sq, ENNReal.toReal_ofReal (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

/-- The difference quotient is controlled by the intrinsic norm. -/
theorem norm_quotient_le (f : IntrinsicIntervalSobolev s L) : ‖quotient f‖ ≤ ‖f‖ := by
  have hL : 0 < L := Fact.out
  have h := norm_sq f
  nlinarith [sq_nonneg ‖f.val‖, norm_nonneg f, norm_nonneg (quotient f)]

/-- Physical `L²` inclusion retains its exact interval-length factor. -/
theorem norm_toL2_le (f : IntrinsicIntervalSobolev s L) :
    ‖f.val‖ ≤ (Real.sqrt L)⁻¹ * ‖f‖ := by
  have hL : 0 < L := Fact.out
  have h := norm_sq f
  have hb : Real.sqrt L * ‖f.val‖ ≤ ‖f‖ := by
    have hs := Real.sq_sqrt hL.le
    have hn := norm_nonneg f
    have hq := sq_nonneg ‖quotient f‖
    have hp : 0 ≤ Real.sqrt L * ‖f.val‖ := by positivity
    nlinarith [sq_nonneg (Real.sqrt L * ‖f.val‖ - ‖f‖)]
  exact (le_inv_mul_iff₀ (Real.sqrt_pos.mpr hL)).mpr hb

/-- Continuous inclusion into the underlying normalized `L²` space. -/
def toL2Continuous : IntrinsicIntervalSobolev s L →L[ℂ] CircleL2 :=
  toL2.mkContinuous (Real.sqrt L)⁻¹ norm_toL2_le

/-- Continuous physical difference-quotient operator. -/
def quotientContinuous : IntrinsicIntervalSobolev s L →L[ℂ] Lp ℂ 2 (intervalProductMeasure L) :=
  quotient.mkContinuous 1 (fun f => by simpa only [one_mul] using norm_quotient_le f)

/-- Every square-integrable original interval function with finite intrinsic energy defines a class. -/
def ofFunction (f : ℝ → ℂ) (hf : MemLp f 2 (volume.restrict (Ioc 0 L)))
    (hE : fractionalIntervalEnergy s L f < ⊤) : IntrinsicIntervalSobolev s L :=
  ⟨intervalL2Class (Fact.out : 0 < L) f hf, by
    apply (memLp_fractionalDifferenceQuotient_iff s L _ (measurable_intervalPullback L _)).mpr
    rw [fractionalIntervalEnergy_congr (intervalPullback_intervalL2Class (Fact.out : 0 < L) f hf)]
    exact hE⟩

theorem ofFunction_reconstruct (f : ℝ → ℂ) (hf : MemLp f 2 (volume.restrict (Ioc 0 L)))
    (hE : fractionalIntervalEnergy s L f < ⊤) :
    intervalPullback L (ofFunction f hf hE).val =ᵐ[volume.restrict (Ioo 0 L)] f :=
  intervalPullback_intervalL2Class (Fact.out : 0 < L) f hf

theorem norm_ofFunction (f : ℝ → ℂ) (hf : MemLp f 2 (volume.restrict (Ioc 0 L)))
    (hE : fractionalIntervalEnergy s L f < ⊤) :
    ‖ofFunction f hf hE‖ = intrinsicIntervalSize s L f := by
  rw [norm_eq_size, intrinsicIntervalSize,
    intrinsicIntervalEnergy_congr (ofFunction_reconstruct f hf hE)]
  rfl

/-- Equality of intrinsic classes is exactly equality of the original interval data almost everywhere. -/
theorem ofFunction_eq_iff (f g : ℝ → ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 L))) (hg : MemLp g 2 (volume.restrict (Ioc 0 L)))
    (hEf : fractionalIntervalEnergy s L f < ⊤) (hEg : fractionalIntervalEnergy s L g < ⊤) :
    ofFunction f hf hEf = ofFunction g hg hEg ↔ f =ᵐ[volume.restrict (Ioo 0 L)] g := by
  constructor
  · intro he
    exact (ofFunction_reconstruct f hf hEf).symm.trans
      (he ▸ ofFunction_reconstruct g hg hEg)
  · intro he
    apply Subtype.ext
    exact intervalL2Class_congr (Fact.out : 0 < L) f g hf hg he

@[simp] theorem ofFunction_pullback (f : IntrinsicIntervalSobolev s L) :
    ofFunction (intervalPullback L f.val) (memLp_intervalPullback (Fact.out : 0 < L) f.val) f.energy_lt_top = f := by
  apply Subtype.ext
  exact intervalL2Class_intervalPullback (Fact.out : 0 < L) f.val

end IntrinsicIntervalSobolev
end NLS.Fourier
