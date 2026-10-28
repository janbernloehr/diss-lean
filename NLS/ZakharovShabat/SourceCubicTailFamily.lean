import NLS.ZakharovShabat.ResonantCubicFourthTail
import NLS.ZakharovShabat.ResonantTwoModeCubic
import NLS.ZakharovShabat.SourceRealTypeConvex

/-! # A small original period-two family for the cubic tail estimates

The first component has physical Fourier modes 0, -n and -2n, and the
second has modes 0, n and 2n. The first two amplitudes are s; the resonant
amplitude is s^3/(pi*n)^2. This real-type family enters every open
neighborhood of zero. Its actual full-strip fourth-power error tail,
after subtraction of its own cubic term, is o(s^12).

These estimates do not identify the perturbed cubic term with that of the
two-mode background and do not establish spectral-gap asymptotics or the
final weighted gap-sum assertion on dissertation p.44.
-/
noncomputable section
open scoped ENNReal ComplexConjugate
namespace NLS.ZakharovShabat
local instance cubicTailFamilyFact : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩

/-- The coefficient scale for the resonant mode. -/
def sourceCubicTailScale (n : ℤ) : ℝ := 1/(Real.pi*(n : ℝ))^2

/-- The three-mode family in unit-weight coordinates. -/
def weightedCubicTailFamily (n : ℤ) (s : ℝ) : WeightedCoeffPair SpectralWeight.one.toWeight 4 :=
  (s : ℂ) • twoModeResonantPotential SpectralWeight.one n 1 +
    ((s^3 : ℝ) : ℂ) • singleResonantPotential SpectralWeight.one n (sourceCubicTailScale n) (sourceCubicTailScale n)

/-- The same family in the original period-two coefficient space. -/
def sourceCubicTailFamily (n : ℤ) (s : ℝ) : CoeffPair 4 := unitWeightedPairEquiv.symm (weightedCubicTailFamily n s)

/-- The unit-weight equivalence recovers the specified weighted family. -/
theorem unitWeightedPairEquiv_sourceCubicTailFamily (n : ℤ) (s : ℝ) :
    unitWeightedPairEquiv (sourceCubicTailFamily n s) = weightedCubicTailFamily n s :=
  LinearIsometryEquiv.apply_symm_apply _ _

/-- The three physical Fourier modes in the first weighted component. -/
theorem weightedCubicTailFamily_fst (n : ℤ) (hn : 0 < n) (s : ℝ) (k : ℤ) :
    (weightedCubicTailFamily n s).fst.val k =
      (if k=0 ∨ k= -n then (s : ℂ) else 0) +
      (if k= -(2*n) then ((s^3*sourceCubicTailScale n : ℝ) : ℂ) else 0) := by
  change (s : ℂ)*(twoModeResonantPotential (p := 4) SpectralWeight.one n 1).fst.val k +
    ((s^3 : ℝ) : ℂ)*(singleResonantPotential (p := 4) SpectralWeight.one n (sourceCubicTailScale n) (sourceCubicTailScale n)).fst.val k = _
  rw [twoModeResonantPotential_fst _ _ hn,singleResonantPotential_fst]
  simp only [mul_ite,mul_one,mul_zero,Complex.ofReal_mul]

/-- The three physical Fourier modes in the second weighted component. -/
theorem weightedCubicTailFamily_snd (n : ℤ) (hn : 0 < n) (s : ℝ) (k : ℤ) :
    (weightedCubicTailFamily n s).snd.val k =
      (if k=0 ∨ k=n then (s : ℂ) else 0) +
      (if k=2*n then ((s^3*sourceCubicTailScale n : ℝ) : ℂ) else 0) := by
  change (s : ℂ)*(twoModeResonantPotential (p := 4) SpectralWeight.one n 1).snd.val k +
    ((s^3 : ℝ) : ℂ)*(singleResonantPotential (p := 4) SpectralWeight.one n (sourceCubicTailScale n) (sourceCubicTailScale n)).snd.val k = _
  rw [twoModeResonantPotential_snd _ _ hn,singleResonantPotential_snd]
  simp only [mul_ite,mul_one,mul_zero,Complex.ofReal_mul]

/-- The first original component has the reflected physical modes. -/
theorem sourceCubicTailFamily_fst (n : ℤ) (hn : 0 < n) (s : ℝ) (k : ℤ) :
    (sourceCubicTailFamily n s).fst k = (if k=0 ∨ k= -n then (s : ℂ) else 0) +
      (if k= -(2*n) then ((s^3*sourceCubicTailScale n : ℝ) : ℂ) else 0) := by
  rw [← unitWeightedPairEquiv_fst,unitWeightedPairEquiv_sourceCubicTailFamily,weightedCubicTailFamily_fst n hn]

/-- The second original component has the positive physical modes. -/
theorem sourceCubicTailFamily_snd (n : ℤ) (hn : 0 < n) (s : ℝ) (k : ℤ) :
    (sourceCubicTailFamily n s).snd k = (if k=0 ∨ k=n then (s : ℂ) else 0) +
      (if k=2*n then ((s^3*sourceCubicTailScale n : ℝ) : ℂ) else 0) := by
  rw [← unitWeightedPairEquiv_snd,unitWeightedPairEquiv_sourceCubicTailFamily,weightedCubicTailFamily_snd n hn]

/-- Every real amplitude gives a real-type original potential. -/
theorem sourceCubicTailFamily_realType (n : ℤ) (hn : 0 < n) (s : ℝ) :
    IsRealType (CoeffPair.toMax 4 (sourceCubicTailFamily n s)) := by
  intro k
  change (sourceCubicTailFamily n s).snd k = conj ((sourceCubicTailFamily n s).fst (-k))
  rw [sourceCubicTailFamily_fst n hn,sourceCubicTailFamily_snd n hn]
  simp only [map_add,neg_eq_zero,neg_inj]
  split_ifs <;> simp_all

/-- A fixed norm bound for the two coefficient profiles. -/
def sourceCubicTailNormBound (n : ℤ) : ℝ :=
  ‖twoModeResonantPotential (p := 4) SpectralWeight.one n 1‖ +
    ‖singleResonantPotential (p := 4) SpectralWeight.one n (sourceCubicTailScale n) (sourceCubicTailScale n)‖

/-- The weighted family has a linear norm bound for amplitudes in [0,1]. -/
theorem weightedCubicTailFamily_norm_le (n : ℤ) (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    ‖weightedCubicTailFamily n s‖ ≤ sourceCubicTailNormBound n*s := by
  have hpow : s^3 ≤ s := by nlinarith [mul_nonneg hs (sub_nonneg.mpr hs1)]
  apply (norm_add_le _ _).trans
  simp only [norm_smul,Complex.norm_real,Real.norm_of_nonneg hs,
    Real.norm_of_nonneg (pow_nonneg hs 3)]
  dsimp [sourceCubicTailNormBound]
  nlinarith [norm_nonneg (singleResonantPotential (p := 4) SpectralWeight.one n (sourceCubicTailScale n) (sourceCubicTailScale n))]

/-- The original family has the same linear norm bound. -/
theorem sourceCubicTailFamily_norm_le (n : ℤ) (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    ‖sourceCubicTailFamily n s‖ ≤ sourceCubicTailNormBound n*s := by
  simpa only [sourceCubicTailFamily,LinearIsometryEquiv.norm_map] using weightedCubicTailFamily_norm_le n s hs hs1

open Filter Topology in
/-- Small positive amplitudes satisfy the global half-contraction bound. -/
theorem weightedCubicTailFamily_eventually_controlled (n : ℤ) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ),
      2*weightedDoubleConstant (p := 4) (by simp)*‖weightedCubicTailFamily n s‖^2 ≤ 1/2 ∧
      ‖weightedCubicTailFamily n s‖ ≤ sourceCubicTailNormBound n*s := by
  have hc : Continuous (weightedCubicTailFamily n) := by unfold weightedCubicTailFamily; fun_prop
  have ht : Tendsto (fun s : ℝ => 2*weightedDoubleConstant (p := 4) (by simp)*‖weightedCubicTailFamily n s‖^2)
      (𝓝 0) (𝓝 0) := by
    simpa [weightedCubicTailFamily,Pi.mul_apply,Pi.pow_apply] using
      (show Continuous (fun s : ℝ => 2*weightedDoubleConstant (p := 4) (by simp)*‖weightedCubicTailFamily n s‖^2) from
        continuous_const.mul (hc.norm.pow 2)).tendsto 0
  have hsmall : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      2*weightedDoubleConstant (p := 4) (by simp)*‖weightedCubicTailFamily n s‖^2 < 1/2 :=
    (ht.mono_left nhdsWithin_le_nhds).eventually
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1/2))
  have hs1 : ∀ᶠ s in 𝓝[>] (0 : ℝ), s < 1 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hsmall,hs1,self_mem_nhdsWithin] with s hsmall hs1 hs
  exact ⟨hsmall.le,weightedCubicTailFamily_norm_le n s hs.le hs1.le⟩

open Filter Topology in
/-- The actual infinite fourth-power error tail is o(s^12), at every cutoff N>=1. -/
theorem sourceCubicTailFamily_normalized_tail_tendsto (n : ℤ) (N : ℕ) (hN : 0 < N) (positive : Bool) :
    Tendsto (fun s => resonantCubicFourthErrorSum SpectralWeight.one
      (unitWeightedPairEquiv (sourceCubicTailFamily n s)) N positive/s^12) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  simpa only [unitWeightedPairEquiv_sourceCubicTailFamily] using resonantCubicFourthErrorSum_normalized_tendsto
    SpectralWeight.one (weightedCubicTailFamily n) N hN positive (sourceCubicTailNormBound n)
      (weightedCubicTailFamily_eventually_controlled n)

/-- The original family depends continuously on its real amplitude. -/
theorem sourceCubicTailFamily_continuous (n : ℤ) : Continuous (sourceCubicTailFamily n) := by
  unfold sourceCubicTailFamily weightedCubicTailFamily
  fun_prop

/-- Zero amplitude gives the zero original potential. -/
@[simp] theorem sourceCubicTailFamily_zero (n : ℤ) : sourceCubicTailFamily n 0 = 0 := by
  simp [sourceCubicTailFamily,weightedCubicTailFamily]

open Filter Topology in
/-- The family eventually enters any original open neighborhood of zero. -/
theorem sourceCubicTailFamily_eventually_mem (n : ℤ) (U : Set (CoeffPair 4)) (ho : IsOpen U) (h0 : 0 ∈ U) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), sourceCubicTailFamily n s ∈ U := by
  have ht : Tendsto (sourceCubicTailFamily n) (𝓝[>] (0 : ℝ)) (𝓝 (0 : CoeffPair 4)) := by
    simpa only [sourceCubicTailFamily_zero] using (sourceCubicTailFamily_continuous n).continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ))
  exact ht.eventually (ho.mem_nhds h0)

end NLS.ZakharovShabat
