import NLS.ZakharovShabat.L2PeriodicFundamental
import NLS.ZakharovShabat.L2FundamentalInitialValue

/-! # The original equation for the periodic physical L2 continuation

Each continued column is the actual unit-interval initial-value solution
on every closed period. Translation gives the signed differential equation
almost everywhere on the full nonnegative time domain.
-/
noncomputable section
open Set Complex MeasureTheory Filter Topology
open NLS.LinearVolterra
open scoped Matrix.Norms.Elementwise
namespace NLS.ZakharovShabat

/-- The period-one extension of an original physical L2 representative. -/
def periodicL2Representative (u : IntervalPairL2) (x : ℝ) : ℂ × ℂ :=
  intervalL2Representative u (Int.fract x)

theorem periodic_periodicL2Representative (u : IntervalPairL2) :
    Function.Periodic (periodicL2Representative u) 1 := by
  intro x
  simp [periodicL2Representative,Int.fract_add_one]

theorem periodicL2Representative_on_period (u : IntervalPairL2) (n : ℕ)
    (x : ℝ) (hx : x ∈ Ico (n : ℝ) ((n : ℝ)+1)) :
    periodicL2Representative u x = intervalL2Representative u (x-n) := by
  have h0 : 0 ≤ x := (Nat.cast_nonneg n).trans hx.1
  simp only [periodicL2Representative,Int.fract,← natCast_floor_eq_intCast_floor h0,
    Nat.floor_eq_on_Ico n x hx]

/-- Periodic extension preserves the original physical class on its defining interval. -/
theorem periodicL2Representative_eq_ae (u : IntervalPairL2) :
    periodicL2Representative u =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] intervalL2Representative u := by
  rw [Filter.EventuallyEq,ae_restrict_iff' measurableSet_Ioc]
  filter_upwards [volume.ae_ne (1 : ℝ)] with x hx hmem
  have h := periodicL2Representative_on_period u 0 x
    (by simpa only [Nat.cast_zero,zero_add] using
      (show x ∈ Ico (0 : ℝ) 1 from ⟨hmem.1.le,lt_of_le_of_ne hmem.2 hx⟩))
  simpa only [Nat.cast_zero,sub_zero] using h

/-- Any original square-integrable representative is recovered almost everywhere. -/
theorem periodicL2Representative_ofFunction (φ : ℝ → ℂ × ℂ)
    (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1))) :
    periodicL2Representative (intervalL2OfFunction φ hφ) =ᵐ[volume.restrict (Ioc 0 1)] φ :=
  (periodicL2Representative_eq_ae _).trans (intervalL2Representative_ofFunction φ hφ)

/-- Real-variable column, extended constantly to negative times solely to state derivatives. -/
def l2PeriodicColumn (u : IntervalPairL2) (z : ℂ) (j : Fin 2) (x : ℝ) : ℂ × ℂ :=
  let M := l2PeriodicFundamentalMatrix u z ⟨max x 0,by change 0 ≤ max x 0; exact le_max_right _ _⟩
  (M 0 j,M 1 j)

/-- On each closed period the continued column is exactly the original L2 solution. -/
theorem l2PeriodicColumn_on_period (u : IntervalPairL2) (z : ℂ) (j : Fin 2)
    (n : ℕ) (x : ℝ) (hx : x ∈ Icc (n : ℝ) ((n : ℝ)+1)) :
    l2PeriodicColumn u z j x =
      extend (l2SolutionCurve u z ((l2Monodromy u z ^ n) 0 j,(l2Monodromy u z ^ n) 1 j)) (x-n) := by
  have h0 : 0 ≤ x := (Nat.cast_nonneg n).trans hx.1
  have hr : x-(n : ℝ) ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [hx.1,hx.2]
  unfold l2PeriodicColumn
  simp only [max_eq_left h0]
  rw [l2PeriodicFundamentalMatrix_on_period _ _ n _ hx]
  rw [l2FundamentalMatrix_mul_column]
  exact (extend_coe _ ⟨x-n,hr⟩).symm

/-- The actual Volterra equation on every closed period, with the previous endpoint as initial data. -/
theorem l2PeriodicColumn_integral_on_period (u : IntervalPairL2) (z : ℂ) (j : Fin 2)
    (n : ℕ) (s : Icc (0 : ℝ) 1) :
    l2PeriodicColumn u z j (n+s.val) = l2PeriodicColumn u z j n+
      ∫ r in (0 : ℝ)..s.val,
        classicalODECoefficient (intervalL2Representative u r) z (l2PeriodicColumn u z j (n+r)) := by
  let v := ((l2Monodromy u z ^ n) 0 j,(l2Monodromy u z ^ n) 1 j)
  have he (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) :
      l2PeriodicColumn u z j (n+r) = extend (l2SolutionCurve u z v) r := by
    have h := l2PeriodicColumn_on_period u z j n (n+r) (by constructor <;> linarith [hr.1,hr.2])
    simpa [v] using h
  have h0 : l2PeriodicColumn u z j n = extend (l2SolutionCurve u z v) 0 := by
    simpa only [add_zero] using he 0 (by simp)
  have hz : extend (l2SolutionCurve u z v) 0 = v := by
    have h := extend_coe (l2SolutionCurve u z v) ⟨0,by constructor <;> norm_num⟩
    simpa only [l2SolutionCurve_zero] using h
  rw [he s.val s.property,h0,hz,extend_coe _ s,l2SolutionCurve_eq_integral]
  congr 1
  apply intervalIntegral.integral_congr
  intro r hr
  have hr' : r ∈ Icc (0 : ℝ) 1 := by
    rw [uIcc_of_le s.property.1] at hr
    exact ⟨hr.1,hr.2.trans s.property.2⟩
  dsimp only
  rw [he r hr']

/-- The continued column satisfies the original signed system on the interior of each period. -/
theorem ae_hasDerivAt_l2PeriodicColumn_on_period (u : IntervalPairL2) (z : ℂ)
    (j : Fin 2) (n : ℕ) :
    ∀ᵐ x ∂volume.restrict (Ioo (n : ℝ) ((n : ℝ)+1)),
      HasDerivAt (l2PeriodicColumn u z j)
        (classicalODECoefficient (periodicL2Representative u x) z (l2PeriodicColumn u z j x)) x := by
  let v := ((l2Monodromy u z ^ n) 0 j,(l2Monodromy u z ^ n) 1 j)
  have hu := (ae_restrict_iff' measurableSet_Ioc).mp (ae_hasDerivAt_l2SolutionCurve u z v)
  have hs := (measurePreserving_sub_right volume (n : ℝ)).quasiMeasurePreserving.ae hu
  rw [ae_restrict_iff' measurableSet_Ioo]
  filter_upwards [hs] with x hx hmem
  have hunit : x-(n : ℝ) ∈ Ioc (0 : ℝ) 1 := by constructor <;> linarith [hmem.1,hmem.2]
  have hd := (hx hunit).comp_sub_const x (n : ℝ)
  have he : (fun r => extend (l2SolutionCurve u z v) (r-n)) =ᶠ[𝓝 x] l2PeriodicColumn u z j := by
    filter_upwards [Ioo_mem_nhds hmem.1 hmem.2] with r hr
    exact (l2PeriodicColumn_on_period u z j n r (Ioo_subset_Icc_self hr)).symm
  have hd' := hd.congr_of_eventuallyEq he.symm
  rw [periodicL2Representative_on_period u n x (Ioo_subset_Ico_self hmem),
    l2PeriodicColumn_on_period u z j n x (Ioo_subset_Icc_self hmem)]
  exact hd'

/-- The original differential equation holds almost everywhere for all positive times. -/
theorem ae_hasDerivAt_l2PeriodicColumn (u : IntervalPairL2) (z : ℂ) (j : Fin 2) :
    ∀ᵐ x ∂volume.restrict (Ioi (0 : ℝ)),
      HasDerivAt (l2PeriodicColumn u z j)
        (classicalODECoefficient (periodicL2Representative u x) z (l2PeriodicColumn u z j x)) x := by
  have hall := ae_all_iff.mpr (fun n : ℕ => (ae_restrict_iff' measurableSet_Ioo).mp
    (ae_hasDerivAt_l2PeriodicColumn_on_period u z j n))
  have hne : ∀ᵐ x : ℝ ∂volume, ∀ n : ℕ, x ≠ (n : ℝ) :=
    ae_all_iff.mpr (fun n => volume.ae_ne (n : ℝ))
  rw [ae_restrict_iff' measurableSet_Ioi]
  filter_upwards [hall,hne] with x hx hn hpos
  exact hx ⌊x⌋₊ ⟨lt_of_le_of_ne (Nat.floor_le hpos.le) (hn _).symm,Nat.lt_floor_add_one x⟩

/-- The original physical Zakharov-Shabat operator equals z times each continued column. -/
theorem ae_physicalOperator_l2PeriodicColumn (u : IntervalPairL2) (z : ℂ) (j : Fin 2) :
    physicalOperator (periodicL2Representative u) (l2PeriodicColumn u z j)
      =ᵐ[volume.restrict (Ioi (0 : ℝ))] (fun x => z • l2PeriodicColumn u z j x) := by
  filter_upwards [ae_hasDerivAt_l2PeriodicColumn u z j] with x hx
  simp only [physicalOperator,(HasFDerivAt.hasDerivAt hx.fst).deriv,
    (HasFDerivAt.hasDerivAt hx.snd).deriv,classicalODECoefficient_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.toSpanSingleton_apply,one_smul]
  apply Prod.ext <;> dsimp <;> ring_nf <;> simp [I_sq]

/-- Every original period-one square-integrable potential agrees with the continued representative. -/
theorem periodicL2Representative_ofFunction_periodic (φ : ℝ → ℂ × ℂ)
    (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1))) (hper : Function.Periodic φ 1) :
    periodicL2Representative (intervalL2OfFunction φ hφ) =ᵐ[volume.restrict (Ioi (0 : ℝ))] φ := by
  have hu := (ae_restrict_iff' measurableSet_Ioc).mp (intervalL2Representative_ofFunction φ hφ)
  have hall := ae_all_iff.mpr (fun n : ℕ =>
    (measurePreserving_sub_right volume (n : ℝ)).quasiMeasurePreserving.ae hu)
  have hne : ∀ᵐ x : ℝ ∂volume, ∀ n : ℕ, x ≠ (n : ℝ) :=
    ae_all_iff.mpr (fun n => volume.ae_ne (n : ℝ))
  rw [Filter.EventuallyEq,ae_restrict_iff' measurableSet_Ioi]
  filter_upwards [hall,hne] with x hx hn hpos
  have hm : x ∈ Ico (⌊x⌋₊ : ℝ) ((⌊x⌋₊ : ℝ)+1) := ⟨Nat.floor_le hpos.le,Nat.lt_floor_add_one x⟩
  have hs : x-(⌊x⌋₊ : ℝ) ∈ Ioc (0 : ℝ) 1 := by
    have hl := lt_of_le_of_ne hm.1 (hn _).symm
    constructor <;> linarith [hm.2]
  rw [periodicL2Representative_on_period _ ⌊x⌋₊ x hm,hx ⌊x⌋₊ hs]
  have hp := hper.nat_mul ⌊x⌋₊ (x-(⌊x⌋₊ : ℝ))
  simpa using hp.symm

/-- The full-time spectral equation uses any original period-one physical L2 representative. -/
theorem ae_physicalOperator_l2PeriodicColumn_ofFunction (φ : ℝ → ℂ × ℂ)
    (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1))) (hper : Function.Periodic φ 1)
    (z : ℂ) (j : Fin 2) :
    physicalOperator φ (l2PeriodicColumn (intervalL2OfFunction φ hφ) z j)
      =ᵐ[volume.restrict (Ioi (0 : ℝ))]
        (fun x => z • l2PeriodicColumn (intervalL2OfFunction φ hφ) z j x) := by
  filter_upwards [ae_physicalOperator_l2PeriodicColumn (intervalL2OfFunction φ hφ) z j,
    periodicL2Representative_ofFunction_periodic φ hφ hper] with x hx hφx
  simpa only [physicalOperator,hφx] using hx

end NLS.ZakharovShabat
