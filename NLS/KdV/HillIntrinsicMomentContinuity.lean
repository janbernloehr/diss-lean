import NLS.KdV.HillIntrinsicFrequencyMoments
import NLS.KdV.HillMovingContourSourceNeighborhood
import NLS.KdV.HillGlobalDifferentialContinuity
import NLS.ComplexAnalysis.CompactFiberIntegralContinuity
import NLS.ComplexAnalysis.NonrealCircleIntegralVectorComparison

/-! # Continuity of the actual intrinsic moments at every original real source

A genuine local continued logarithm controls each complete moving contour.
Its nonreal physical matching identifies the actual circle integral, including
closed own or integration gaps. No moment-continuity premise is assumed.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
namespace NLS.KdV

private theorem continuous_recentered_moment_section {A : Type*} [TopologicalSpace A]
    (q : RealPeriodOneHillPotential) (p : A → RealPeriodOneHillPotential) (hp : Continuous p)
    (Z : A × Icc (0 : ℝ) (2*Real.pi) → ℂ) (hZ : Continuous Z) (n k : ℕ+) (m : ℕ)
    (hD : ∀ t, (Z t,SpectralWeight.one.toCoeff (p t.1).val-SpectralWeight.one.toCoeff q.val)∈
      hillRecenteredContinuationDomain q.val q.property.1 q.property.2)
    (hcut : ∀ t, (Z t,p t.1)∈hillRealCutFamilyDomain) :
    Continuous (fun t =>
      (hillRecenteredPrimitive q.val q.property.1 q.property.2
        (Z t,SpectralWeight.one.toCoeff (p t.1).val-SpectralWeight.one.toCoeff q.val)+I*(k : ℂ)*Real.pi)^m*
          (hillAbelianSelectedGlobalPsi (p t.1).val (p t.1).property.1 (p t.1).property.2 n n.pos (Z t)/
            hillEnergyCanonicalRootProduct (p t.1).val (p t.1).property.1 (p t.1).property.2 (Z t))) := by
  have h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0 := by
    rw [map_zero]
    exact (Coeff.paritySubspace 0).zero_mem
  have h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)) := by
    rw [map_zero]
    intro j
    simp
  let K := Icc (0 : ℝ) (2*Real.pi)
  have hP : Continuous (fun x : A => SpectralWeight.one.toCoeff (p x).val) :=
    SpectralWeight.one.toCoeff.continuous.comp (continuous_subtype_val.comp hp)
  have hF : Continuous (fun t : A × K => hillRecenteredPrimitive q.val q.property.1 q.property.2
      (Z t,SpectralWeight.one.toCoeff (p t.1).val-SpectralWeight.one.toCoeff q.val)) :=
    (analyticOnNhd_hillRecenteredPrimitive q.val q.property.1 q.property.2).continuousOn.comp_continuous
      (hZ.prodMk ((hP.comp continuous_fst).sub continuous_const)) hD
  have hJ : Continuous (fun t : A × K => (Z t,p t.1)) := hZ.prodMk (hp.comp continuous_fst)
  have hψ : Continuous (fun t : A × K =>
      hillAbelianSelectedGlobalPsi (p t.1).val (p t.1).property.1 (p t.1).property.2 n n.pos (Z t)) := by
    simpa only [Function.comp_def] using!
      (continuous_hillAbelianSelectedGlobalPsi_joint h0q h0r n n.pos).comp hJ
  have hroot : Continuous (fun t : A × K =>
      hillEnergyCanonicalRootProduct (p t.1).val (p t.1).property.1 (p t.1).property.2 (Z t)) :=
    continuousOn_hillEnergyCanonicalRootProduct_joint.comp_continuous hJ hcut
  have hne (t : A × K) : hillEnergyCanonicalRootProduct (p t.1).val (p t.1).property.1 (p t.1).property.2 (Z t)≠0 :=
    hillEnergyCanonicalRootProduct_ne_zero_on_realCutDomain (p t.1).val (p t.1).property.1 (p t.1).property.2 (Z t) (hcut t)
  exact ((hF.add continuous_const).pow m).mul (hψ.div hroot hne)

/-- Every actual original contour moment is continuous in the complete
real physical L2 source, through arbitrary closed gaps and branch endpoints. -/
theorem continuous_hillIntrinsicFrequencyMoment (n k : ℕ+) (m : ℕ) :
    Continuous (fun p : RealPeriodOneHillPotential =>
      hillIntrinsicFrequencyMoment p.val p.property.1 p.property.2 n n.pos k m) := by
  apply continuous_iff_continuousAt.mpr
  intro q
  obtain ⟨V,hV,hqV,hdom⟩ := exists_hillMovingIntrinsicContour_recentered_neighborhood q k k.pos
  let c : RealPeriodOneHillPotential → ℂ := fun p => hillRealGapCenter p.val p.property.1 p.property.2 k
  let R : RealPeriodOneHillPotential → ℝ := fun p => hillRealGapHalfLength p.val p.property.1 p.property.2 k+
    hillRealGapCollar p.val p.property.1 p.property.2 k
  have hc : Continuous c := Complex.continuous_ofReal.comp (continuous_hillRealGapCenter k)
  have hcollar : Continuous (fun p : RealPeriodOneHillPotential => hillRealGapCollar p.val p.property.1 p.property.2 k) := by
    unfold hillRealGapCollar
    exact (((continuous_hillRealLabels (2*k-1)).sub (continuous_hillRealLabels (2*k-2))).min
      ((continuous_hillRealLabels (2*k+1)).sub (continuous_hillRealLabels (2*k)))).div_const 4
  have hR : Continuous R := (continuous_hillRealGapHalfLength k).add hcollar
  let P : V → Coeff 2 := fun p => SpectralWeight.one.toCoeff p.val.val
  have hP : Continuous P := SpectralWeight.one.toCoeff.continuous.comp
    (continuous_subtype_val.comp continuous_subtype_val)
  let w : V → ℂ → ℂ := fun p z =>
    (hillRecenteredPrimitive q.val q.property.1 q.property.2 (z,P p-SpectralWeight.one.toCoeff q.val)+I*(k : ℂ)*Real.pi)^m*
      (hillAbelianSelectedGlobalPsi p.val.val p.val.property.1 p.val.property.2 n n.pos z/
        hillEnergyCanonicalRootProduct p.val.val p.val.property.1 p.val.property.2 z)
  let K := Icc (0 : ℝ) (2*Real.pi)
  let Z : V × K → ℂ := fun t => circleMap (c t.1.val) (R t.1.val) t.2.val
  have hZ : Continuous Z := by dsimp only [Z,circleMap]; fun_prop
  have hD (t : V × K) : (Z t,P t.1-SpectralWeight.one.toCoeff q.val)∈
      hillRecenteredContinuationDomain q.val q.property.1 q.property.2 :=
    hdom t.1.val t.1.property (Z t) (circleMap_mem_sphere (c t.1.val)
      (add_nonneg (hillRealGapContour_geometry t.1.val.val t.1.val.property.1 t.1.val.property.2 k k.pos).1
        (hillRealGapContour_geometry t.1.val.val t.1.val.property.1 t.1.val.property.2 k k.pos).2.1.le) t.2.val)
  have hcut (t : V × K) : (Z t,t.1.val)∈hillRealCutFamilyDomain :=
    hillRealGapContour_sphere_subset t.1.val.val t.1.val.property.1 t.1.val.property.2 k k.pos
      (circleMap_mem_sphere (c t.1.val)
        (add_nonneg (hillRealGapContour_geometry t.1.val.val t.1.val.property.1 t.1.val.property.2 k k.pos).1
          (hillRealGapContour_geometry t.1.val.val t.1.val.property.1 t.1.val.property.2 k k.pos).2.1.le) t.2.val)
  have hw : Continuous (fun t : V × K => w t.1 (Z t)) := by
    simpa only [w,P] using!
      continuous_recentered_moment_section q (fun p : V => p.val) continuous_subtype_val Z hZ n k m hD hcut
  have hL : Continuous (fun p : V => ∮ z in C(c p.val,R p.val),w p z) :=
    continuous_circleIntegral_of_continuous_moving_section (fun t : V × ℂ => w t.1 t.2)
      (fun p => c p.val) (fun p => R p.val) (hR.comp continuous_subtype_val) hw
  have heq (p : V) : (∮ z in C(c p.val,R p.val),w p z)=
      hillIntrinsicFrequencyMoment p.val.val p.val.property.1 p.val.property.2 n n.pos k m := by
    unfold hillIntrinsicFrequencyMoment frequencyMoment
    apply circleIntegral_eq_of_eq_on_nonreal_vector _ _ (hillRealGapCenter p.val.val p.val.property.1 p.val.property.2 k)
      (R p.val) (add_pos_of_nonneg_of_pos
        (hillRealGapContour_geometry p.val.val p.val.property.1 p.val.property.2 k k.pos).1
        (hillRealGapContour_geometry p.val.val p.val.property.1 p.val.property.2 k k.pos).2.1)
    intro z _ him
    dsimp only [w]
    rw [hillRecenteredPrimitive_eq_physical_nonreal q p.val z him]
    rfl
  have hOn : ContinuousOn (fun p : RealPeriodOneHillPotential =>
      hillIntrinsicFrequencyMoment p.val p.property.1 p.property.2 n n.pos k m) V :=
    continuousOn_iff_continuous_domRestrict.mpr (hL.congr heq)
  exact (hOn q hqV).continuousAt (hV.mem_nhds hqV)

/-- A literal finite positive-index physical moment sum, with the original coefficients. -/
def hillIntrinsicWeightedMomentPartialSum (p : RealPeriodOneHillPotential) (n : ℕ+) (a b L : ℕ) : ℂ :=
  ∑ k ∈ Finset.Icc 1 L, (k : ℂ)^a*hillIntrinsicFrequencyMoment p.val p.property.1 p.property.2 n n.pos k b

/-- Every finite weighted physical moment head is continuous in the full original L2 source. -/
theorem continuous_hillIntrinsicWeightedMomentPartialSum (n : ℕ+) (a b L : ℕ) :
    Continuous (fun p => hillIntrinsicWeightedMomentPartialSum p n a b L) := by
  apply continuous_finsetSum
  intro k hk
  have hkpos : 0<k := (Finset.mem_Icc.mp hk).1
  exact continuous_const.mul (continuous_hillIntrinsicFrequencyMoment n ⟨k,hkpos⟩ b)

end NLS.KdV
