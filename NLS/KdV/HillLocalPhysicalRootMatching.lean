import NLS.KdV.HillLocalNonrealRootMatching
import NLS.KdV.HillLabelContinuity
import NLS.ComplexAnalysis.CompactSliceLocalBounds

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



def hillRealCutFamilyDomain : Set (ℂ × RealPeriodOneHillPotential) :=
  {t | t.1 ∈ hillL2RealCutDomain t.2.val t.2.property.1 t.2.property.2}

theorem isOpen_hillRealCutFamilyDomain : IsOpen hillRealCutFamilyDomain := by
  have he : hillRealCutFamilyDomain = {t : ℂ × RealPeriodOneHillPotential | t.1.im ≠ 0} ∪
      ⋃ j : ℕ, {t : ℂ × RealPeriodOneHillPotential |
        hillRealLabels t.2.val t.2.property.1 t.2.property.2 (2*j) < t.1.re ∧
        t.1.re < hillRealLabels t.2.val t.2.property.1 t.2.property.2 (2*j+1)} := by
    ext t
    simp only [hillRealCutFamilyDomain,hillL2RealCutDomain,mem_ofPred_eq,mem_union,mem_iUnion,mem_Ioo]
  rw [he]
  apply (isOpen_ne_fun (continuous_im.comp continuous_fst) continuous_const).union
  apply isOpen_iUnion
  intro j
  exact (isOpen_lt ((continuous_hillRealLabels (2*j)).comp continuous_snd)
    (continuous_re.comp continuous_fst)).inter
      (isOpen_lt (continuous_re.comp continuous_fst) ((continuous_hillRealLabels (2*j+1)).comp continuous_snd))

variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

theorem exists_hillAbelianComplexRoot_local_physical_matching (E : ℂ) (hE : E ∈ hillL2RealCutDomain q hq hr) :
    ∃ r : ℝ, 0 < r ∧ ∃ V : Set RealPeriodOneHillPotential,
      IsOpen V ∧ (⟨q,hq,hr⟩ : RealPeriodOneHillPotential) ∈ V ∧
        ∀ p ∈ V, ∀ z ∈ ball E r,
          (z,SpectralWeight.one.toCoeff p.val) ∈ hillAbelianComplexRootDomain q hq hr ∧
          z ∈ hillL2RealCutDomain p.val p.property.1 p.property.2 ∧
          hillAbelianComplexRoot q hq hr (z,SpectralWeight.one.toCoeff p.val) =
            hillEnergyCanonicalRootProduct p.val p.property.1 p.property.2 z := by
  let p0 : RealPeriodOneHillPotential := ⟨q,hq,hr⟩
  let J : ℂ × RealPeriodOneHillPotential → ℂ × Coeff 2 := fun t => (t.1,SpectralWeight.one.toCoeff t.2.val)
  have hJ : Continuous J := continuous_fst.prodMk
    ((SpectralWeight.one.toCoeff.continuous.comp continuous_subtype_val).comp continuous_snd)
  let A := J ⁻¹' hillAbelianComplexRootDomain q hq hr ∩ hillRealCutFamilyDomain
  have hA : IsOpen A := ((isOpen_hillAbelianComplexRootDomain q hq hr).preimage hJ).inter isOpen_hillRealCutFamilyDomain
  have hbase : (E,p0) ∈ A := ⟨mem_hillAbelianComplexRootDomain_base q hq hr E hE,hE⟩
  obtain ⟨W,V,hW,hV,hEW,hpV,hWV⟩ := isOpen_prod_iff.mp hA E p0 hbase
  obtain ⟨r,hrpos,hball⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds hEW)
  obtain ⟨w,hwim,hw⟩ := dense_complex_nonreal.exists_mem_open isOpen_ball ⟨E,mem_ball_self hrpos⟩
  have hT : Tendsto (fun p : RealPeriodOneHillPotential => (w,SpectralWeight.one.toCoeff p.val))
      (𝓝 p0) (𝓝 (w,SpectralWeight.one.toCoeff q)) :=
    continuousAt_const.prodMk (SpectralWeight.one.toCoeff.continuous.comp continuous_subtype_val).continuousAt
  have hmatch : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 p0,
      hillAbelianComplexRoot q hq hr (w,SpectralWeight.one.toCoeff p.val) =
        hillL2ContinuedRoot (w,SpectralWeight.one.toCoeff p.val) :=
    hT.eventually (hillAbelianComplexRoot_eventually_eq_continued_at_nonreal q hq hr w hwim)
  obtain ⟨V',hV'sub,hV'open,hpV'⟩ := _root_.mem_nhds_iff.mp hmatch
  refine ⟨r,hrpos,V ∩ V',hV.inter hV'open,⟨hpV,hpV'⟩,?_⟩
  intro p hp z hz
  have hdom (u : ℂ) (hu : u ∈ ball E r) :
      (u,SpectralWeight.one.toCoeff p.val) ∈ hillAbelianComplexRootDomain q hq hr ∧
      u ∈ hillL2RealCutDomain p.val p.property.1 p.property.2 := by
    have hh : (u,p) ∈ A := hWV ⟨hball hu,hp.1⟩
    exact hh
  have hleft : ContinuousOn (fun u => hillAbelianComplexRoot q hq hr (u,SpectralWeight.one.toCoeff p.val)) (ball E r) :=
    (analyticOnNhd_hillAbelianComplexRoot q hq hr).continuousOn.comp (by fun_prop)
      (fun u hu => (hdom u hu).1)
  have hright : ContinuousOn (hillEnergyCanonicalRootProduct p.val p.property.1 p.property.2) (ball E r) :=
    (analyticOnNhd_hillEnergyCanonicalRootProduct p.val p.property.1 p.property.2).continuousOn.mono
      (fun u hu => (hdom u hu).2)
  have hsame : hillAbelianComplexRoot q hq hr (w,SpectralWeight.one.toCoeff p.val) =
      hillEnergyCanonicalRootProduct p.val p.property.1 p.property.2 w :=
    (hV'sub hp.2).trans (hillEnergyCanonicalRootProduct_eq_continued_of_mem p.val p.property.1 p.property.2 w
      (Or.inl hwim) (mem_hillL2ContinuationDomain_of_im_ne_zero p.val p.property.1 p.property.2 w hwim)).symm
  have he := (convex_ball E r).isPreconnected.eq_of_sq_eq hleft hright
    (fun u hu => (hillAbelianComplexRoot_sq q hq hr _ (hdom u hu).1).trans
      (hillEnergyCanonicalRootProduct_sq_actual p.val p.property.1 p.property.2 u (hdom u hu).2).symm)
    (fun {u} hu => hillEnergyCanonicalRootProduct_ne_zero_on_realCutDomain p.val p.property.1 p.property.2 u (hdom u hu).2)
    hw hsame
  exact ⟨(hdom z hz).1,(hdom z hz).2,he hz⟩

theorem exists_hillAbelianComplexRoot_physical_contour_neighborhood
    (k : ℕ) (hk : 1 ≤ k) :
    ∃ V : Set RealPeriodOneHillPotential, IsOpen V ∧ (⟨q,hq,hr⟩ : RealPeriodOneHillPotential) ∈ V ∧
      ∀ p ∈ V, ∀ z ∈ sphere (hillRealGapCenter q hq hr k : ℂ)
          (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k),
        (z,SpectralWeight.one.toCoeff p.val) ∈ hillAbelianComplexRootDomain q hq hr ∧
        z ∈ hillL2RealCutDomain p.val p.property.1 p.property.2 ∧
        hillAbelianComplexRoot q hq hr (z,SpectralWeight.one.toCoeff p.val) =
          hillEnergyCanonicalRootProduct p.val p.property.1 p.property.2 z := by
  let c := (hillRealGapCenter q hq hr k : ℂ)
  let R := hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k
  let P : (ℂ × RealPeriodOneHillPotential) → ℝ → Prop := fun t _ =>
    (t.1,SpectralWeight.one.toCoeff t.2.val) ∈ hillAbelianComplexRootDomain q hq hr ∧
    t.1 ∈ hillL2RealCutDomain t.2.val t.2.property.1 t.2.property.2 ∧
    hillAbelianComplexRoot q hq hr (t.1,SpectralWeight.one.toCoeff t.2.val) =
      hillEnergyCanonicalRootProduct t.2.val t.2.property.1 t.2.property.2 t.1
  have hlocal (z : ℂ) (hz : z ∈ sphere c R) :
      ∃ W : Set (ℂ × RealPeriodOneHillPotential), IsOpen W ∧ (z,(⟨q,hq,hr⟩ : RealPeriodOneHillPotential)) ∈ W ∧
        ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ W, P t C := by
    obtain ⟨r,hrpos,V,hV,hqV,hmatching⟩ := exists_hillAbelianComplexRoot_local_physical_matching q hq hr z
      (hillRealGapContour_sphere_subset q hq hr k hk hz)
    exact ⟨ball z r ×ˢ V,isOpen_ball.prod hV,⟨mem_ball_self hrpos,hqV⟩,0,le_rfl,
      fun t ht => hmatching t.2 ht.2 t.1 ht.1⟩
  obtain ⟨V,hV,hqV,C,_,hprop⟩ := exists_uniform_property_near_compact_slice
    (sphere c R) (isCompact_sphere c R) (⟨q,hq,hr⟩ : RealPeriodOneHillPotential) P
      (fun _ _ _ _ h => h) hlocal
  exact ⟨V,hV,hqV,fun p hp z hz => hprop p hp z hz⟩

end NLS.KdV
