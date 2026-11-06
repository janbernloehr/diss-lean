import NLS.KdV.HillDeflatedRootNonrealContinuity
import NLS.KdV.HillLocalDeflatedComplexRoot
import NLS.ComplexAnalysis.PrescribedAnalyticSquareRoot
import NLS.ComplexAnalysis.DenseNonreal

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



def hillGapFilledFamilyDomain (k : ℕ) : Set (ℂ × RealPeriodOneHillPotential) :=
  {t | t.1 ∈ hillGapFilledDomain t.2.val t.2.property.1 t.2.property.2 k}

theorem isOpen_hillGapFilledFamilyDomain (k : ℕ) : IsOpen (hillGapFilledFamilyDomain k) := by
  have he : hillGapFilledFamilyDomain k = {t : ℂ × RealPeriodOneHillPotential | t.1.im ≠ 0} ∪
      {t : ℂ × RealPeriodOneHillPotential |
        hillRealLabels t.2.val t.2.property.1 t.2.property.2 (2*k-2) < t.1.re ∧
        t.1.re < hillRealLabels t.2.val t.2.property.1 t.2.property.2 (2*k+1)} := by
    ext t
    rfl
  rw [he]
  exact (isOpen_ne_fun (continuous_im.comp continuous_fst) continuous_const).union
    ((isOpen_lt ((continuous_hillRealLabels (2*k-2)).comp continuous_snd)
      (continuous_re.comp continuous_fst)).inter
      (isOpen_lt (continuous_re.comp continuous_fst)
        ((continuous_hillRealLabels (2*k+1)).comp continuous_snd)))

variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

theorem exists_hillLocalDeflatedComplexRoot_local_physical_matching (k : ℕ) (hk : 1 ≤ k)
    (E : ℂ) (hE : E ∈ ball (hillRealGapCenter q hq hr k : ℂ)
      (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k)) :
    ∃ r : ℝ, 0 < r ∧ ∃ V : Set RealPeriodOneHillPotential,
      IsOpen V ∧ (⟨q,hq,hr⟩ : RealPeriodOneHillPotential) ∈ V ∧
        ∀ p ∈ V, ∀ z ∈ ball E r,
          (z,SpectralWeight.one.toCoeff p.val) ∈ hillLocalDeflatedRootDomain q hq hr k ∧
          z ∈ hillGapFilledDomain p.val p.property.1 p.property.2 k ∧
          hillLocalDeflatedComplexRoot q hq hr k (z,SpectralWeight.one.toCoeff p.val) =
            hillDeflatedEnergyCanonicalRoot p.val p.property.1 p.property.2 k z := by
  let p0 : RealPeriodOneHillPotential := ⟨q,hq,hr⟩
  let J : ℂ × RealPeriodOneHillPotential → ℂ × Coeff 2 := fun t => (t.1,SpectralWeight.one.toCoeff t.2.val)
  have hJ : Continuous J := continuous_fst.prodMk
    ((SpectralWeight.one.toCoeff.continuous.comp continuous_subtype_val).comp continuous_snd)
  let A := J ⁻¹' hillLocalDeflatedRootDomain q hq hr k ∩ hillGapFilledFamilyDomain k
  have hA : IsOpen A := ((isOpen_hillLocalDeflatedRootDomain q hq hr k hk).preimage hJ).inter
    (isOpen_hillGapFilledFamilyDomain k)
  have hbase : (E,p0) ∈ A := ⟨mem_hillLocalDeflatedRootDomain_base q hq hr k hk E hE,
    hillRealGapContour_closedBall_subset_filledDomain q hq hr k hk (ball_subset_closedBall hE)⟩
  obtain ⟨W,V,hW,hV,hEW,hpV,hWV⟩ := isOpen_prod_iff.mp hA E p0 hbase
  obtain ⟨r,hrpos,hball⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds hEW)
  obtain ⟨w,hwim,hw⟩ := dense_complex_nonreal.exists_mem_open isOpen_ball ⟨E,mem_ball_self hrpos⟩
  have hdom (p : RealPeriodOneHillPotential) (hp : p ∈ V) (z : ℂ) (hz : z ∈ ball E r) :
      (z,SpectralWeight.one.toCoeff p.val) ∈ hillLocalDeflatedRootDomain q hq hr k ∧
      z ∈ hillGapFilledDomain p.val p.property.1 p.property.2 k := by
    have hh : (z,p) ∈ A := hWV ⟨hball hz,hp⟩
    exact hh
  have hbw : w ∈ ball (hillRealGapCenter q hq hr k : ℂ)
      (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k) := (hdom p0 hpV w hw).1.1.2.1
  obtain ⟨U,hU,hpU,hunit⟩ := exists_hillLocalGapUnit_physical_neighborhood q hq hr k hk
  have hinc : Continuous (fun p : RealPeriodOneHillPotential => (w,SpectralWeight.one.toCoeff p.val)) :=
    continuous_const.prodMk (SpectralWeight.one.toCoeff.continuous.comp continuous_subtype_val)
  have hleft : ContinuousAt (fun p : RealPeriodOneHillPotential =>
      hillLocalDeflatedComplexRoot q hq hr k (w,SpectralWeight.one.toCoeff p.val)) p0 :=
    ContinuousAt.comp (f := fun p : RealPeriodOneHillPotential => (w,SpectralWeight.one.toCoeff p.val))
      (analyticOnNhd_hillLocalDeflatedComplexRoot q hq hr k hk _ (hdom p0 hpV w hw).1).continuousAt
      hinc.continuousAt
  have hright := (continuous_hillDeflatedEnergyCanonicalRoot_nonreal k hk w hwim).continuousAt (x := p0)
  have hsame : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 p0,
      hillLocalDeflatedComplexRoot q hq hr k (w,SpectralWeight.one.toCoeff p.val) =
        hillDeflatedEnergyCanonicalRoot p.val p.property.1 p.property.2 k w := by
    apply eventuallyEq_of_sq_eq_of_continuousAt _ _ p0 hleft hright
      (hillLocalDeflatedComplexRoot_base q hq hr k hk w hbw)
      (hillDeflatedEnergyCanonicalRoot_ne_zero q hq hr k hk w (Or.inl hwim))
    filter_upwards [hV.mem_nhds hpV,hU.mem_nhds hpU] with p hpV' hpU'
    exact (hillLocalDeflatedComplexRoot_sq q hq hr k hk _ (hdom p hpV' w hw).1).trans
      (hunit p hpU' w hbw)
  obtain ⟨V',hV'sub,hV'open,hpV'⟩ := _root_.mem_nhds_iff.mp hsame
  refine ⟨r,hrpos,(V ∩ U) ∩ V',(hV.inter hU).inter hV'open,⟨⟨hpV,hpU⟩,hpV'⟩,?_⟩
  intro p hp z hz
  have hleft' : ContinuousOn (fun u => hillLocalDeflatedComplexRoot q hq hr k
      (u,SpectralWeight.one.toCoeff p.val)) (ball E r) :=
    (analyticOnNhd_hillLocalDeflatedComplexRoot q hq hr k hk).continuousOn.comp (by fun_prop)
      (fun u hu => (hdom p hp.1.1 u hu).1)
  have hright' : ContinuousOn (hillDeflatedEnergyCanonicalRoot p.val p.property.1 p.property.2 k)
      (ball E r) :=
    (analyticOnNhd_hillDeflatedEnergyCanonicalRoot p.val p.property.1 p.property.2 k).continuousOn.mono
      (fun u hu => (hdom p hp.1.1 u hu).2)
  have he := (convex_ball E r).isPreconnected.eq_of_sq_eq hleft' hright'
    (fun u hu => (hillLocalDeflatedComplexRoot_sq q hq hr k hk _ (hdom p hp.1.1 u hu).1).trans
      (hunit p hp.1.2 u (hdom p hp.1.1 u hu).1.1.2.1))
    (fun {u} hu => hillDeflatedEnergyCanonicalRoot_ne_zero p.val p.property.1 p.property.2 k hk u
      (hdom p hp.1.1 u hu).2) hw (hV'sub hp.2)
  exact ⟨(hdom p hp.1.1 z hz).1,(hdom p hp.1.1 z hz).2,he hz⟩

end NLS.KdV
