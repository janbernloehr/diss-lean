import NLS.KdV.HillHminusLocalFilledTrace
import NLS.KdV.HillDeflatedLocalPhysicalMatching
import NLS.KdV.HillDirichletLabelContinuity
import NLS.KdV.HillHminusPhysicalPeriodicLabels
import NLS.KdV.HillAbelianCoordinateFactor

/-! # Rough local inverse roots evaluated at the actual moving divisor -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
namespace NLS.KdV
variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem hillFreeGapCenter_complex_square (n : ℕ+) :
    (hillRealGapCenter 0 h0q h0r (n : ℕ) : ℂ)=((Real.pi : ℂ)*(n : ℕ))^2 := by
  rw [hillFreeGapCenter h0q h0r (n : ℕ) n.property]
  simp only [freeHillValue,Int.cast_natCast,ofReal_mul,ofReal_pow,ofReal_natCast]
  ring

theorem hillHminusLocalDeflatedRoot_base (n : ℕ+) (E : ℂ)
    (hE : E ∈ ball (hillRealGapCenter 0 h0q h0r (n : ℕ) : ℂ)
      (hillRealGapHalfLength 0 h0q h0r (n : ℕ)+hillRealGapCollar 0 h0q h0r (n : ℕ))) :
    hillHminusLocalDeflatedRoot h0q h0r n (E,0)=hillDeflatedEnergyCanonicalRoot 0 h0q h0r (n : ℕ) E := by
  have he := hillHminusLocalDeflatedRoot_l2 h0q h0r n (0 : Coeff 2) E
  simp only [map_zero] at he
  exact he.trans (by simpa only [map_zero] using
    hillLocalDeflatedComplexRoot_base 0 h0q h0r (n : ℕ) n.property E hE)

theorem analyticAt_hillHminusLocalDeflatedRoot_zero (n : ℕ+) :
    AnalyticAt ℂ (hillHminusLocalDeflatedRoot h0q h0r n)
      ((hillRealGapCenter 0 h0q h0r (n : ℕ) : ℂ),0) := by
  let c : ℂ := hillRealGapCenter 0 h0q h0r (n : ℕ)
  let R := hillRealGapHalfLength 0 h0q h0r (n : ℕ)+hillRealGapCollar 0 h0q h0r (n : ℕ)
  have hR : 0 < R := add_pos_of_nonneg_of_pos
    (hillRealGapContour_geometry 0 h0q h0r (n : ℕ) n.property).1
    (hillRealGapContour_geometry 0 h0q h0r (n : ℕ) n.property).2.1
  have hc : c ∈ hillGapFilledDomain 0 h0q h0r (n : ℕ) :=
    hillRealGapContour_closedBall_subset_filledDomain 0 h0q h0r (n : ℕ) n.property
      (mem_closedBall_self hR.le)
  let B : ℂ × PeriodOneHminusOne → ℂ := fun t => hillDeflatedEnergyCanonicalRoot 0 h0q h0r (n : ℕ) t.1
  have hB0 := analyticOnNhd_hillDeflatedEnergyCanonicalRoot 0 h0q h0r (n : ℕ) c hc
  have hBa : AnalyticAt ℂ B (c,0) :=
    hB0.comp (x := (c,(0 : PeriodOneHminusOne)))
      (f := fun t : ℂ × PeriodOneHminusOne => t.1) analyticAt_fst
  have hBn : B (c,0) ≠ 0 := hillDeflatedEnergyCanonicalRoot_ne_zero 0 h0q h0r (n : ℕ) n.property c hc
  obtain ⟨W,_hW,h0W,hU⟩ := exists_hillHminusLocalGapUnit_analytic h0q h0r n
  have hUa := hU (c,0) ⟨mem_ball_self hR,h0W⟩
  have hU0 : hillHminusLocalGapUnit h0q h0r n (c,0)=B (c,0)^2 :=
    hillHminusLocalGapUnit_zero h0q h0r n c (mem_ball_self hR)
  have hrat : hillHminusLocalGapUnit h0q h0r n (c,0)/B (c,0)^2=1 := by
    rw [hU0,div_self (pow_ne_zero 2 hBn)]
  have hs := (Complex.differentiableOn_sqrt.analyticAt (isOpen_slitPlane.mem_nhds
    (hrat ▸ one_mem_slitPlane))).comp (f := fun t => hillHminusLocalGapUnit h0q h0r n t/B t^2)
      (hUa.div (hBa.pow 2) (pow_ne_zero 2 hBn))
  exact hBa.mul hs

def hillHminusMovingDirichletEnergy (D : PeriodOneHminusOne → Coeff 2) (n : ℕ+)
    (q : PeriodOneHminusOne) : ℂ := ((Real.pi : ℂ)*(n : ℕ))^2+(n : ℂ)*D q (n : ℤ)

theorem analyticAt_hillHminusMovingDirichletEnergy (D : PeriodOneHminusOne → Coeff 2)
    (n : ℕ+) (q : PeriodOneHminusOne) (hD : AnalyticAt ℂ D q) :
    AnalyticAt ℂ (hillHminusMovingDirichletEnergy D n) q := by
  have he := ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 (n : ℤ)).analyticAt (D q)).comp hD
  exact analyticAt_const.add (analyticAt_const.mul he)

theorem hillHminusMovingDirichletEnergy_zero (D : PeriodOneHminusOne → Coeff 2)
    (hD0 : D 0=0) (n : ℕ+) :
    hillHminusMovingDirichletEnergy D n 0=((Real.pi : ℂ)*(n : ℕ))^2 := by
  simp only [hillHminusMovingDirichletEnergy,hD0,lp.coeFn_zero,Pi.zero_apply,mul_zero,add_zero]

def hillHminusLocalNormalizedRootInverse (D : PeriodOneHminusOne → Coeff 2) (n : ℕ+)
    (q : PeriodOneHminusOne) : ℂ :=
  ((n : ℂ)*hillHminusLocalDeflatedRoot h0q h0r n (hillHminusMovingDirichletEnergy D n q,q))⁻¹

theorem analyticAt_hillHminusLocalNormalizedRootInverse (D : PeriodOneHminusOne → Coeff 2)
    (hD : AnalyticAt ℂ D 0) (hD0 : D 0=0) (n : ℕ+) :
    AnalyticAt ℂ (hillHminusLocalNormalizedRootInverse h0q h0r D n) 0 := by
  let c : ℂ := hillRealGapCenter 0 h0q h0r (n : ℕ)
  let R := hillRealGapHalfLength 0 h0q h0r (n : ℕ)+hillRealGapCollar 0 h0q h0r (n : ℕ)
  have hR : 0 < R := add_pos_of_nonneg_of_pos
    (hillRealGapContour_geometry 0 h0q h0r (n : ℕ) n.property).1
    (hillRealGapContour_geometry 0 h0q h0r (n : ℕ) n.property).2.1
  have hE0 : hillHminusMovingDirichletEnergy D n 0=c :=
    (hillHminusMovingDirichletEnergy_zero D hD0 n).trans
      (hillFreeGapCenter_complex_square h0q h0r n).symm
  have hroot : AnalyticAt ℂ (hillHminusLocalDeflatedRoot h0q h0r n)
      (hillHminusMovingDirichletEnergy D n 0,(0 : PeriodOneHminusOne)) := by
    rw [hE0]
    exact analyticAt_hillHminusLocalDeflatedRoot_zero h0q h0r n
  have ha := hroot.comp (f := fun q => (hillHminusMovingDirichletEnergy D n q,q))
    ((analyticAt_hillHminusMovingDirichletEnergy D n 0 hD).prod analyticAt_id)
  have hn : (n : ℂ)≠0 := by exact_mod_cast n.ne_zero
  have hc : c ∈ hillGapFilledDomain 0 h0q h0r (n : ℕ) :=
    hillRealGapContour_closedBall_subset_filledDomain 0 h0q h0r (n : ℕ) n.property
      (mem_closedBall_self hR.le)
  have hB : hillHminusLocalDeflatedRoot h0q h0r n (hillHminusMovingDirichletEnergy D n 0,0)≠0 := by
    rw [hE0,hillHminusLocalDeflatedRoot_base h0q h0r n c (mem_ball_self hR)]
    exact hillDeflatedEnergyCanonicalRoot_ne_zero 0 h0q h0r (n : ℕ) n.property c hc
  exact (analyticAt_const.mul ha).inv (mul_ne_zero hn hB)

theorem exists_hillHminusLocalNormalizedRootInverse_analytic_bound
    (D : PeriodOneHminusOne → Coeff 2) (hD : AnalyticAt ℂ D 0) (hD0 : D 0=0) (n : ℕ+) :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧
      AnalyticOnNhd ℂ (hillHminusLocalNormalizedRootInverse h0q h0r D n)
        (ball (0 : PeriodOneHminusOne) η) ∧
      ∀ q ∈ ball (0 : PeriodOneHminusOne) η, ‖hillHminusLocalNormalizedRootInverse h0q h0r D n q‖ ≤ C := by
  let H := hillHminusLocalNormalizedRootInverse h0q h0r D n
  have ha := analyticAt_hillHminusLocalNormalizedRootInverse h0q h0r D hD hD0 n
  obtain ⟨r,hr,hRa⟩ := ha.exists_ball_analyticOnNhd
  have he := ha.continuousAt.preimage_mem_nhds (ball_mem_nhds (H 0) zero_lt_one)
  obtain ⟨s,hs,hsub⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨min r s,‖H 0‖+1,lt_min hr hs,by positivity,hRa.mono (ball_subset_ball (min_le_left r s)),?_⟩
  intro q hq
  have hh := mem_ball_iff_norm.mp (hsub (ball_subset_ball (min_le_right r s) hq))
  have ht := norm_le_norm_sub_add (H q) (H 0)
  linarith

theorem hillHminusLocalNormalizedRootInverse_physical_germ
    (D : PeriodOneHminusOne → Coeff 2) (n : ℕ+)
    (hD : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 ⟨0,h0q,h0r⟩,
      hillHminusMovingDirichletEnergy D n (hillPhysicalHminusEmbedding p).val=
        (hillDirichletEnergy p.val p.property.1 p.property.2 (n : ℕ) n.property : ℂ)) :
    ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 ⟨0,h0q,h0r⟩,
      hillHminusLocalNormalizedRootInverse h0q h0r D n (hillPhysicalHminusEmbedding p).val=
        ((n : ℂ)*hillDeflatedEnergyCanonicalRoot p.val p.property.1 p.property.2 (n : ℕ)
          (hillDirichletEnergy p.val p.property.1 p.property.2 (n : ℕ) n.property))⁻¹ := by
  let c : ℂ := hillRealGapCenter 0 h0q h0r (n : ℕ)
  let μ : RealPeriodOneHillPotential → ℂ := fun p => hillDirichletEnergy p.val p.property.1 p.property.2 (n : ℕ) n.property
  have hμ : Continuous μ := continuous_ofReal.comp (continuous_hillDirichletEnergy (n : ℕ) n.property)
  have hμ0 : μ (⟨0,h0q,h0r⟩ : RealPeriodOneHillPotential)=c := by
    exact congrArg Complex.ofReal (hillDirichletEnergy_eq_center_of_halfLength_zero 0 h0q h0r
      (n : ℕ) n.property (hillFreeGapHalfLength h0q h0r (n : ℕ) n.property))
  have hR : 0 < hillRealGapHalfLength 0 h0q h0r (n : ℕ)+hillRealGapCollar 0 h0q h0r (n : ℕ) :=
    add_pos_of_nonneg_of_pos (hillRealGapContour_geometry 0 h0q h0r (n : ℕ) n.property).1
      (hillRealGapContour_geometry 0 h0q h0r (n : ℕ) n.property).2.1
  obtain ⟨s,hs,W,hW,h0W,hmatch⟩ := exists_hillLocalDeflatedComplexRoot_local_physical_matching
    0 h0q h0r (n : ℕ) n.property c (mem_ball_self hR)
  have ht : Tendsto μ (𝓝 (⟨0,h0q,h0r⟩ : RealPeriodOneHillPotential)) (𝓝 c) := by
    simpa only [hμ0] using hμ.tendsto (⟨0,h0q,h0r⟩ : RealPeriodOneHillPotential)
  filter_upwards [hD,hW.mem_nhds h0W,ht.eventually (ball_mem_nhds c hs)] with p hpD hpW hpμ
  rw [hillHminusLocalNormalizedRootInverse,hpD]
  have he := hillHminusLocalDeflatedRoot_l2 h0q h0r n
    (Fourier.paritySample 0 (SpectralWeight.one.toCoeff p.val)) (μ p)
  rw [hillPeriodDouble_unitSample _ p.property.1] at he
  have hh : hillHminusLocalDeflatedRoot h0q h0r n (μ p,(hillPhysicalHminusEmbedding p).val)=
      hillDeflatedEnergyCanonicalRoot p.val p.property.1 p.property.2 (n : ℕ) (μ p) :=
    he.trans (hmatch p hpW (μ p) hpμ).2.2
  exact congrArg (fun z : ℂ => ((n : ℂ)*z)⁻¹) hh

end NLS.KdV
