import NLS.KdV.HillHminusLocalGapMoments
import NLS.KdV.HillDeflatedTraceCharts

/-! # Actual rough Cauchy deflation and its free-normalized trace germ -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
namespace NLS.KdV
variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

def hillHminusLocalGapPolynomial (n : ℕ+) (q : PeriodOneHminusOne) (E : ℂ) : ℂ :=
  (E-hillHminusLocalGapMidpoint h0q h0r n q)^2-hillHminusLocalGapSquare h0q h0r n q/4

def hillHminusLocalGapUnit (n : ℕ+) : ℂ × PeriodOneHminusOne → ℂ :=
  parametricCircleCauchyTransform
    (fun t : ℂ × PeriodOneHminusOne => hillHminusRadicand t.2 t.1 /
      hillHminusLocalGapPolynomial h0q h0r n t.2 t.1)
    (hillRealGapCenter 0 h0q h0r (n : ℕ))
    (hillRealGapHalfLength 0 h0q h0r (n : ℕ)+hillRealGapCollar 0 h0q h0r (n : ℕ))

def hillHminusLocalDeflatedRoot (n : ℕ+) (t : ℂ × PeriodOneHminusOne) : ℂ :=
  hillDeflatedEnergyCanonicalRoot 0 h0q h0r (n : ℕ) t.1 *
    sqrt (hillHminusLocalGapUnit h0q h0r n t /
      hillDeflatedEnergyCanonicalRoot 0 h0q h0r (n : ℕ) t.1^2)

def hillHminusLocalDeflatedTrace (n : ℕ+) (t : ℂ × PeriodOneHminusOne) : ℂ :=
  deriv (hillHminusDiscriminant t.2) t.1 / hillHminusLocalDeflatedRoot h0q h0r n t

theorem hillHminusLocalGapUnit_l2 (n : ℕ+) (u : Coeff 2) (E : ℂ) :
    hillHminusLocalGapUnit h0q h0r n (E,periodOneL2Inclusion u) =
      hillLocalGapUnit 0 h0q h0r (n : ℕ) (E,Coeff.periodDouble u) := by
  simp only [hillHminusLocalGapUnit,hillLocalGapUnit,parametricCircleCauchyTransform,
    hillHminusLocalGapPolynomial,hillLocalGapPolynomial,hillHminusLocalGapMidpoint_l2,
    hillHminusLocalGapSquare_l2,hillHminusRadicand_eq_hillL2]

theorem hillHminusLocalDeflatedRoot_l2 (n : ℕ+) (u : Coeff 2) (E : ℂ) :
    hillHminusLocalDeflatedRoot h0q h0r n (E,periodOneL2Inclusion u) =
      hillLocalDeflatedComplexRoot 0 h0q h0r (n : ℕ) (E,Coeff.periodDouble u) := by
  simp only [hillHminusLocalDeflatedRoot,hillLocalDeflatedComplexRoot,
    hillLocalDeflatedRootRatio,hillHminusLocalGapUnit_l2]

theorem hillHminusLocalDeflatedTrace_l2 (n : ℕ+) (u : Coeff 2) (E : ℂ) :
    hillHminusLocalDeflatedTrace h0q h0r n (E,periodOneL2Inclusion u) =
      hillLocalDeflatedTraceNumerator 0 h0q h0r (n : ℕ) (E,Coeff.periodDouble u) := by
  have he : hillHminusDiscriminant (periodOneL2Inclusion u) =
      hillL2Discriminant (Coeff.periodDouble u) := funext (hillHminusDiscriminant_eq_hillL2 u)
  simp only [hillHminusLocalDeflatedTrace,hillLocalDeflatedTraceNumerator,
    hillHminusLocalDeflatedRoot_l2,he]

theorem hillHminusLocalGapUnit_zero (n : ℕ+) (E : ℂ)
    (hE : E ∈ ball (hillRealGapCenter 0 h0q h0r (n : ℕ) : ℂ)
      (hillRealGapHalfLength 0 h0q h0r (n : ℕ)+hillRealGapCollar 0 h0q h0r (n : ℕ))) :
    hillHminusLocalGapUnit h0q h0r n (E,0) =
      hillDeflatedEnergyCanonicalRoot 0 h0q h0r (n : ℕ) E^2 := by
  calc
    _ = hillLocalGapUnit 0 h0q h0r (n : ℕ) (E,0) := by
      simpa only [map_zero] using hillHminusLocalGapUnit_l2 h0q h0r n (0 : Coeff 2) E
    _ = _ := by
      simpa only [map_zero] using hillLocalGapUnit_at_base 0 h0q h0r (n : ℕ) n.property E hE

theorem exists_hillHminusLocalGapUnit_analytic (n : ℕ+) :
    ∃ W : Set PeriodOneHminusOne, IsOpen W ∧ (0 : PeriodOneHminusOne) ∈ W ∧
      AnalyticOnNhd ℂ (hillHminusLocalGapUnit h0q h0r n)
        (ball (hillRealGapCenter 0 h0q h0r (n : ℕ) : ℂ)
          (hillRealGapHalfLength 0 h0q h0r (n : ℕ)+hillRealGapCollar 0 h0q h0r (n : ℕ)) ×ˢ W) := by
  obtain ⟨V,hV,h0V,hM,hS⟩ := exists_hillHminusLocalGapMoments_analytic h0q h0r n
  let c : ℂ := hillRealGapCenter 0 h0q h0r (n : ℕ)
  let R := hillRealGapHalfLength 0 h0q h0r (n : ℕ)+hillRealGapCollar 0 h0q h0r (n : ℕ)
  have hR : 0 < R := add_pos_of_nonneg_of_pos
    (hillRealGapContour_geometry 0 h0q h0r (n : ℕ) n.property).1
    (hillRealGapContour_geometry 0 h0q h0r (n : ℕ) n.property).2.1
  let P : ℂ × PeriodOneHminusOne → ℂ := fun t => hillHminusLocalGapPolynomial h0q h0r n t.2 t.1
  let B : Set (ℂ × PeriodOneHminusOne) := univ ×ˢ V
  have hB : IsOpen B := isOpen_univ.prod hV
  have hP : AnalyticOnNhd ℂ P B := by
    intro t ht
    exact ((analyticAt_fst.sub ((hM t.2 ht.2).comp analyticAt_snd)).pow 2).sub
      (((hS t.2 ht.2).comp analyticAt_snd).div_const)
  let D := B ∩ P ⁻¹' ({0} : Set ℂ)ᶜ
  have hD : IsOpen D := hP.continuousOn.isOpen_inter_preimage hB isClosed_singleton.isOpen_compl
  have hbase : sphere c R ×ˢ ({0} : Set PeriodOneHminusOne) ⊆ D := by
    rintro ⟨z,q⟩ ⟨hz,hq⟩
    have hq0 : q = 0 := mem_singleton_iff.mp hq
    subst q
    refine ⟨⟨mem_univ _,h0V⟩,?_⟩
    change P (z,0) ≠ 0
    simp only [P,hillHminusLocalGapPolynomial,(hillHminusLocalGapMoments_zero h0q h0r n).1,
      (hillHminusLocalGapMoments_zero h0q h0r n).2,zero_div,sub_zero]
    apply pow_ne_zero 2
    apply sub_ne_zero.mpr
    intro he
    rw [he] at hz
    exact (ne_of_gt hR) (by simpa only [c,mem_sphere,dist_self] using hz.symm)
  obtain ⟨Z,W,_,hW,hKZ,h0W,hZW⟩ :=
    generalized_tube_lemma (isCompact_sphere c R) isCompact_singleton hD hbase
  have hF : AnalyticOnNhd ℂ
      (fun t : ℂ × PeriodOneHminusOne => hillHminusRadicand t.2 t.1/P t)
      (sphere c R ×ˢ W) := by
    intro t ht
    have hd := hZW ⟨hKZ ht.1,ht.2⟩
    exact (analyticOnNhd_hillHminusRadicand_joint t (mem_univ _)).div (hP t hd.1) hd.2
  have hU := analyticOnNhd_parametricCircleCauchyTransform _ c R hR.le W hW hF
  refine ⟨W,hW,h0W (mem_singleton 0),hU.mono ?_⟩
  intro t ht
  exact ⟨fun he => (ne_of_lt ht.1) he,ht.2⟩

theorem analyticAt_hillHminusLocalDeflatedTrace_zero (n : ℕ+) :
    AnalyticAt ℂ (hillHminusLocalDeflatedTrace h0q h0r n)
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
  have hB0 : AnalyticAt ℂ (hillDeflatedEnergyCanonicalRoot 0 h0q h0r (n : ℕ)) c :=
    analyticOnNhd_hillDeflatedEnergyCanonicalRoot 0 h0q h0r (n : ℕ) c hc
  have hBa : AnalyticAt ℂ B (c,0) := by
    exact hB0.comp (x := (c,(0 : PeriodOneHminusOne)))
      (f := fun t : ℂ × PeriodOneHminusOne => t.1) analyticAt_fst
  have hBn : B (c,0) ≠ 0 := hillDeflatedEnergyCanonicalRoot_ne_zero 0 h0q h0r (n : ℕ) n.property c hc
  obtain ⟨W,_,h0W,hU⟩ := exists_hillHminusLocalGapUnit_analytic h0q h0r n
  have hUa := hU (c,0) ⟨mem_ball_self hR,h0W⟩
  have hU0 : hillHminusLocalGapUnit h0q h0r n (c,0) = B (c,0)^2 :=
    hillHminusLocalGapUnit_zero h0q h0r n c (mem_ball_self hR)
  have hrat : hillHminusLocalGapUnit h0q h0r n (c,0)/B (c,0)^2 = 1 := by
    rw [hU0,div_self (pow_ne_zero 2 hBn)]
  have hs := (Complex.differentiableOn_sqrt.analyticAt (isOpen_slitPlane.mem_nhds
    (hrat ▸ one_mem_slitPlane))).comp (f := fun t => hillHminusLocalGapUnit h0q h0r n t/B t^2)
      (hUa.div (hBa.pow 2) (pow_ne_zero 2 hBn))
  have hroot : hillHminusLocalDeflatedRoot h0q h0r n (c,0) ≠ 0 := by
    change B (c,0)*sqrt (hillHminusLocalGapUnit h0q h0r n (c,0)/B (c,0)^2) ≠ 0
    simpa only [hrat,sqrt_one,mul_one] using hBn
  have hD := analyticOnNhd_spectral_deriv_of_analyticOnNhd
    (fun t : ℂ × PeriodOneHminusOne => hillHminusDiscriminant t.2 t.1) univ isOpen_univ
    analyticOnNhd_hillHminusDiscriminant_joint
  exact (hD (c,0) (mem_univ _)).div (hBa.mul hs) hroot

end NLS.KdV
