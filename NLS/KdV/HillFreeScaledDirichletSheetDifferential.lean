import NLS.KdV.HillFreeDirichletSheetDifferential
import NLS.KdV.HillFreeDeflatedRootValue
import NLS.KdV.HillHminusOriginalOwnGapFactor

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
namespace NLS.KdV

variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

/-- The ORIGINAL free signed sheet vanishes at the collapsed base gap. -/
theorem hillDirichletSheet_hminus_free_zero
    (n : ℕ) (hn : 1 ≤ n) (S : PeriodOneHminusOne → ℂ)
    (hSM : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨0,h0q,h0r⟩ : RealPeriodOneHillPotential),
      S (hillOriginalHminusSource p.val) = hillDirichletSheetRoot
        (SpectralWeight.one.toCoeff p.val) (hillDirichletEnergy p.val p.property.1 p.property.2 n hn)) : S 0 = 0 := by
  have hh := hSM.self_of_nhds
  rw [hillDirichletSheetRoot_at_dirichlet_eq_norming,
    hillDirichletLogMultiplier_zero_potential h0q h0r n hn,Real.sinh_zero,mul_zero,ofReal_zero] at hh
  simpa only [map_zero] using hh

/-- At the free collapsed gap, the quotient by the ORIGINAL deflated root
has its exact antisymmetric Fourier differential. Any analytic moving root
with the actual original base value is allowed: its derivative is multiplied
by the vanishing original sheet and hence contributes zero. -/
theorem hillFree_scaledDirichletSheet_fourier_fderiv
    (n : ℕ) (hn : 1 ≤ n) (S B : PeriodOneHminusOne → ℂ)
    (hS : AnalyticAt ℂ S 0) (hB : AnalyticAt ℂ B 0)
    (hSM : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨0,h0q,h0r⟩ : RealPeriodOneHillPotential),
      S (hillOriginalHminusSource p.val) = hillDirichletSheetRoot
        (SpectralWeight.one.toCoeff p.val) (hillDirichletEnergy p.val p.property.1 p.property.2 n hn))
    (hB0 : B 0 = hillDeflatedEnergyCanonicalRoot 0 h0q h0r n (freeHillValue n : ℂ))
    (h : PeriodOneHminusOne) :
    (fderiv ℂ (fun p => S p/B p) 0) h = (h.val n-h.val (-(n : ℤ)))/2 := by
  have hS0 := hillDirichletSheet_hminus_free_zero h0q h0r n hn S hSM
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hsign : (-1 : ℂ)^n ≠ 0 := pow_ne_zero _ (by norm_num)
  have hBv : B 0 = I*(-1 : ℂ)^n/((n : ℂ)*Real.pi) :=
    hB0.trans (hillDeflatedEnergyCanonicalRoot_free_value h0q h0r n hn)
  have hBn : B 0 ≠ 0 := by
    rw [hBv]
    exact div_ne_zero (mul_ne_zero I_ne_zero hsign) (mul_ne_zero hn0 (ofReal_ne_zero.mpr Real.pi_ne_zero))
  have hInv := hB.inv hBn
  have hP := hS.differentiableAt.hasFDerivAt.mul hInv.differentiableAt.hasFDerivAt
  have hPd : HasFDerivAt (fun p => S p*(B p)⁻¹) ((B 0)⁻¹ • fderiv ℂ S 0) 0 := by
    convert! hP using 1
    ext v
    simp [hS0]
  have he : (fun p => S p/B p) = (fun p => S p*(B p)⁻¹) := by
    funext p
    exact div_eq_mul_inv _ _
  rw [he,hPd.fderiv,smul_apply,smul_eq_mul,
    hillDirichletSheet_hminus_free_fourier_fderiv h0q h0r n hn S hS hSM h,hBv]
  field_simp [hsign,hn0,Real.pi_ne_zero,I_ne_zero]
  ring_nf
  simp only [I_sq]
  ring

/-- The ACTUAL scaled original sheet has a constructed H-minus-one germ
with its exact antisymmetric Fourier differential at every free positive
gap. The analytic moving deflated root and physical matching are supplied
by the original intrinsic contour charts. -/
theorem exists_hillFree_scaledDirichletSheet_hminus_fourier_germ (n : ℕ+) :
    ∃ T : PeriodOneHminusOne → ℂ, AnalyticAt ℂ T 0 ∧ T 0 = 0 ∧
      (∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨0,h0q,h0r⟩ : RealPeriodOneHillPotential),
        T (hillOriginalHminusSource p.val) = hillDirichletSheetRoot
          (SpectralWeight.one.toCoeff p.val) (hillDirichletEnergy p.val p.property.1 p.property.2 n n.pos)/
            hillDeflatedEnergyCanonicalRoot p.val p.property.1 p.property.2 n
              (hillDirichletEnergy p.val p.property.1 p.property.2 n n.pos)) ∧
      ∀ h : PeriodOneHminusOne, (fderiv ℂ T 0) h = (h.val n-h.val (-(n : ℤ)))/2 := by
  let Q : RealPeriodOneHillPotential := ⟨0,h0q,h0r⟩
  obtain ⟨a,S,ha,hS,ha0,_,hM,_⟩ := exists_hillFreeDirichletSheet_hminus_fourier_germ h0q h0r n
  have hR : 0 < hillRealGapHalfLength 0 h0q h0r n+hillRealGapCollar 0 h0q h0r n :=
    add_pos_of_nonneg_of_pos (hillRealGapContour_geometry 0 h0q h0r n n.pos).1
      (hillRealGapContour_geometry 0 h0q h0r n n.pos).2.1
  have hEball : (freeHillValue n : ℂ) ∈ ball (hillRealGapCenter 0 h0q h0r n : ℂ)
      (hillRealGapHalfLength 0 h0q h0r n+hillRealGapCollar 0 h0q h0r n) := by
    rw [hillFreeGapCenter h0q h0r n n.pos]
    exact mem_ball_self hR
  have hdom : (a 0,(0 : PeriodOneHminusOne)) ∈ hillHminusIntrinsicDeflatedRootDomain 0 h0q h0r n := by
    rw [ha0]
    simpa only [map_zero] using mem_hillHminusIntrinsicDeflatedRootDomain_base 0 h0q h0r n n.pos _ hEball
  let B : PeriodOneHminusOne → ℂ := fun b => hillHminusIntrinsicDeflatedRoot 0 h0q h0r n (a b,b)
  have hB : AnalyticAt ℂ B 0 :=
    (analyticOnNhd_hillHminusIntrinsicDeflatedRoot 0 h0q h0r n n.pos _ hdom).comp
      (f := fun b : PeriodOneHminusOne => (a b,b)) (ha.prod analyticAt_id)
  have hBn : B 0 ≠ 0 := hillHminusIntrinsicDeflatedRoot_ne_zero 0 h0q h0r n n.pos _ hdom
  have hB0 : B 0 = hillDeflatedEnergyCanonicalRoot 0 h0q h0r n (freeHillValue n : ℂ) := by
    change hillHminusIntrinsicDeflatedRoot 0 h0q h0r n (a 0,0) = _
    rw [ha0]
    simpa only [map_zero] using hillHminusIntrinsicDeflatedRoot_base 0 h0q h0r n n.pos _ hEball
  let T : PeriodOneHminusOne → ℂ := fun b => S b/B b
  have hSM := hM.mono (fun _ hp => hp.2)
  have hS0 := hillDirichletSheet_hminus_free_zero h0q h0r n n.pos S hSM
  refine ⟨T,hS.div hB hBn,?_,?_,?_⟩
  · change S 0/B 0 = 0
    rw [hS0,zero_div]
  · obtain ⟨E,V,hE,hV,hgapE,hQV,hrootmatch⟩ := exists_hillLocalDeflatedComplexRoot_gap_physical_matching
      0 h0q h0r n n.pos
    have hμbase : (freeHillValue n : ℂ) ∈ segment ℝ
        (hillRealLabels 0 h0q h0r (2*(n:ℕ)-1) : ℂ) (hillRealLabels 0 h0q h0r (2*(n:ℕ)) : ℂ) := by
      obtain ⟨hl,hu⟩ := hillFreeGapEndpoints h0q h0r n n.pos
      rw [hl,hu]
      exact left_mem_segment ℝ _ _
    have hμE : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 Q, a (hillOriginalHminusSource p.val) ∈ E := by
      have haQ : AnalyticAt ℂ a (hillOriginalHminusSource Q.val) := by simpa only [Q,map_zero] using ha
      have hc : ContinuousAt (fun p : RealPeriodOneHillPotential => a (hillOriginalHminusSource p.val)) Q :=
        haQ.continuousAt.comp (f := fun p : RealPeriodOneHillPotential => hillOriginalHminusSource p.val)
          (hillOriginalHminusSource.continuous.comp continuous_subtype_val).continuousAt
      apply hc.preimage_mem_nhds (hE.mem_nhds ?_)
      simpa only [Q,map_zero,ha0] using hgapE hμbase
    filter_upwards [hM,hμE,hV.mem_nhds hQV] with p hp hpE hpV
    have hroot : B (hillOriginalHminusSource p.val) =
        hillDeflatedEnergyCanonicalRoot p.val p.property.1 p.property.2 n (a (hillOriginalHminusSource p.val)) := by
      dsimp only [B]
      rw [hillHminusIntrinsicDeflatedRoot_original_source 0 h0q h0r n p.val p.property.1]
      exact (hrootmatch p hpV _ hpE).2.2
    dsimp only [T]
    rw [hroot,hp.1,hp.2]
  · exact hillFree_scaledDirichletSheet_fourier_fderiv h0q h0r n n.pos S B hS hB hSM hB0

end NLS.KdV
