import NLS.KdV.PhysicalMiuraFrequencyChart
import NLS.KdV.HillHminusNativeSobolevMiuraLift
import NLS.KdV.HillMiuraSobolevNormalizedSource
import NLS.ZakharovShabat.SourceSobolevSecondMomentPacket

/-! At every real native H^(-1/2) source the ACTUAL physical KdV
corrections form an unweighted ellr-valued complex analytic germ, for
every r>1. The same rough Miura chart, physical numerator, primitive and
Jacobian calibrate every coefficient. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.KdV

def hillMiuraNormalizedSobolevSource (t : ℝ) :
    WeightedCoeff (Weight.sobolev t) 2 →L[ℂ] CoeffPair 2 :=
  hillMiuraDiagonal.comp
    (WeightedCoeff.weightIsometry (Weight.sobolev t) 2).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem hillMiuraNormalizedSobolevSource_fst
    (t : ℝ) (a : WeightedCoeff (Weight.sobolev t) 2) (n : ℤ) :
    (hillMiuraNormalizedSobolevSource t a).fst n=(Weight.sobolev t n : ℂ)*a.val n := by
  change (hillMiuraDiagonal (WeightedCoeff.weightEquiv (Weight.sobolev t) 2 a)).fst n=_
  rw [hillMiuraDiagonal_fst]
  rfl

@[simp] theorem hillMiuraNormalizedSobolevSource_snd
    (t : ℝ) (a : WeightedCoeff (Weight.sobolev t) 2) (n : ℤ) :
    (hillMiuraNormalizedSobolevSource t a).snd n=(Weight.sobolev t n : ℂ)*a.val n := by
  change (hillMiuraDiagonal (WeightedCoeff.weightEquiv (Weight.sobolev t) 2 a)).snd n=_
  rw [hillMiuraDiagonal_snd]
  rfl

theorem normalizedWeightedSource_hillMiuraNormalizedSobolevSource
    (t : ℝ) (ht : 0≤t) (a : WeightedCoeff (Weight.sobolev t) 2) :
    normalizedWeightedSource (sourceSobolevSpectralWeight t ht)
      (hillMiuraNormalizedSobolevSource t a)=
        hillMiuraDiagonal (WeightedCoeff.sobolevToL2 ht a) := by
  apply (CoeffPair.toMax 2).injective
  apply Prod.ext
  · ext n
    change (normalizedWeightedSource _ _).fst n=(hillMiuraDiagonal _).fst n
    rw [normalizedWeightedSource_fst,hillMiuraNormalizedSobolevSource_fst,
      sourceSobolevSpectralWeight_even,hillMiuraDiagonal_fst,WeightedCoeff.sobolevToL2_apply,
      mul_div_cancel_left₀ _ (Weight.complex_ne_zero (Weight.sobolev t) n)]
  · ext n
    change (normalizedWeightedSource _ _).snd n=(hillMiuraDiagonal _).snd n
    rw [normalizedWeightedSource_snd,hillMiuraNormalizedSobolevSource_snd,
      sourceSobolevSpectralWeight_even,hillMiuraDiagonal_snd,WeightedCoeff.sobolevToL2_apply,
      mul_div_cancel_left₀ _ (Weight.complex_ne_zero (Weight.sobolev t) n)]

theorem isRealType_hillMiuraNormalizedSobolevSource
    (t : ℝ) (ht : 0≤t) (a : WeightedCoeff (Weight.sobolev t) 2)
    (hr : periodOneL2Conjugation (WeightedCoeff.sobolevToL2 ht a)=WeightedCoeff.sobolevToL2 ht a) :
    hillMiuraNormalizedSobolevSource t a∈realTypeSourceLocus 2 := by
  have ha (n : ℤ) : a.val (-n)=conj (a.val n) := by
    simpa only [WeightedCoeff.sobolevToL2_apply] using
      (periodOneL2Conjugation_fixed_iff _).mp hr n
  have hw (n : ℤ) :
      WeightedCoeff.weightEquiv (Weight.sobolev t) 2 a (-n)=
        conj (WeightedCoeff.weightEquiv (Weight.sobolev t) 2 a n) := by
    simp only [WeightedCoeff.weightEquiv_apply,Weight.sobolev_neg,map_mul,Complex.conj_ofReal,ha n]
  exact isRealType_hillMiuraDiagonal ⟨_,hw⟩

abbrev HalfSobolevHillSource := WeightedCoeff (Weight.sobolev ((1/2 : ℝ)-1)) 2
abbrev halfSobolevHillInclusion := periodOneSobolevImageInclusion (1/2) (by norm_num)

structure PhysicalSobolevLpFrequencyChart (r : ℝ≥0∞) [Fact (1 ≤ r)] where
  physical : PhysicalMiuraFrequencyChart
  domain : Set HalfSobolevHillSource
  domain_open : IsOpen domain
  domain_subset : domain⊆halfSobolevHillInclusion ⁻¹' physical.domain
  packet : HalfSobolevHillSource → Coeff r
  analytic_packet : AnalyticOnNhd ℂ packet domain
  bound : ℝ
  bound_pos : 0<bound
  norm_packet : ∀ q∈domain, ‖packet q‖≤bound
  nonpositive : ∀ q∈domain, ∀ j : ℤ, j≤0 → packet q j=0
  positive : ∀ q∈domain, ∀ n : ℕ+,
    packet q (n : ℤ)=physical.correction n (halfSobolevHillInclusion q)

theorem exists_physicalSobolevLpFrequencyChart {r : ℝ≥0∞} [Fact (1 ≤ r)] (hr : 1<r)
    (q : HalfSobolevHillSource) (hq : IsRealPeriodOneHminusOne (halfSobolevHillInclusion q)) :
    ∃ B : PhysicalSobolevLpFrequencyChart r, q∈B.domain := by
  let J := halfSobolevHillInclusion
  obtain ⟨C,c,hc,hshift,hqC,hreal,houtside,_hlabels,_hcoeff,hstrong⟩ :=
    exists_hillHminus_real_native_all_sobolev_analytic_Miura_germs (J q) hq
  obtain ⟨A₀,H⟩ := exists_miuraHillPsiFamily_with_original_estimates
  let P : HillHminusPsiChart := ⟨C,A₀⟩
  obtain ⟨W,A,U₀,hU₀,_hU₀c,hrealU₀,hsub₀,hsum,ha,hbound₀⟩ :=
    P.family.exists_weighted_secondMoment_atlas H
  let F : PeriodOneHminusOne → CoeffPair 2 := fun a => hillMiuraDiagonal (C.lift a)
  have hF : AnalyticOnNhd ℂ F C.domain := by
    intro a ha
    exact (hillMiuraDiagonal.analyticAt _).comp (C.lift_analytic a ha)
  have hqr : F (J q)∈realTypeSourceLocus 2 :=
    isRealType_hillMiuraDiagonal ⟨C.lift (J q),(periodOneL2Conjugation_fixed_iff _).mp (hreal _ hqC hq)⟩
  obtain ⟨S₀,hS₀,hqS₀,hS₀U,K₀,hK₀,hK₀b⟩ := hbound₀ (F (J q)) (hrealU₀ hqr)
  let T₀ := C.domain∩F ⁻¹' S₀
  have hT₀ : IsOpen T₀ := hF.continuousOn.isOpen_inter_preimage C.domain_open hS₀
  let B : PhysicalMiuraFrequencyChart :=
    ⟨P,c,hc,hshift,W,A,T₀,hT₀,(fun a ha => ⟨ha.1,(hsub₀ (hS₀U ha.2)).2⟩),
      (fun a ha hr => (periodOneL2Conjugation_fixed_iff _).mp (hreal a ha hr)),houtside,
      (fun n a haT => (ha n (F a) (hS₀U haT.2)).comp (hF a haT.1)),
      (fun a haT n => hsum (F a) (hS₀U haT.2) n),K₀,hK₀,
      (fun a haT n => hK₀b (F a) haT.2 n)⟩
  obtain ⟨V,hV,hqV,g,hga,hg⟩ := hstrong (1/2) (by norm_num) q hqC
  let N := hillMiuraNormalizedSobolevSource (1/2)
  let L := normalizedWeightedSourceCLM (p := 2) (sourceSobolevSpectralWeight (1/2) (by norm_num))
  have he (a : HalfSobolevHillSource) (haV : a∈V) : L (N (g a))=F (J a) := by
    rw [normalizedWeightedSourceCLM_apply,normalizedWeightedSource_hillMiuraNormalizedSobolevSource]
    rw [(hg a haV).2,hillHminusNativeSobolevMiuraLift_toL2_of_mem C (1/2) (by norm_num) a (hg a haV).1]
  have hNg : AnalyticOnNhd ℂ (fun a => N (g a)) V := fun a ha => (N.analyticAt _).comp (hga a ha)
  have hNqr : N (g q)∈realTypeSourceLocus 2 := by
    apply isRealType_hillMiuraNormalizedSobolevSource (1/2) (by norm_num)
    rw [(hg q hqV).2,hillHminusNativeSobolevMiuraLift_toL2_of_mem C (1/2) (by norm_num) q (hg q hqV).1]
    exact hreal _ hqC hq
  obtain ⟨U₁,hU₁,hrealU₁,_hsub₁,hpacket,hval,hbound₁⟩ :=
    A.exists_analytic_sobolevSecondMomentPacket H.angular_extension P.family.domain_open P.family.real_subset hr
  obtain ⟨S₁,hS₁,hqS₁,hS₁U,K₁,hK₁,hK₁b⟩ := hbound₁ (N (g q)) (hrealU₁ hNqr)
  let T := (V∩(fun a => N (g a)) ⁻¹' S₁)∩J ⁻¹' T₀
  have hT : IsOpen T := (hNg.continuousOn.isOpen_inter_preimage hV hS₁).inter (hT₀.preimage J.continuous)
  let packet := fun a => (-12 : ℂ) • A.positiveSecondMomentPacket r (L (N (g a)))
  have hpa : AnalyticOnNhd ℂ packet T := by
    intro a haT
    exact (analyticAt_const (v := (-12 : ℂ))).smul
      ((hpacket _ (hS₁U haT.1.2)).comp (f := fun a => N (g a)) (hNg a haT.1.1))
  refine ⟨⟨B,T,hT,(fun _ ha => ha.2),packet,hpa,12*K₁+1,by positivity,?_,?_,?_⟩,
    ⟨⟨hqV,hqS₁⟩,hqC,hqS₀⟩⟩
  · intro a haT
    change ‖(-12 : ℂ) • A.positiveSecondMomentPacket r (L (N (g a)))‖≤_
    rw [norm_smul]
    norm_num only [norm_neg,Complex.norm_ofNat]
    linarith [mul_le_mul_of_nonneg_left (hK₁b _ haT.1.2) (by norm_num : (0 : ℝ)≤12)]
  · intro a haT j hj
    change (-12 : ℂ)*A.positiveSecondMomentPacket r (L (N (g a))) j=0
    rw [hval _ (hS₁U haT.1.2) j,if_neg (by omega),mul_zero]
  · intro a haT n
    change (-12 : ℂ)*A.positiveSecondMomentPacket r (L (N (g a))) (n : ℤ)=_
    rw [hval _ (hS₁U haT.1.2) (n : ℤ),if_pos (by exact_mod_cast n.pos : (0 : ℤ)<n),he a haT.1.1]
    rfl

end NLS.KdV
