import NLS.KdV.PhysicalSobolevLpFrequencyChart
import NLS.ZakharovShabat.SourceOffDiagonalMomentGain
import NLS.KdV.PhysicalOffDiagonalFrequency

/-! At every real native intermediate Hill source, the ACTUAL
physical off-diagonal moment correction has a strictly stronger
weighted ell1 analytic germ with a full complex vector norm bound. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.KdV

structure PhysicalOffDiagonalFrequencyChart (β t ε : ℝ) (ht : 0<t) where
  physical : PhysicalMiuraFrequencyChart
  domain : Set (WeightedCoeff (Weight.sobolev (t-1)) 2)
  domain_open : IsOpen domain
  domain_subset : domain⊆periodOneSobolevImageInclusion t ht.le ⁻¹' physical.domain
  packet : WeightedCoeff (Weight.sobolev (t-1)) 2 → Coeff 1
  analytic_packet : AnalyticOnNhd ℂ packet domain
  bound : ℝ
  bound_pos : 0<bound
  norm_packet : ∀ q∈domain, ‖packet q‖≤bound
  nonpositive : ∀ q∈domain, ∀ j : ℤ, j≤0 → packet q j=0
  positive : ∀ q∈domain, ∀ n : ℕ+,
    packet q (n : ℤ)=(Weight.sobolev (-(β-ε)) (n : ℤ) : ℂ)*physical.offDiagonalCorrection n (periodOneSobolevImageInclusion t ht.le q)

theorem exists_physicalOffDiagonalFrequencyChart
    (β t : ℝ) (hβ : 0<β) (hβ1 : β<1) (ht : 0<t) (hβt : 2*t=1-β)
    (q : WeightedCoeff (Weight.sobolev (t-1)) 2)
    (hq : IsRealPeriodOneHminusOne (periodOneSobolevImageInclusion t ht.le q)) :
    ∃ ε : ℝ, 0<ε ∧ ε<β ∧ ∃ B : PhysicalOffDiagonalFrequencyChart β t ε ht, q∈B.domain := by
  let J := periodOneSobolevImageInclusion t ht.le
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
  obtain ⟨V,hV,hqV,g,hga,hg⟩ := hstrong t ht.le q hqC
  let N := hillMiuraNormalizedSobolevSource t
  let L := normalizedWeightedSourceCLM (p := 2) (sourceSobolevSpectralWeight t ht.le)
  have he (a : WeightedCoeff (Weight.sobolev (t-1)) 2) (haV : a∈V) : L (N (g a))=F (J a) := by
    rw [normalizedWeightedSourceCLM_apply,normalizedWeightedSource_hillMiuraNormalizedSobolevSource]
    rw [(hg a haV).2,hillHminusNativeSobolevMiuraLift_toL2_of_mem C t ht.le a (hg a haV).1]
  have hNg : AnalyticOnNhd ℂ (fun a => N (g a)) V := fun a ha => (N.analyticAt _).comp (hga a ha)
  have hNqr : N (g q)∈realTypeSourceLocus 2 := by
    apply isRealType_hillMiuraNormalizedSobolevSource t ht.le
    rw [(hg q hqV).2,hillHminusNativeSobolevMiuraLift_toL2_of_mem C t ht.le q (hg q hqV).1]
    exact hreal _ hqC hq
  obtain ⟨ε,hε,hεβ,U₁,hU₁,hrealU₁,_hsub₁,hpacket,hval,hbound₁⟩ :=
    A.exists_offDiagonalSecondMoment_gain β t hβ hβ1 ht hβt
      H.angular_extension P.family.domain_open P.family.real_subset
  obtain ⟨S₁,hS₁,hqS₁,hS₁U,K₁,hK₁,hK₁b⟩ := hbound₁ (N (g q)) (hrealU₁ hNqr)
  let T := (V∩(fun a => N (g a)) ⁻¹' S₁)∩J ⁻¹' T₀
  have hT : IsOpen T := (hNg.continuousOn.isOpen_inter_preimage hV hS₁).inter (hT₀.preimage J.continuous)
  let packet := fun a => (-12 : ℂ) • A.negativeWeightedOffDiagonalSecondMomentPacket (β-ε) (L (N (g a)))
  have hpa : AnalyticOnNhd ℂ packet T := by
    intro a haT
    exact (analyticAt_const (v := (-12 : ℂ))).smul
      ((hpacket _ (hS₁U haT.1.2)).comp (f := fun a => N (g a)) (hNg a haT.1.1))
  refine ⟨ε,hε,hεβ,⟨B,T,hT,(fun _ ha => ha.2),packet,hpa,12*K₁+1,by positivity,?_,?_,?_⟩,
    ⟨⟨hqV,hqS₁⟩,hqC,hqS₀⟩⟩
  · intro a haT
    change ‖(-12 : ℂ) • A.negativeWeightedOffDiagonalSecondMomentPacket (β-ε) (L (N (g a)))‖≤_
    rw [norm_smul]
    norm_num only [norm_neg,Complex.norm_ofNat]
    linarith [mul_le_mul_of_nonneg_left (hK₁b _ haT.1.2) (by norm_num : (0 : ℝ)≤12)]
  · intro a haT j hj
    change (-12 : ℂ)*A.negativeWeightedOffDiagonalSecondMomentPacket (β-ε) (L (N (g a))) j=0
    rw [hval _ (hS₁U haT.1.2) j,if_neg (by omega),mul_zero,mul_zero]
  · intro a haT n
    change (-12 : ℂ)*A.negativeWeightedOffDiagonalSecondMomentPacket (β-ε) (L (N (g a))) (n : ℤ)=_
    rw [hval _ (hS₁U haT.1.2) (n : ℤ),if_pos (by exact_mod_cast n.pos : (0 : ℤ)<n),he a haT.1.1]
    change (-12 : ℂ)*((Weight.sobolev (-(β-ε)) (n : ℤ) : ℂ)*
      (A.weightedSecondMomentSum (n : ℤ) (F (J a))-(n : ℂ)*
        (A.moment (n : ℤ) (n : ℤ) 2 (F (J a))-A.moment (n : ℤ) (-(n : ℤ)) 2 (F (J a)))))=
      (Weight.sobolev (-(β-ε)) (n : ℤ) : ℂ)*((-12 : ℂ)*
        (A.weightedSecondMomentSum (n : ℤ) (F (J a))-(n : ℂ)*
          (A.moment (n : ℤ) (n : ℤ) 2 (F (J a))-A.moment (n : ℤ) (-(n : ℤ)) 2 (F (J a)))))
    ring

end NLS.KdV
