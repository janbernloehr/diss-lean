import NLS.KdV.PhysicalOffDiagonalFrequencyEstimates
import NLS.KdV.PhysicalSharpOffDiagonalTransport

/-! Sharp off-diagonal decay for the ACTUAL physical KdV frequency
at every original native source -1<=s<=-1/3. The big-O bound is uniform
on a full complex native neighborhood; little-o is pointwise there. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.KdV

theorem exists_physicalMiuraFrequencyChart_with_sharp_offDiagonal_decay
    (t : ℝ) (ht : 0≤t) (ht1 : t≤2/3)
    (q : WeightedCoeff (Weight.sobolev (t-1)) 2)
    (hq : IsRealPeriodOneHminusOne (periodOneSobolevImageInclusion t ht q)) :
    ∃ B : PhysicalMiuraFrequencyChart,
      ∃ T : Set (WeightedCoeff (Weight.sobolev (t-1)) 2), IsOpen T ∧ q∈T ∧
        T⊆periodOneSobolevImageInclusion t ht ⁻¹' B.domain ∧
        ∃ K : ℝ, 0≤K ∧
          (∀ a∈T, ∀ n : ℕ+, Weight.sobolev (3*t-1) (n : ℤ)*
            ‖B.offDiagonalCorrection n (periodOneSobolevImageInclusion t ht a)‖≤K) ∧
          (t<2/3 → ∀ a∈T,
            Tendsto (fun n : ℕ => Weight.sobolev (3*t-1) ((n+1 : ℕ) : ℤ)*
              ‖B.offDiagonalCorrection ⟨n+1,by omega⟩ (periodOneSobolevImageInclusion t ht a)‖)
              atTop (𝓝 0)) := by
  let J := periodOneSobolevImageInclusion t ht
  obtain ⟨C,c,hc,hshift,hqC,hreal,houtside,_hlabels,_hcoeff,hstrong⟩ :=
    exists_hillHminus_real_native_all_sobolev_analytic_Miura_germs (J q) hq
  obtain ⟨A₀,H⟩ := exists_miuraHillPsiFamily_with_original_estimates
  let P : HillHminusPsiChart := ⟨C,A₀⟩
  obtain ⟨W,A,U₀,hU₀,_hU₀c,hrealU₀,hsub₀,hsum,ha,hbound₀⟩ :=
    P.family.exists_weighted_secondMoment_atlas H
  let F := fun a : PeriodOneHminusOne => hillMiuraDiagonal (C.lift a)
  have hF : AnalyticOnNhd ℂ F C.domain := fun a ha =>
    (hillMiuraDiagonal.analyticAt _).comp (C.lift_analytic a ha)
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
  obtain ⟨V,hV,hqV,g,hga,hg⟩ := hstrong t ht q hqC
  let N := hillMiuraNormalizedSobolevSource t
  let L := normalizedWeightedSourceCLM (p := 2) (sourceSobolevSpectralWeight t ht)
  let η := fun a => N (g a)
  have hη : AnalyticOnNhd ℂ η V := fun a ha => (N.analyticAt _).comp (hga a ha)
  have he (a : WeightedCoeff (Weight.sobolev (t-1)) 2) (haV : a∈V) : L (η a)=F (J a) := by
    rw [normalizedWeightedSourceCLM_apply,normalizedWeightedSource_hillMiuraNormalizedSobolevSource]
    rw [(hg a haV).2,hillHminusNativeSobolevMiuraLift_toL2_of_mem C t ht a (hg a haV).1]
  have hηqr : η q∈realTypeSourceLocus 2 := by
    apply isRealType_hillMiuraNormalizedSobolevSource t ht
    rw [(hg q hqV).2,hillHminusNativeSobolevMiuraLift_toL2_of_mem C t ht q (hg q hqV).1]
    exact hreal _ hqC hq
  obtain ⟨T,hT,hqT,hsub,K,hK,hb,hd⟩ := B.exists_sharp_offDiagonal_decay_of_native_parameterization
    H t ht ht1 J q (show J q∈B.domain from ⟨hqC,hqS₀⟩) V hV hqV η hη hηqr he
  exact ⟨B,T,hT,hqT,hsub,K,hK,hb,hd⟩

end NLS.KdV
