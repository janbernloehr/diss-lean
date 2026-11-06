import NLS.KdV.PhysicalMiuraFrequencyChart
import NLS.ZakharovShabat.SourceDividedSecondMomentPacket

/-! Actual physical Miura frequency charts retaining a full ellr packet
of the corrections divided by their own index. The physical numerator,
primitive, shifted pullback and Jacobian are the SAME calibrated data. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.KdV

structure PhysicalMiuraLpFrequencyChart (r : ℝ≥0∞) [Fact (1 ≤ r)] where
  physical : PhysicalMiuraFrequencyChart
  packet : PeriodOneHminusOne → Coeff r
  analytic_packet : AnalyticOnNhd ℂ packet physical.domain
  bound : ℝ
  bound_pos : 0<bound
  norm_packet : ∀ q∈physical.domain, ‖packet q‖≤bound
  nonpositive : ∀ q∈physical.domain, ∀ j : ℤ, j≤0 → packet q j=0
  positive : ∀ q∈physical.domain, ∀ n : ℕ+, packet q (n : ℤ)=physical.correction n q/(n : ℂ)

theorem exists_physicalMiuraLpFrequencyChart {r : ℝ≥0∞} [Fact (1 ≤ r)] (hr : 1<r)
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) (M : ℝ) :
    ∃ B : PhysicalMiuraLpFrequencyChart r, q∈B.physical.domain ∧ M<B.physical.shift := by
  obtain ⟨P,c,hc,hMc,hshift,hqP,hreal,houtside,H⟩ :=
    exists_hillHminusPsiChart_real_form_outside_shift q hq M
  obtain ⟨W,A,U₀,hU₀,_hU₀c,hrealU₀,hsub₀,hsum,ha,hbound₀⟩ :=
    P.family.exists_weighted_secondMoment_atlas H
  obtain ⟨U₁,hU₁,hrealU₁,hsub₁,hpacket,hval,hbound₁⟩ :=
    A.exists_analytic_dividedSecondMomentPacket H.angular_extension P.family.domain_open P.family.real_subset hr
  let F : PeriodOneHminusOne → CoeffPair 2 := fun a => hillMiuraDiagonal (P.miura.lift a)
  have hF : AnalyticOnNhd ℂ F P.miura.domain := by
    intro a ha
    exact (hillMiuraDiagonal.analyticAt _).comp (P.miura.lift_analytic a ha)
  have hqr : F q∈realTypeSourceLocus 2 :=
    isRealType_hillMiuraDiagonal ⟨P.miura.lift q,hreal q hqP.1 hq⟩
  obtain ⟨S₀,hS₀,hqS₀,hS₀U,C,hC,hCb⟩ := hbound₀ (F q) (hrealU₀ hqr)
  obtain ⟨S₁,hS₁,hqS₁,hS₁U,K,hK,hKb⟩ := hbound₁ (F q) (hrealU₁ hqr)
  let T := P.miura.domain∩F ⁻¹' (S₀∩S₁)
  have hT : IsOpen T := hF.continuousOn.isOpen_inter_preimage P.miura.domain_open (hS₀.inter hS₁)
  have hTP : T⊆P.source := fun a ha => ⟨ha.1,(hsub₀ (hS₀U ha.2.1)).2⟩
  let B : PhysicalMiuraFrequencyChart :=
    ⟨P,c,hc,hshift,W,A,T,hT,hTP,hreal,houtside,
      (fun n a haT => (ha n (F a) (hS₀U haT.2.1)).comp (hF a haT.1)),
      (fun a haT n => hsum (F a) (hS₀U haT.2.1) n),C,hC,
      (fun a haT n => hCb (F a) haT.2.1 n)⟩
  let packet := fun a => (-12 : ℂ) • A.positiveDividedSecondMomentPacket r (F a)
  have hpa : AnalyticOnNhd ℂ packet T := by
    intro a haT
    exact (analyticAt_const (v := (-12 : ℂ))).smul ((hpacket (F a) (hS₁U haT.2.2)).comp (hF a haT.1))
  have hpn (a : PeriodOneHminusOne) (haT : a∈T) : ‖packet a‖≤12*K+1 := by
    change ‖(-12 : ℂ) • A.positiveDividedSecondMomentPacket r (F a)‖≤_
    rw [norm_smul]
    norm_num only [norm_neg,Complex.norm_ofNat]
    linarith [mul_le_mul_of_nonneg_left (hKb (F a) haT.2.2) (by norm_num : (0 : ℝ)≤12)]
  refine ⟨⟨B,packet,hpa,12*K+1,by positivity,hpn,?_,?_⟩,⟨hqP.1,hqS₀,hqS₁⟩,hMc⟩
  · intro a haT j hj
    change (-12 : ℂ)*A.positiveDividedSecondMomentPacket r (F a) j=0
    rw [hval (F a) (hS₁U haT.2.2) j,if_neg (by omega),mul_zero]
  · intro a haT n
    change (-12 : ℂ)*A.positiveDividedSecondMomentPacket r (F a) (n : ℤ)=_
    rw [hval (F a) (hS₁U haT.2.2) (n : ℤ),if_pos (by exact_mod_cast n.pos : (0 : ℤ)<n)]
    change (-12 : ℂ)*(A.weightedSecondMomentSum (n : ℤ) (F a)/(n : ℂ))=
      (-12*A.weightedSecondMomentSum (n : ℤ) (F a))/(n : ℂ)
    ring

end NLS.KdV
