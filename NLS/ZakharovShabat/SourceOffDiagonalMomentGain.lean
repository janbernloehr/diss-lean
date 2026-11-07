import NLS.ZakharovShabat.SourceOffDiagonalSecondMomentSmoothing
import NLS.SequenceSpaces.CompactSobolevInclusion
import NLS.SequenceSpaces.AnalyticLinearPacketTransport

/-! A strict weighted gain for the actual paired off-diagonal moments,
and compact derivatives after their literal inclusion in the original
target norm. The source is the full complex native source topology. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {W V : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

theorem SourceAbelianMomentAtlas.exists_offDiagonalSecondMoment_gain
    (A : SourceAbelianMomentAtlas (by norm_num) (by norm_num) W s)
    (a t : ℝ) (ha0 : 0<a) (ha1 : a<1) (ht : 0<t) (hat : 2*t=1-a)
    (hs : SourcePsiSquaredGapComplexExtension (by norm_num) (by norm_num) V s)
    (hV : IsOpen V) (hrealV : realTypeSourceLocus 2⊆V) :
    ∃ ε : ℝ, 0<ε ∧ ε<a ∧
      let w := sourceSobolevSpectralWeight t ht.le
      let L := normalizedWeightedSourceCLM (p := 2) w
      ∃ U : Set (CoeffPair 2), IsOpen U ∧ realTypeSourceLocus 2⊆U ∧ U⊆L ⁻¹' (A.domain∩V) ∧
        AnalyticOnNhd ℂ (fun φ => A.negativeWeightedOffDiagonalSecondMomentPacket (a-ε) (L φ)) U ∧
        (∀ φ∈U, ∀ n : ℤ, A.negativeWeightedOffDiagonalSecondMomentPacket (a-ε) (L φ) n=
          (Weight.sobolev (-(a-ε)) n : ℂ)*(if 0<n then A.weightedSecondMomentSum n (L φ)-
            (n : ℂ)*(A.moment n n 2 (L φ)-A.moment n (-n) 2 (L φ)) else 0)) ∧
        ∀ φ∈U, ∃ T : Set (CoeffPair 2), IsOpen T ∧ φ∈T ∧ T⊆U ∧
          ∃ K : ℝ, 0≤K ∧ ∀ ψ∈T, ‖A.negativeWeightedOffDiagonalSecondMomentPacket (a-ε) (L ψ)‖≤K := by
  let ε := min t a/4
  have hε : 0<ε := div_pos (lt_min ht ha0) (by norm_num)
  have haε : 4*ε≤a := by dsimp only [ε];linarith [min_le_right t a]
  have htε : 4*ε≤t := by dsimp only [ε];linarith [min_le_left t a]
  refine ⟨ε,hε,by linarith,?_⟩
  exact A.exists_analytic_negativeWeightedOffDiagonalSecondMomentPacket a (a-ε) (a-2*ε) t
    (lt_trans (sub_lt_self a hε) ha1) (by linarith) (by linarith) ht hat (by linarith) hs hV hrealV

theorem SourceAbelianMomentAtlas.exists_raw_offDiagonalSecondMoment_compact_germ
    (A : SourceAbelianMomentAtlas (by norm_num) (by norm_num) W s)
    (a t : ℝ) (ha0 : 0<a) (ha1 : a<1) (ht : 0<t) (hat : 2*t=1-a)
    (hs : SourcePsiSquaredGapComplexExtension (by norm_num) (by norm_num) V s)
    (hV : IsOpen V) (hrealV : realTypeSourceLocus 2⊆V) :
    ∃ ε : ℝ, ∃ hε : 0<ε, ε<a ∧
      let w := sourceSobolevSpectralWeight t ht.le
      let L := normalizedWeightedSourceCLM (p := 2) w
      ∃ U : Set (CoeffPair 2), ∃ P : CoeffPair 2 → WeightedCoeff (Weight.sobolev (-(a-ε))) 1,
        IsOpen U ∧ realTypeSourceLocus 2⊆U ∧ U⊆L ⁻¹' (A.domain∩V) ∧ AnalyticOnNhd ℂ P U ∧
        (∀ φ∈U, ∀ n : ℤ, (P φ).val n=if 0<n then A.weightedSecondMomentSum n (L φ)-
          (n : ℂ)*(A.moment n n 2 (L φ)-A.moment n (-n) 2 (L φ)) else 0) ∧
        ∀ φ∈U, IsCompactOperator (fderiv ℂ (fun ψ =>
          WeightedCoeff.sobolevInclusion (by linarith : -a≤-(a-ε)) (P ψ)) φ) := by
  obtain ⟨ε,hε,hεa,U,hU,hrealU,hsub,hpa,hval,_hbound⟩ :=
    A.exists_offDiagonalSecondMoment_gain a t ha0 ha1 ht hat hs hV hrealV
  refine ⟨ε,hε,hεa,?_⟩
  intro w L
  let K := (WeightedCoeff.weightIsometry (Weight.sobolev (-(a-ε))) 1).symm.toContinuousLinearEquiv.toContinuousLinearMap
  obtain ⟨T,P,hT,hrealT,hP,hTU,hPV⟩ := exists_analytic_linear_packet_transport
    (ContinuousLinearMap.id ℂ (CoeffPair 2)) K U
    (fun φ => A.negativeWeightedOffDiagonalSecondMomentPacket (a-ε) (L φ)) hU hpa
    (realTypeSourceLocus 2) (fun φ hφ => hrealU hφ)
  refine ⟨T,P,hT,hrealT,(fun φ hφ => hsub (hTU φ hφ)),hP,?_,?_⟩
  · intro φ hφ n
    rw [hPV φ hφ]
    change A.negativeWeightedOffDiagonalSecondMomentPacket (a-ε) (L φ) n/
      (Weight.sobolev (-(a-ε)) n : ℂ)=_
    rw [hval φ (hTU φ hφ) n,mul_div_cancel_left₀ _ (Weight.complex_ne_zero _ _)]
  · intro φ hφ
    exact isCompactOperator_fderiv_compact_clm
      (WeightedCoeff.sobolevInclusion (by linarith : -a≤-(a-ε)))
      (WeightedCoeff.isCompactOperator_sobolevInclusion_strict (by linarith : -a < -(a-ε)))
      P φ (hP φ hφ).differentiableAt

end NLS.ZakharovShabat
