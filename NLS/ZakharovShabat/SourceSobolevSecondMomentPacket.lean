import NLS.ZakharovShabat.SourceDividedSecondMomentPacket
import NLS.ZakharovShabat.SourceWeightedGapBound
import NLS.ZakharovShabat.SourceSection14WeightedMembership
import NLS.SequenceSpaces.WeightedCubicFrequencyPacket
import NLS.SequenceSpaces.SobolevHomogeneous

/-! The actual index-weighted second moments give an UNDIVIDED ellr
packet on normalized H^(1/2) sources. A common complex neighborhood
bounds the whole packet, retaining the same numerator and gap branch. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {W V : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
variable {r : ℝ≥0∞} [Fact (1 ≤ r)]

def SourceAbelianMomentAtlas.positiveSecondMomentPacket
    (A : SourceAbelianMomentAtlas (by norm_num) (by norm_num) W s)
    (r : ℝ≥0∞) (ψ : CoeffPair 2) : Coeff r :=
  Coeff.ofFunctionOrZero r (Coeff.positiveWeightedCubicSums (fun n k => A.moment n k 2 ψ))

theorem SourceAbelianMomentAtlas.exists_analytic_sobolevSecondMomentPacket
    (A : SourceAbelianMomentAtlas (by norm_num) (by norm_num) W s)
    (hs : SourcePsiSquaredGapComplexExtension (by norm_num) (by norm_num) V s)
    (hV : IsOpen V) (hrealV : realTypeSourceLocus 2⊆V) (hr : 1<r) :
    let w := sourceSobolevSpectralWeight (1/2) (by norm_num)
    let L := normalizedWeightedSourceCLM (p := 2) w
    ∃ U : Set (CoeffPair 2), IsOpen U ∧ realTypeSourceLocus 2⊆U ∧ U⊆L ⁻¹' (A.domain∩V) ∧
      AnalyticOnNhd ℂ (fun φ => A.positiveSecondMomentPacket r (L φ)) U ∧
      (∀ φ∈U, ∀ n : ℤ, A.positiveSecondMomentPacket r (L φ) n=
        if 0<n then A.weightedSecondMomentSum n (L φ) else 0) ∧
      ∀ φ∈U, ∃ T : Set (CoeffPair 2), IsOpen T ∧ φ∈T ∧ T⊆U ∧
        ∃ K : ℝ, 0≤K ∧ ∀ ψ∈T, ‖A.positiveSecondMomentPacket r (L ψ)‖≤K := by
  intro w L
  obtain ⟨Us,hUs,_hUsc,hrealUs,hUsV,hsum,ha,_hconv,_hlocalUs⟩ :=
    A.exists_analytic_weightedSecondMomentSum hs hV hrealV
  obtain ⟨Ur,hUr,_hUrc,hrealUr,_hUrV,hrows⟩ := A.exists_lemma20_3_refined hs hV hrealV
  let U := L ⁻¹' (Us∩Ur)
  have hU : IsOpen U := (hUs.inter hUr).preimage L.continuous
  let f := fun (φ : CoeffPair 2) => Coeff.positiveWeightedCubicSums (fun n k => A.moment n k 2 (L φ))
  have hlocal (φ : CoeffPair 2) (hφ : φ∈U) :
      ∃ T : Set (CoeffPair 2), IsOpen T ∧ φ∈T ∧ T⊆U ∧
        ∃ K : ℝ, 0≤K ∧ ∀ ψ∈T, ∃ b : Coeff r, (∀ n, b n=f ψ n) ∧ ‖b‖≤K := by
    obtain ⟨ρ,hρ,hball,hcoeff⟩ := hrows (L φ) hφ.2
    obtain ⟨M,hM,hdata⟩ := hcoeff 2 (by norm_num) (by norm_num) (by norm_num)
    obtain ⟨G,hG,hφG,R,hgap⟩ := exists_local_sourceWeightedSquaredGap_bound w L
      (normalizedWeightedPeriodOne w).toContinuousLinearMap
      (weightedBaseToPair_normalizedWeightedPeriodOne w) φ
    obtain ⟨h0,_,h0norm⟩ := hgap φ hφG
    have hR : 0≤R := (norm_nonneg h0).trans h0norm
    obtain ⟨_,_,H,hH,hφH,S,hS,hgn⟩ :=
      exists_uniform_small_sourcePeriodicGapDisplacement (p := 2) (by norm_num) (by norm_num) (L φ)
        (by norm_num : (0 : ℝ)<1)
    let T := U∩(L ⁻¹' (ball (L φ) ρ∩H)∩G)
    let D := (Real.pi+M)/4
    let K := D*R+M*‖Coeff.puncturedLattice r hr‖*(S*R)
    have hD : 0≤D := by dsimp only [D];positivity
    have hK : 0≤K := by dsimp only [K];positivity
    refine ⟨T,hU.inter (((isOpen_ball.inter hH).preimage L.continuous).inter hG),
      ⟨hφ,⟨mem_ball_self hρ,hφH⟩,hφG⟩,(fun _ hψ => hψ.1),K,hK,?_⟩
    intro ψ hψ
    obtain ⟨d,_hdval,hdnorm,hdfactor,hoff⟩ := hdata (L ψ) hψ.2.1.1
    obtain ⟨g,hg,hgnorm⟩ := hgap ψ hψ.2.2
    have hweight (k : ℤ) :
        ‖(k : ℂ)‖*‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (L ψ) k‖^2≤‖g k‖ := by
      rw [hg k,sourceWeightedSquaredGap,←mul_pow,sourceSobolevSpectralWeight_even]
      rw [norm_pow,Weight.norm_sobolev_mul_sq]
      norm_num only [show 2*(1/2 : ℝ)=1 by norm_num,Real.rpow_one,Complex.norm_intCast]
      nlinarith [sq_nonneg ‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (L ψ) k‖]
    have hdiag (n : ℤ) : ‖A.moment n n 2 (L ψ)‖≤D*‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (L ψ) n‖^2 := by
      rw [hdfactor n,norm_mul,norm_div,norm_pow]
      have hdn := (lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞)≠0) d n).trans hdnorm
      have hb : ‖(Real.pi : ℂ)+d n‖≤Real.pi+M := by
        apply (norm_add_le _ _).trans
        simpa only [Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le] using add_le_add le_rfl hdn
      norm_num only [Complex.norm_ofNat]
      calc
        _≤‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (L ψ) n‖^2/4*(Real.pi+M) := by gcongr
        _=_ := by dsimp only [D];ring
    exact Coeff.exists_positive_weighted_cubic_packet hr
      (sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (L ψ))
      (fun n k => A.moment n k 2 (L ψ)) g R S D M hS hD hM.le hgnorm
      (hgn (L ψ) hψ.2.1.2).1 hweight hdiag
      (fun n => by obtain ⟨a,_haval,_han,hanorm,hafactor⟩ := hoff n;exact ⟨a,hanorm,hafactor⟩)
      (hsum (L ψ) hψ.1.1)
  have hcoord (n : ℤ) : AnalyticOnNhd ℂ (fun φ => f φ n) U := by
    by_cases hn : 0<n
    · intro φ hφ
      exact ((ha n (L φ) hφ.1).comp (L.analyticAt φ)).congr
        (Eventually.of_forall (fun _ => (if_pos hn).symm))
    · simpa only [f,Coeff.positiveWeightedCubicSums,if_neg hn] using
        (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : CoeffPair 2 => (0 : ℂ)) U)
  obtain ⟨hval,hpacket⟩ := Coeff.analytic_realization_of_local_bounds (r := r) f hU hcoord (by
    intro φ hφ
    obtain ⟨T,hT,hφT,hTU,K,_hK,hb⟩ := hlocal φ hφ
    exact ⟨T,hT,hφT,hTU,K,hb⟩)
  refine ⟨U,hU,?_,(fun _ hφ => hUsV hφ.1),hpacket,(fun φ hφ n => hval φ hφ n),?_⟩
  · intro φ hφ
    have hrφ := normalizedWeightedSource_realType w φ hφ
    exact ⟨hrealUs hrφ,hrealUr hrφ⟩
  · intro φ hφ
    obtain ⟨T,hT,hφT,hTU,K,hK,hb⟩ := hlocal φ hφ
    refine ⟨T,hT,hφT,hTU,K,hK,?_⟩
    intro ψ hψ
    obtain ⟨b,hb,hbn⟩ := hb ψ hψ
    change ‖Coeff.ofFunctionOrZero r (f ψ)‖≤K
    rwa [Coeff.ofFunctionOrZero_eq_of_coordinates _ b hb]

end NLS.ZakharovShabat
