import NLS.ZakharovShabat.SourceSobolevSecondMomentPacket
import NLS.ZakharovShabat.SourceRefinedCubicNormBounds
import NLS.ZakharovShabat.SourceSobolevSquaredGapBounds
import NLS.SequenceSpaces.NegativeWeightReciprocalColumns
import NLS.SequenceSpaces.NegativeWeightedCubicPacket

/-! The ACTUAL signed index-weighted second moments have a genuine
negative-weight ell1 packet for EVERY -1<alpha<0, on complex normalized
H^((alpha+1)/2) source neighborhoods. All root and numerator data are
the SAME calibrated atlas; real membership alone is never used as a norm bound. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {W V : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

def SourceAbelianMomentAtlas.negativeWeightedSecondMomentPacket
    (A : SourceAbelianMomentAtlas (by norm_num) (by norm_num) W s)
    (a : ℝ) (ψ : CoeffPair 2) : Coeff 1 :=
  Coeff.ofFunctionOrZero 1 (fun n => (Weight.sobolev (-a) n : ℂ)*
    Coeff.positiveWeightedCubicSums (fun n k => A.moment n k 2 ψ) n)

theorem SourceAbelianMomentAtlas.exists_analytic_negativeWeightedSecondMomentPacket
    (A : SourceAbelianMomentAtlas (by norm_num) (by norm_num) W s)
    (a t : ℝ) (ha0 : 0<a) (ha1 : a<1) (ht : 0<t) (hat : 2*t=1-a)
    (hs : SourcePsiSquaredGapComplexExtension (by norm_num) (by norm_num) V s)
    (hV : IsOpen V) (hrealV : realTypeSourceLocus 2⊆V) :
    let w := sourceSobolevSpectralWeight t ht.le
    let L := normalizedWeightedSourceCLM (p := 2) w
    ∃ U : Set (CoeffPair 2), IsOpen U ∧ realTypeSourceLocus 2⊆U ∧ U⊆L ⁻¹' (A.domain∩V) ∧
      AnalyticOnNhd ℂ (fun φ => A.negativeWeightedSecondMomentPacket a (L φ)) U ∧
      (∀ φ∈U, ∀ n : ℤ, A.negativeWeightedSecondMomentPacket a (L φ) n=
        (Weight.sobolev (-a) n : ℂ)*(if 0<n then A.weightedSecondMomentSum n (L φ) else 0)) ∧
      ∀ φ∈U, ∃ T : Set (CoeffPair 2), IsOpen T ∧ φ∈T ∧ T⊆U ∧
        ∃ K : ℝ, 0≤K ∧ ∀ ψ∈T, ‖A.negativeWeightedSecondMomentPacket a (L ψ)‖≤K := by
  intro w L
  let δ := min t a/2
  let σ := a-δ
  have hδ : 0<δ := by dsimp only [δ];exact div_pos (lt_min ht ha0) (by norm_num)
  have hσ : 0<σ := by dsimp only [σ,δ];linarith [min_le_right t a]
  have hσa : σ<a := by dsimp only [σ];linarith
  have horder : 1≤σ+t+(1-a) := by dsimp only [σ,δ];linarith [min_le_left t a]
  obtain ⟨C,hC,hcolumn⟩ := Coeff.exists_negative_weight_reciprocal_column_bound a σ ha1 hσ hσa
  have hmat (k : ℤ) : (fun n => Coeff.negativeReciprocalMatrix a σ n k)=
      (fun n => Weight.sobolev σ k*(Weight.sobolev (-a) n*‖Coeff.puncturedLattice 2 (by norm_num) (n-k)‖)) := by
    funext n
    dsimp only [Coeff.negativeReciprocalMatrix]
    ring
  have hcols (k : ℤ) : Summable (fun n => Coeff.negativeReciprocalMatrix a σ n k) := by
    rw [hmat k]
    exact (hcolumn k).1.mul_left _
  have hcolb (k : ℤ) : (∑' n, Coeff.negativeReciprocalMatrix a σ n k)≤C := by
    rw [hmat k,tsum_mul_left]
    exact (hcolumn k).2
  obtain ⟨Us,hUs,_hUsc,hrealUs,hUsV,hsum,ha,_hconv,_hlocalUs⟩ :=
    A.exists_analytic_weightedSecondMomentSum hs hV hrealV
  obtain ⟨Ur,hUr,hrealUr,_hUrV,hrows⟩ := A.exists_local_refinedCubicNormBounds hs hV hrealV
  let U := L ⁻¹' (Us∩Ur)
  have hU : IsOpen U := (hUs.inter hUr).preimage L.continuous
  let f := fun (φ : CoeffPair 2) (n : ℤ) => (Weight.sobolev (-a) n : ℂ)*
    Coeff.positiveWeightedCubicSums (fun n k => A.moment n k 2 (L φ)) n
  have hlocal (φ : CoeffPair 2) (hφ : φ∈U) :
      ∃ T : Set (CoeffPair 2), IsOpen T ∧ φ∈T ∧ T⊆U ∧
        ∃ K : ℝ, 0≤K ∧ ∀ ψ∈T, ∃ b : Coeff 1, (∀ n, b n=f ψ n) ∧ ‖b‖≤K := by
    obtain ⟨ρ,hρ,_hball,D,M,hD,hM,hdata⟩ := hrows (L φ) hφ.2
    obtain ⟨G,hG,hφG,R,hR,hgap⟩ := exists_local_sobolevSquaredGap_bounds t ht.le φ
    let S := R+1
    have hS : 0≤S := by dsimp only [S];positivity
    let T := U∩(L ⁻¹' ball (L φ) ρ∩G)
    let K := (D+M*C*S)*R
    have hK : 0≤K := by dsimp only [K];positivity
    have hcenter : L φ∈ball (L φ) ρ := mem_ball_self hρ
    have hφT : φ∈T := ⟨hφ,hcenter,hφG⟩
    have hTU : T⊆U := fun _ hψ => hψ.1
    have hTo : IsOpen T := hU.inter ((isOpen_ball.preimage L.continuous).inter hG)
    refine ⟨T,hTo,hφT,hTU,K,hK,?_⟩
    intro ψ hψ
    obtain ⟨hdiag,hoffnorm⟩ := hdata (L ψ) hψ.2.1
    obtain ⟨g,hgnorm,hquad,hpoint⟩ := hgap ψ hψ.2.2
    let γ := sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (L ψ)
    have hquad' (k : ℤ) : ‖g k‖=Weight.sobolev (1-a) k*‖γ k‖^2 := by
      simpa only [hat] using hquad k
    exact Coeff.exists_negative_weighted_cubic_packet a σ t D M S C R horder hD hM hS hC
      hcols hcolb γ g hgnorm hquad' hpoint (fun n k => A.moment n k 2 (L ψ)) hdiag hoffnorm
      (hsum (L ψ) hψ.1.1)
  have hcoord (n : ℤ) : AnalyticOnNhd ℂ (fun φ => f φ n) U := by
    by_cases hn : 0<n
    · intro φ hφ
      have H : AnalyticAt ℂ (fun χ => (Weight.sobolev (-a) n : ℂ)*A.weightedSecondMomentSum n (L χ)) φ :=
        analyticAt_const.mul ((ha n (L φ) hφ.1).comp (L.analyticAt φ))
      exact H.congr (Eventually.of_forall (fun _ => by dsimp only [f,Coeff.positiveWeightedCubicSums];rw [if_pos hn];rfl))
    · simpa only [f,Coeff.positiveWeightedCubicSums,if_neg hn,mul_zero] using
        (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : CoeffPair 2 => (0 : ℂ)) U)
  obtain ⟨hval,hpacket⟩ := Coeff.analytic_realization_of_local_bounds (r := 1) f hU hcoord (by
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
    change ‖Coeff.ofFunctionOrZero 1 (f ψ)‖≤K
    rwa [Coeff.ofFunctionOrZero_eq_of_coordinates _ b hb]

end NLS.ZakharovShabat
