import NLS.ZakharovShabat.SourceSobolevSecondMomentPacket
import NLS.ZakharovShabat.SourceRefinedCubicNormBounds
import NLS.ZakharovShabat.SourceSobolevSquaredGapBounds
import NLS.SequenceSpaces.NegativeWeightReciprocalColumns
import NLS.SequenceSpaces.NegativeWeightedOffDiagonalPacket

/-! The actual off-diagonal moment sum admits a strictly stronger
negative weighted ell1 target at every intermediate source order.
All estimates hold on full complex source neighborhoods. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {W V : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

theorem SourceAbelianMomentAtlas.pairedOffDiagonalSecondMomentSum_eq
    (A : SourceAbelianMomentAtlas (by norm_num) (by norm_num) W s)
    (ψ : CoeffPair 2) (n : ℤ)
    (hs : Summable (fun k : ℤ => ‖(k : ℂ)*A.moment n k 2 ψ‖)) :
    (∑' k : ℤ, (k : ℂ)*Coeff.pairedOffDiagonalRow (fun n k => A.moment n k 2 ψ) n k)=
      A.weightedSecondMomentSum n ψ-(n : ℂ)*(A.moment n n 2 ψ-A.moment n (-n) 2 ψ) :=
  Coeff.tsum_pairedOffDiagonalRow (fun n k => A.moment n k 2 ψ) n hs

def SourceAbelianMomentAtlas.negativeWeightedOffDiagonalSecondMomentPacket
    (A : SourceAbelianMomentAtlas (by norm_num) (by norm_num) W s)
    (b : ℝ) (ψ : CoeffPair 2) : Coeff 1 :=
  Coeff.ofFunctionOrZero 1 (fun n => (Weight.sobolev (-b) n : ℂ)*
    Coeff.positiveWeightedCubicSums (Coeff.pairedOffDiagonalRow (fun n k => A.moment n k 2 ψ)) n)

theorem SourceAbelianMomentAtlas.exists_negativeWeightedOffDiagonalSecondMoment_localBounds
    (A : SourceAbelianMomentAtlas (by norm_num) (by norm_num) W s)
    (a b σ t : ℝ) (hb1 : b<1) (hσ : 0<σ) (hσb : σ<b)
    (ht : 0<t) (hat : 2*t=1-a) (horder : 1≤σ+t+(1-a))
    (hs : SourcePsiSquaredGapComplexExtension (by norm_num) (by norm_num) V s)
    (hV : IsOpen V) (hrealV : realTypeSourceLocus 2⊆V) :
    let w := sourceSobolevSpectralWeight t ht.le
    let L := normalizedWeightedSourceCLM (p := 2) w
    ∃ U : Set (CoeffPair 2), IsOpen U ∧ realTypeSourceLocus 2⊆U ∧ U⊆L ⁻¹' (A.domain∩V) ∧
      (∀ φ∈U, ∀ n, Summable (fun k : ℤ => ‖(k : ℂ)*A.moment n k 2 (L φ)‖)) ∧
      ∀ φ∈U, ∃ T : Set (CoeffPair 2), IsOpen T ∧ φ∈T ∧ T⊆U ∧
        ∃ K : ℝ, 0≤K ∧ ∀ ψ∈T, ∃ c : Coeff 1,
          (∀ n, c n=(Weight.sobolev (-b) n : ℂ)*Coeff.positiveWeightedCubicSums
            (Coeff.pairedOffDiagonalRow (fun n k => A.moment n k 2 (L ψ))) n) ∧ ‖c‖≤K := by
  intro w L
  obtain ⟨C,hC,hcolumn⟩ := Coeff.exists_negative_weight_reciprocal_column_bound b σ hb1 hσ hσb
  have hmat (k : ℤ) : (fun n => Coeff.negativeReciprocalMatrix b σ n k)=
      (fun n => Weight.sobolev σ k*(Weight.sobolev (-b) n*‖Coeff.puncturedLattice 2 (by norm_num) (n-k)‖)) := by
    funext n
    dsimp only [Coeff.negativeReciprocalMatrix]
    ring
  have hcols (k : ℤ) : Summable (fun n => Coeff.negativeReciprocalMatrix b σ n k) := by
    rw [hmat k]
    exact (hcolumn k).1.mul_left _
  have hcolb (k : ℤ) : (∑' n, Coeff.negativeReciprocalMatrix b σ n k)≤C := by
    rw [hmat k,tsum_mul_left]
    exact (hcolumn k).2
  obtain ⟨Us,hUs,_hUsc,hrealUs,hUsV,hsum,_ha,_hconv,_hlocalUs⟩ :=
    A.exists_analytic_weightedSecondMomentSum hs hV hrealV
  obtain ⟨Ur,hUr,hrealUr,_hUrV,hrows⟩ := A.exists_local_refinedCubicNormBounds hs hV hrealV
  let U := L ⁻¹' (Us∩Ur)
  have hU : IsOpen U := (hUs.inter hUr).preimage L.continuous
  let f := fun (φ : CoeffPair 2) (n : ℤ) => (Weight.sobolev (-b) n : ℂ)*
    Coeff.positiveWeightedCubicSums (Coeff.pairedOffDiagonalRow (fun n k => A.moment n k 2 (L φ))) n
  have hlocal (φ : CoeffPair 2) (hφ : φ∈U) :
      ∃ T : Set (CoeffPair 2), IsOpen T ∧ φ∈T ∧ T⊆U ∧
        ∃ K : ℝ, 0≤K ∧ ∀ ψ∈T, ∃ b : Coeff 1, (∀ n, b n=f ψ n) ∧ ‖b‖≤K := by
    obtain ⟨ρ,hρ,_hball,_D,M,_hD,hM,hdata⟩ := hrows (L φ) hφ.2
    obtain ⟨G,hG,hφG,R,hR,hgap⟩ := exists_local_sobolevSquaredGap_bounds t ht.le φ
    let S := R+1
    have hS : 0≤S := by dsimp only [S];positivity
    let T := U∩(L ⁻¹' ball (L φ) ρ∩G)
    let K := M*C*S*R
    have hK : 0≤K := by dsimp only [K];positivity
    have hcenter : L φ∈ball (L φ) ρ := mem_ball_self hρ
    have hφT : φ∈T := ⟨hφ,hcenter,hφG⟩
    have hTU : T⊆U := fun _ hψ => hψ.1
    have hTo : IsOpen T := hU.inter ((isOpen_ball.preimage L.continuous).inter hG)
    refine ⟨T,hTo,hφT,hTU,K,hK,?_⟩
    intro ψ hψ
    obtain ⟨_hdiag,hoffnorm⟩ := hdata (L ψ) hψ.2.1
    obtain ⟨g,hgnorm,hquad,hpoint⟩ := hgap ψ hψ.2.2
    let γ := sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (L ψ)
    have hquad' (k : ℤ) : ‖g k‖=Weight.sobolev (1-a) k*‖γ k‖^2 := by
      simpa only [hat] using hquad k
    exact Coeff.exists_negative_weighted_offDiagonal_packet a b σ t M S C R horder hM hS hC
      hcols hcolb γ g hgnorm hquad' hpoint
      (Coeff.pairedOffDiagonalRow (fun n k => A.moment n k 2 (L ψ)))
      (Coeff.pairedOffDiagonalRow_self (fun n k => A.moment n k 2 (L ψ)))
      (fun n k hkn => (Coeff.norm_pairedOffDiagonalRow_le (fun n k => A.moment n k 2 (L ψ)) n k).trans (hoffnorm n k hkn))
      (fun n => Coeff.summable_norm_pairedOffDiagonalRow (fun n k => A.moment n k 2 (L ψ)) n (hsum (L ψ) hψ.1.1 n))
  refine ⟨U,hU,?_,(fun _ hφ => hUsV hφ.1),(fun _ hφ => hsum _ hφ.1),hlocal⟩
  intro φ hφ
  have hrφ := normalizedWeightedSource_realType w φ hφ
  exact ⟨hrealUs hrφ,hrealUr hrφ⟩

end NLS.ZakharovShabat
