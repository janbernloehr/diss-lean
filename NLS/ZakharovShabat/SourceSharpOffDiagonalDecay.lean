import NLS.ZakharovShabat.SourceOffDiagonalSecondMomentBounds
import NLS.SequenceSpaces.SharpCubicOffDiagonalDecay

/-! The ACTUAL off-diagonal weighted second-moment sum has exact order
1-3t at EVERY complex source in a neighborhood of the full real locus.
For t<2/3 it is little-o pointwise; at t=2/3 it is locally uniformly O(1/n).
Uniform little-o on whole neighborhoods is not asserted here. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {W V : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

theorem SourceAbelianMomentAtlas.exists_sharp_offDiagonal_secondMoment_decay
    (A : SourceAbelianMomentAtlas (by norm_num) (by norm_num) W s)
    (t : ℝ) (ht : 0≤t) (ht1 : t≤2/3)
    (hs : SourcePsiSquaredGapComplexExtension (by norm_num) (by norm_num) V s)
    (hV : IsOpen V) (hrealV : realTypeSourceLocus 2⊆V) :
    let w := sourceSobolevSpectralWeight t ht
    let L := normalizedWeightedSourceCLM (p := 2) w
    ∃ U : Set (CoeffPair 2), IsOpen U ∧ realTypeSourceLocus 2⊆U ∧ U⊆L ⁻¹' (A.domain∩V) ∧
      ∀ φ∈U, ∃ T : Set (CoeffPair 2), IsOpen T ∧ φ∈T ∧ T⊆U ∧
        ∃ K : ℝ, 0≤K ∧
          (∀ ψ∈T, ∀ n : ℤ, Weight.sobolev (3*t-1) n*
            ‖A.weightedSecondMomentSum n (L ψ)-(n : ℂ)*(A.moment n n 2 (L ψ)-A.moment n (-n) 2 (L ψ))‖≤K) ∧
          (t<2/3 → ∀ ψ∈T,
            Tendsto (fun n : ℕ => Weight.sobolev (3*t-1) (n : ℤ)*
              ‖A.weightedSecondMomentSum (n : ℤ) (L ψ)-(n : ℂ)*
                (A.moment (n : ℤ) (n : ℤ) 2 (L ψ)-A.moment (n : ℤ) (-(n : ℤ)) 2 (L ψ))‖) atTop (𝓝 0)) := by
  intro w L
  obtain ⟨Us,hUs,_hUsc,hrealUs,hUsV,hsum,_ha,_hconv,_hlocalUs⟩ :=
    A.exists_analytic_weightedSecondMomentSum hs hV hrealV
  obtain ⟨Ur,hUr,hrealUr,_hUrV,hrows⟩ := A.exists_local_refinedCubicNormBounds hs hV hrealV
  let U := L ⁻¹' (Us∩Ur)
  have hU : IsOpen U := (hUs.inter hUr).preimage L.continuous
  refine ⟨U,hU,(fun φ hφ => ?_),(fun φ hφ => hUsV hφ.1),?_⟩
  · have hrφ := normalizedWeightedSource_realType w φ hφ
    exact ⟨hrealUs hrφ,hrealUr hrφ⟩
  intro φ hφ
  obtain ⟨ρ,hρ,_hball,_D,M,_hD,hM,hdata⟩ := hrows (L φ) hφ.2
  obtain ⟨G,hG,hφG,R,hR,hgap⟩ := exists_local_sobolevSquaredGap_bounds t ht φ
  let S := R+1
  have hS : 0≤S := by dsimp only [S];positivity
  let T := U∩(L ⁻¹' ball (L φ) ρ∩G)
  have hT : IsOpen T := hU.inter ((isOpen_ball.preimage L.continuous).inter hG)
  have hbounds (ψ : CoeffPair 2) (hψ : ψ∈T) :
      ∃ g : Coeff 1, ‖g‖≤R ∧
        (∀ k, ‖g k‖=Weight.sobolev (2*t) k*
          ‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (L ψ) k‖^2) ∧
        (∀ k, Weight.sobolev t k*‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (L ψ) k‖≤S) ∧
        ∀ n k, k≠n → ‖Coeff.pairedOffDiagonalRow (fun n k => A.moment n k 2 (L ψ)) n k‖≤
          M*‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (L ψ) k‖^3*
            ‖Coeff.puncturedLattice 2 (by norm_num) (n-k)‖ := by
    obtain ⟨g,hgnorm,hquad,hpoint⟩ := hgap ψ hψ.2.2
    refine ⟨g,hgnorm,hquad,hpoint,?_⟩
    intro n k hkn
    exact (Coeff.norm_pairedOffDiagonalRow_le (fun n k => A.moment n k 2 (L ψ)) n k).trans
      ((hdata (L ψ) hψ.2.1).2 n k hkn)
  have hcenter : L φ∈ball (L φ) ρ := mem_ball_self hρ
  have hφT : φ∈T := ⟨hφ,hcenter,hφG⟩
  have hK : 0≤2*(M*S)*R := mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg hM hS)) hR
  refine ⟨T,hT,hφT,(fun _ hψ => hψ.1),2*(M*S)*R,hK,?_,?_⟩
  · intro ψ hψ n
    obtain ⟨g,hgnorm,hquad,hpoint,hoff⟩ := hbounds ψ hψ
    have hb := (Coeff.sharp_offDiagonal_cubic_sum_bound t ht ht1 M S hM hS _ g hquad hpoint
      (Coeff.pairedOffDiagonalRow (fun n k => A.moment n k 2 (L ψ)))
      (Coeff.pairedOffDiagonalRow_self _) hoff).2 n
    rw [A.pairedOffDiagonalSecondMomentSum_eq (L ψ) n (hsum (L ψ) hψ.1.1 n)] at hb
    apply hb.trans
    have hs' := Coeff.tsum_sharpReciprocalKernel_mul_le (1-3*t) (by linarith) (by linarith)
      (fun k => ‖g k‖) ((lp.memℓp g).norm.summable_of_one) (fun k => norm_nonneg _) n
    have he : (∑' k, ‖g k‖)=‖g‖ := by simpa using (lp.norm_eq_tsum_rpow (by norm_num) g).symm
    rw [he] at hs'
    nlinarith [mul_le_mul_of_nonneg_left hs' (mul_nonneg hM hS),
      mul_le_mul_of_nonneg_left hgnorm (mul_nonneg (by norm_num : (0 : ℝ)≤2) (mul_nonneg hM hS))]
  · intro ht2 ψ hψ
    obtain ⟨g,_hgnorm,hquad,hpoint,hoff⟩ := hbounds ψ hψ
    have h := Coeff.tendsto_sharp_offDiagonal_cubic_sum t ht ht2 M S hM hS _ g hquad hpoint
      (Coeff.pairedOffDiagonalRow (fun n k => A.moment n k 2 (L ψ)))
      (Coeff.pairedOffDiagonalRow_self _) hoff
    apply h.congr'
    exact Filter.Eventually.of_forall (fun n => by
      dsimp only
      rw [A.pairedOffDiagonalSecondMomentSum_eq (L ψ) n (hsum (L ψ) hψ.1.1 n)]
      simp only [Int.cast_natCast])

end NLS.ZakharovShabat
