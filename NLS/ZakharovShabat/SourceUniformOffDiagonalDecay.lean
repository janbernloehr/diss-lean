import NLS.ZakharovShabat.SourceSharpOffDiagonalDecay
import NLS.ZakharovShabat.SourceOffDiagonalCubicUniformTail
import NLS.SequenceSpaces.UniformSharpCubicSums

/-! Sharp uniform little-o of the ACTUAL off-diagonal second-moment
sum on one fixed full complex normalized Sobolev neighborhood. -/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {W V : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

theorem SourceAbelianMomentAtlas.exists_uniform_offDiagonal_secondMoment_decay
    (A : SourceAbelianMomentAtlas (by norm_num) (by norm_num) W s)
    (t : ℝ) (ht : 0<t) (ht1 : t<2/3)
    (hs : SourcePsiSquaredGapComplexExtension (by norm_num) (by norm_num) V s)
    (hV : IsOpen V) (hrealV : realTypeSourceLocus 2⊆V) (φ : realTypeSourceSubmodule 2) :
    let L := normalizedWeightedSourceCLM (p := 2) (sourceSobolevSpectralWeight t ht.le)
    ∃ T : Set (CoeffPair 2), IsOpen T ∧ φ.val∈T ∧ T⊆L ⁻¹' (A.domain∩V) ∧
      ∀ ε > (0:ℝ), ∃ N : ℕ, ∀ ψ∈T, ∀ n : ℤ, N≤n.natAbs →
        Weight.sobolev (3*t-1) n*‖A.weightedSecondMomentSum n (L ψ)-(n:ℂ)*
          (A.moment n n 2 (L ψ)-A.moment n (-n) 2 (L ψ))‖≤ε := by
  intro L
  have hrφ := normalizedWeightedSource_realType (sourceSobolevSpectralWeight t ht.le) φ.val φ.property
  obtain ⟨Us,hUs,_,hrealUs,hUsV,hsum,_,_,_⟩ := A.exists_analytic_weightedSecondMomentSum hs hV hrealV
  obtain ⟨Ur,_,hrealUr,_,hrows⟩ := A.exists_local_refinedCubicNormBounds hs hV hrealV
  obtain ⟨ρ,hρ,_,_,M,_,hM,hdata⟩ := hrows (L φ.val) (hrealUr hrφ)
  obtain ⟨D,_⟩ := A.exists_errorDomain hs.toSourcePsiNormalizedComplexExtension hV hrealV
  obtain ⟨Tr,hTr,hφr,_,htail⟩ := D.exists_local_sobolev_offDiagonal_cubic_uniform_tail hs
    t ht (by linarith) φ (hrealV hrφ)
  obtain ⟨G,hG,hφG,R,hR,hgap⟩ := exists_local_sobolevSquaredGap_bounds t ht.le φ.val
  let T := (Tr∩G)∩L ⁻¹' (Us∩ball (L φ.val) ρ)
  have hT : IsOpen T := (hTr.inter hG).inter ((hUs.inter isOpen_ball).preimage L.continuous)
  let γ := fun ψ => sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (L ψ)
  let F := fun ψ => Coeff.pairedOffDiagonalRow (fun n k => A.moment n k 2 (L ψ))
  have hgapT : ∀ ψ∈T, ∃ g : Coeff 1, ‖g‖≤R ∧
      (∀ k, ‖g k‖=Weight.sobolev (2*t) k*‖γ ψ k‖^2) ∧
      ∀ k, Weight.sobolev t k*‖γ ψ k‖≤R+1 := fun ψ hψ => hgap ψ hψ.1.2
  have hrow : ∀ ψ∈T, ∀ n k, k≠n → ‖F ψ n k‖≤
      M*‖γ ψ k‖^3*‖Coeff.puncturedLattice 2 (by norm_num) (n-k)‖ := by
    intro ψ hψ n k hkn
    exact (Coeff.norm_pairedOffDiagonalRow_le _ n k).trans ((hdata (L ψ) hψ.2.2).2 n k hkn)
  have htailT : ∀ δ > (0:ℝ), ∃ K : ℕ, ∀ ψ∈T, ∀ n k : ℤ, K≤k.natAbs → k≠n →
      ‖F ψ n k‖≤δ*‖γ ψ k‖^3*‖Coeff.puncturedLattice 2 (by norm_num) (n-k)‖ := by
    intro δ hδ
    obtain ⟨K,hK⟩ := htail δ hδ
    refine ⟨K,?_⟩
    intro ψ hψ n k hk hkn
    have hb := hK ψ hψ.1.1 n k hk hkn
    have hn : n-k≠0 := sub_ne_zero.mpr hkn.symm
    have hnC : ((n-k:ℤ):ℂ)≠0 := by exact_mod_cast hn
    have hm : ‖A.moment n k 2 (L ψ)‖≤(‖γ ψ k‖^3*δ)/‖((n-k:ℤ):ℂ)‖ := by
      apply (le_div_iff₀ (norm_pos_iff.mpr hnC)).mpr
      simpa only [norm_mul,mul_comm] using hb
    apply (Coeff.norm_pairedOffDiagonalRow_le _ n k).trans
    rw [Coeff.puncturedLattice_apply,if_neg hn,norm_inv]
    exact hm.trans_eq (by ring)
  have hbound := Coeff.exists_uniform_sharp_offDiagonal_cubic_sum_tail T t ht.le ht1 M (R+1) R
    hM (by linarith) hR (fun ψ k => γ ψ k) F hgapT
    (fun ψ _ n => Coeff.pairedOffDiagonalRow_self (fun j k => A.moment j k 2 (L ψ)) n) hrow htailT
  refine ⟨T,hT,⟨⟨hφr,hφG⟩,hrealUs hrφ,mem_ball_self hρ⟩,
    (fun _ hψ => hUsV hψ.2.1),?_⟩
  intro ε hε
  obtain ⟨N,hN⟩ := hbound ε hε
  refine ⟨N,?_⟩
  intro ψ hψ n hn
  have hb := hN ψ hψ n hn
  dsimp only [F] at hb
  rw [A.pairedOffDiagonalSecondMomentSum_eq (L ψ) n (hsum (L ψ) hψ.2.1 n)] at hb
  exact hb

end NLS.ZakharovShabat
