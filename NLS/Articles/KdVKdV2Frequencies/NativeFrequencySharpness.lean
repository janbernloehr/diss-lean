import NLS.Articles.KdVKdV2Frequencies.NativeActionLocalImage
import NLS.Articles.KdVKdV2Frequencies.SharpSobolevActionFrequencyBounds
import NLS.SequenceSpaces.LeadingActionSharpness

/-! Sharpness at EVERY actual real native potential: no stronger
weighted frequency bound holds on ANY open source neighborhood. -/
noncomputable section
open Set Metric Complex NLS.KdV NLS.Articles.KdVConvexity
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies

theorem exists_native_frequency_sharpness
    (D : GlobalRoughAbelianForwardData) (t : ℝ) (ht : 0<t) (ht1 : t<1)
    (G : ℕ+ → Coeff 1 → ℂ) (V : Set (Coeff 1)) (hV : IsOpen V)
    (hCV : Coeff.nonnegativeLocus 1⊆V) (hG : ∀ n, AnalyticOnNhd ℂ (G n) V)
    (hrec : ∀ (P : PhysicalFrequencyPairChart D) (z : Coeff 2 × Coeff 2),
      z∈P.domain → z∈Coeff.realPairLocus 2 → ∀ n, G n (quadraticActionsExponent (q := 1) z)=P.correction n z)
    (a₀ : physicalRealDeletedSubmodule) (T : Set physicalRealDeletedSubmodule)
    (hT : IsOpen T) (haT : a₀∈T) (r : ℝ) (hr : 2*t-1<r) (M : ℝ) (hM : 0≤M) (K : ℕ) :
    let κ := normalizedSobolevWeakActionInclusion (2*t-1) (by linarith)
    ∃ a∈T, ∃ n : ℕ+, K≤(n:ℤ).natAbs ∧
      M<Weight.sobolev r (n:ℤ)*‖G n (κ (nativeActionCoordinates D t ht.le a))‖ := by
  intro κ
  let θ := min t (2/3)
  have hθ : 0≤θ := le_min ht.le (by norm_num)
  have hθ1 : θ≤2/3 := min_le_right _ _
  have hθt : θ≤t := min_le_left _ _
  have hgap : 2*t-1<3*θ-1 := by
    by_cases h : t≤2/3
    · dsimp only [θ];rw [min_eq_left h];linarith
    · dsimp only [θ];rw [min_eq_right (by linarith : (2:ℝ)/3≤t)];linarith
  let b₀ := nativeActionCoordinates D t ht.le a₀
  obtain ⟨U,hU,hbU,_,_,L,B,hB,hb,_⟩ := exists_sharp_sobolev_action_frequency_bounds
    D t θ (2*t-1) ht.le hθ hθ1 hθt rfl G V hV hCV hG hrec b₀
    (nativeActionCoordinates_nonnegative D t ht.le a₀)
  obtain ⟨ρ,hρ,himage⟩ := nativeActionCoordinates_local_image D t ht.le a₀ T hT haT
  obtain ⟨η,hη,hball⟩ := Metric.isOpen_iff.mp (hU.inter isOpen_ball) b₀
    ⟨hbU,mem_ball_self hρ⟩
  let f := fun n b => G n (κ b)
  let g := normalizedSobolevRenormalizedFrequency (2*t-1) (by linarith) G
  have htail := Coeff.exists_uniform_strict_sobolev_frequency_tail U g (2*t-1) (3*θ-1)
    hgap L B hB hb
  obtain ⟨b,hbc,n,hn,hlarge⟩ := Coeff.exists_action_packet_frequency_lower_bound actionIndexEquiv b₀
    (nativeActionCoordinates_nonnegative D t ht.le a₀) η hη (2*t-1) r hr f g (fun _ _ => rfl)
    (fun ε hε => by
      obtain ⟨J,hJ⟩ := htail ε hε
      exact ⟨J,fun b hb n hn => hJ b (hball hb).1 n hn⟩) M hM K
  obtain ⟨a,ha,he⟩ := himage ⟨(hball hbc.1).2,hbc.2⟩
  refine ⟨a,ha,n,hn,?_⟩
  change M<Weight.sobolev r (n:ℤ)*‖f n (nativeActionCoordinates D t ht.le a)‖
  rwa [he]

end NLS.Articles.KdVKdV2Frequencies
