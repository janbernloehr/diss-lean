import NLS.ZakharovShabat.NormalizedWeightedClosingDerivative
import NLS.ComplexAnalysis.NearIdentityAnalyticInverse

/-! # Uniform analytic inverses in normalized weighted source coordinates

The common source and image radii are measured in the weighted norm.
Actual coefficient membership identifies inverse targets with weighted
closing equations at the constructed source.
-/

noncomputable section
open Set Metric NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Uniform inverse branches can be confined to any supplied open
neighborhood of the initial source. Actual coordinate membership holds
on the common source ball. -/
theorem exists_uniform_normalizedWeightedClosingInverse_within
    (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight) (φ : CoeffPair p)
    (V : Set (CoeffPair p)) (hoV : IsOpen V) (hφV : φ ∈ V) :
    let K := resonantCenterRemainderBallConstant p (‖φ‖+1);
    ∃ r : ℝ, 0 < r ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ball φ r ⊆ V ∧
      ∀ N : ℕ, N₀ ≤ N →
        (∀ ψ ∈ ball φ r, ∀ positive : Bool,
          Memℓp (weightedResonantCenterRemainderCoordinate hp w
            (normalizedWeightedPeriodOne w ψ) N positive) p) ∧
        ∃ g : CoeffPair p → CoeffPair p,
          AnalyticOnNhd ℂ g (ball (normalizedWeightedClosingMap hp w φ N) (quantitativeInverseImageRadius r 2 (4*K))) ∧
          g (normalizedWeightedClosingMap hp w φ N) = φ ∧
          ∀ y ∈ ball (normalizedWeightedClosingMap hp w φ N) (quantitativeInverseImageRadius r 2 (4*K)),
            g y ∈ ball φ (quantitativeInverseJointRadius r 2 (4*K)) ∧
            normalizedWeightedClosingMap hp w (g y) N = y ∧
            ‖g y-φ‖ ≤ 2*‖y-normalizedWeightedClosingMap hp w φ N‖ ∧
            ∀ x ∈ ball φ (quantitativeInverseJointRadius r 2 (4*K)),
              normalizedWeightedClosingMap hp w x N = y → x = g y := by
  let K := resonantCenterRemainderBallConstant p (‖φ‖+1)
  have hK : 0 < K := resonantCenterRemainderBallConstant_pos _ (by positivity)
  obtain ⟨r₀,hr₀,N₀,hN₀,hF⟩ := exists_fixedBall_normalizedWeightedClosingMap_derivative
    hp hp1 w φ (1/4) (by norm_num)
  obtain ⟨s,hs,hsV⟩ := Metric.mem_nhds_iff.mp (hoV.mem_nhds hφV)
  let r := min r₀ (s/2)
  have hr : 0 < r := by dsimp [r]; positivity
  have hrr₀ : r ≤ r₀ := min_le_left _ _
  have hrs : r ≤ s := (min_le_right r₀ (s/2)).trans (by linarith)
  have hV : ball φ r ⊆ V := fun _ hψ => hsV (ball_subset_ball hrs hψ)
  have hinner : ball φ r ⊆ ball φ (3*r₀) := ball_subset_ball (by linarith)
  have houter : ball φ r ⊆ ball φ (4*r₀) := ball_subset_ball (by linarith)
  have hbase : ball φ r ⊆ ball φ r₀ := ball_subset_ball hrr₀
  refine ⟨r,hr,N₀,hN₀,hV,?_⟩
  intro N hN
  have h := hF N hN
  have hA : AnalyticOnNhd ℂ (fun ψ => normalizedWeightedClosingMap hp w ψ N) (ball φ r) :=
    fun ψ hψ => h.1 ψ (houter hψ)
  have hnear (ψ : CoeffPair p) (hψ : ψ ∈ ball φ r) :
      ‖fderiv ℂ (fun χ => normalizedWeightedClosingMap hp w χ N) ψ-ContinuousLinearMap.id ℂ (CoeffPair p)‖ ≤ (1/2 : ℝ) :=
    (h.2.2.1 ψ (hinner hψ)).le.trans (by norm_num)
  have hLip (x : CoeffPair p) (hx : x ∈ ball φ r) (y : CoeffPair p) (hy : y ∈ ball φ r) :
      ‖fderiv ℂ (fun χ => normalizedWeightedClosingMap hp w χ N) x-
        fderiv ℂ (fun χ => normalizedWeightedClosingMap hp w χ N) y‖ ≤ 4*K*‖x-y‖ :=
    h.2.2.2 y (hbase hy) x (hbase hx)
  obtain ⟨g,hg,hga,hinv⟩ := exists_analytic_inverse_of_derivative_near_id
    (fun ψ => normalizedWeightedClosingMap hp w ψ N) φ r (4*K) hr (by positivity) hA hnear hLip
  have hρ : quantitativeInverseJointRadius r 2 (4*K) < r :=
    (min_le_left _ _).trans_lt (half_lt_self hr)
  have hsmall : ball φ (quantitativeInverseJointRadius r 2 (4*K)) ⊆ ball φ r := ball_subset_ball hρ.le
  refine ⟨fun ψ hψ => (h.2.1 ψ (houter hψ)).1,g,hg,hga,?_⟩
  intro y hy
  have hi := hinv y hy
  have hbound := norm_sub_le_two_mul_norm_image_sub_of_derivative_near_id
    (fun ψ => normalizedWeightedClosingMap hp w ψ N) φ r hA hnear (g y) φ (hsmall hi.1) (mem_ball_self hr)
  exact ⟨hi.1,hi.2.1,by simpa only [hi.2.1] using hbound,hi.2.2⟩

/-- Right inversion and actual membership identify the two high
target coefficients with the signed spectral closing equations. -/
theorem normalizedWeightedClosingInverse_coefficients
    (hp : p ≠ ⊤) (w : SpectralWeight) (ψ y : CoeffPair p) (N : ℕ)
    (hmem : ∀ positive : Bool, Memℓp (weightedResonantCenterRemainderCoordinate hp w
      (normalizedWeightedPeriodOne w ψ) N positive) p)
    (hF : normalizedWeightedClosingMap hp w ψ N = y) (n : ℤ) (hn : N ≤ n.natAbs) :
    let ζ := weightedResonantDiagonalCenter hp w (normalizedWeightedPeriodOne w ψ) n;
    (w (2*n) : ℂ)*weightedResonantBMinusExtension hp w (normalizedWeightedPeriodOne w ψ) n ζ = y.fst (-n) ∧
      (w (2*n) : ℂ)*weightedResonantBPlusExtension hp w (normalizedWeightedPeriodOne w ψ) n ζ = y.snd n := by
  have hm := (normalizedWeightedClosingMap_apply_of_mem hp w ψ N hmem (-n)).1
  have hpcoord := (normalizedWeightedClosingMap_apply_of_mem hp w ψ N hmem n).2
  rw [hF] at hm hpcoord
  exact ⟨by simpa only [Int.natAbs_neg,if_pos hn,neg_neg,mul_neg,SpectralWeight.apply_neg] using hm.symm,
    by simpa only [if_pos hn] using hpcoord.symm⟩


end NLS.ZakharovShabat
