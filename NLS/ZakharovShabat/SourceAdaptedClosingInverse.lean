import NLS.ZakharovShabat.SourceAdaptedClosingMapDerivative
import NLS.ZakharovShabat.SourceResonantCenterClosing
import NLS.ComplexAnalysis.NearIdentityAnalyticInverse

/-!
# Analytic inverse branches of the actual adapted source map

One fixed source radius and cutoff give analytic inverse branches for
every larger cutoff, with common positive image and source radii. The
inverse displacement is at most twice the target displacement. The
inverse source satisfies the actual spectral closing equations, and
zero high target coordinates close its original periodic spectrum.

Constructing suitable truncated targets in these image balls and
preserving the real-type locus still remain before finite-gap density.
-/

noncomputable section
open Set Metric NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Uniform inverse branches can be confined to any supplied open
neighborhood of the initial source. Actual coordinate membership holds
on the common source ball. -/
theorem exists_uniform_sourceAdaptedClosingInverse_within
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (V : Set (CoeffPair p)) (hoV : IsOpen V) (hφV : φ ∈ V) :
    let K := resonantCenterRemainderBallConstant p (‖φ‖+1);
    ∃ r : ℝ, 0 < r ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ball φ r ⊆ V ∧
      ∀ N : ℕ, N₀ ≤ N →
        (∀ ψ ∈ ball φ r, ∀ positive : Bool,
          Memℓp (weightedResonantCenterRemainderCoordinate hp SpectralWeight.one
            (sourceWeightedPeriodOne ψ) N positive) p) ∧
        ∃ g : CoeffPair p → CoeffPair p,
          AnalyticOnNhd ℂ g (ball (sourceAdaptedClosingMap hp φ N) (quantitativeInverseImageRadius r 2 (4*K))) ∧
          g (sourceAdaptedClosingMap hp φ N) = φ ∧
          ∀ y ∈ ball (sourceAdaptedClosingMap hp φ N) (quantitativeInverseImageRadius r 2 (4*K)),
            g y ∈ ball φ (quantitativeInverseJointRadius r 2 (4*K)) ∧
            sourceAdaptedClosingMap hp (g y) N = y ∧
            ‖g y-φ‖ ≤ 2*‖y-sourceAdaptedClosingMap hp φ N‖ ∧
            ∀ x ∈ ball φ (quantitativeInverseJointRadius r 2 (4*K)),
              sourceAdaptedClosingMap hp x N = y → x = g y := by
  let K := resonantCenterRemainderBallConstant p (‖φ‖+1)
  have hK : 0 < K := resonantCenterRemainderBallConstant_pos _ (by positivity)
  obtain ⟨r₀,hr₀,N₀,hN₀,hF⟩ := exists_fixedBall_sourceAdaptedClosingMap_derivative
    hp hp1 φ (1/4) (by norm_num)
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
  have hA : AnalyticOnNhd ℂ (fun ψ => sourceAdaptedClosingMap hp ψ N) (ball φ r) :=
    fun ψ hψ => h.1 ψ (houter hψ)
  have hnear (ψ : CoeffPair p) (hψ : ψ ∈ ball φ r) :
      ‖fderiv ℂ (fun χ => sourceAdaptedClosingMap hp χ N) ψ-ContinuousLinearMap.id ℂ (CoeffPair p)‖ ≤ (1/2 : ℝ) :=
    (h.2.2.1 ψ (hinner hψ)).le.trans (by norm_num)
  have hLip (x : CoeffPair p) (hx : x ∈ ball φ r) (y : CoeffPair p) (hy : y ∈ ball φ r) :
      ‖fderiv ℂ (fun χ => sourceAdaptedClosingMap hp χ N) x-
        fderiv ℂ (fun χ => sourceAdaptedClosingMap hp χ N) y‖ ≤ 4*K*‖x-y‖ :=
    h.2.2.2 y (hbase hy) x (hbase hx)
  obtain ⟨g,hg,hga,hinv⟩ := exists_analytic_inverse_of_derivative_near_id
    (fun ψ => sourceAdaptedClosingMap hp ψ N) φ r (4*K) hr (by positivity) hA hnear hLip
  have hρ : quantitativeInverseJointRadius r 2 (4*K) < r :=
    (min_le_left _ _).trans_lt (half_lt_self hr)
  have hsmall : ball φ (quantitativeInverseJointRadius r 2 (4*K)) ⊆ ball φ r := ball_subset_ball hρ.le
  refine ⟨fun ψ hψ => (h.2.1 ψ (houter hψ)).1,g,hg,hga,?_⟩
  intro y hy
  have hi := hinv y hy
  have hbound := norm_sub_le_two_mul_norm_image_sub_of_derivative_near_id
    (fun ψ => sourceAdaptedClosingMap hp ψ N) φ r hA hnear (g y) φ (hsmall hi.1) (mem_ball_self hr)
  exact ⟨hi.1,hi.2.1,by simpa only [hi.2.1] using hbound,hi.2.2⟩

/-- Right inversion and actual membership identify the two high
target coefficients with the signed spectral closing equations. -/
theorem sourceAdaptedClosingInverse_coefficients
    (hp : p ≠ ⊤) (ψ y : CoeffPair p) (N : ℕ)
    (hmem : ∀ positive : Bool, Memℓp (weightedResonantCenterRemainderCoordinate hp SpectralWeight.one
      (sourceWeightedPeriodOne ψ) N positive) p)
    (hF : sourceAdaptedClosingMap hp ψ N = y) (n : ℤ) (hn : N ≤ n.natAbs) :
    let ζ := weightedResonantDiagonalCenter hp SpectralWeight.one (sourceWeightedPeriodOne ψ) n;
    weightedResonantBMinusExtension hp SpectralWeight.one (sourceWeightedPeriodOne ψ) n ζ = y.fst (-n) ∧
      weightedResonantBPlusExtension hp SpectralWeight.one (sourceWeightedPeriodOne ψ) n ζ = y.snd n := by
  have hm := (sourceAdaptedClosingMap_apply_of_mem hp ψ N hmem (-n)).1
  have hpcoord := (sourceAdaptedClosingMap_apply_of_mem hp ψ N hmem n).2
  rw [hF] at hm hpcoord
  exact ⟨by simpa only [Int.natAbs_neg,if_pos hn,neg_neg] using hm.symm,
    by simpa only [if_pos hn] using hpcoord.symm⟩

/-- The actual adapted source map has analytic inverse branches on
common quantitative balls for every larger cutoff. Their high target
coordinates are the actual off-diagonal equations at the constructed
source, and their zero coordinates close the original periodic spectrum. -/
theorem exists_uniform_sourceAdaptedClosingInverse
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    let K := resonantCenterRemainderBallConstant p (‖φ‖+1);
    ∃ r : ℝ, 0 < r ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      ∃ g : CoeffPair p → CoeffPair p,
        AnalyticOnNhd ℂ g (ball (sourceAdaptedClosingMap hp φ N) (quantitativeInverseImageRadius r 2 (4*K))) ∧
        g (sourceAdaptedClosingMap hp φ N) = φ ∧
        ∀ y ∈ ball (sourceAdaptedClosingMap hp φ N) (quantitativeInverseImageRadius r 2 (4*K)),
          let ψ := g y;
          ψ ∈ ball φ (quantitativeInverseJointRadius r 2 (4*K)) ∧
          sourceAdaptedClosingMap hp ψ N = y ∧
          ‖ψ-φ‖ ≤ 2*‖y-sourceAdaptedClosingMap hp φ N‖ ∧
          (∀ x ∈ ball φ (quantitativeInverseJointRadius r 2 (4*K)),
            sourceAdaptedClosingMap hp x N = y → x = ψ) ∧
          ∀ n : ℤ, N ≤ n.natAbs →
            let ζ := weightedResonantDiagonalCenter hp SpectralWeight.one (sourceWeightedPeriodOne ψ) n;
            (weightedResonantBMinusExtension hp SpectralWeight.one (sourceWeightedPeriodOne ψ) n ζ = y.fst (-n) ∧
              weightedResonantBPlusExtension hp SpectralWeight.one (sourceWeightedPeriodOne ψ) n ζ = y.snd n) ∧
            (y.fst (-n) = 0 → y.snd n = 0 →
              (∀ z ∈ resonantStrip n, z ∈ periodicSpectrum hp (periodOnePotential ψ) ↔ z = ζ) ∧
              ∀ z ∈ resonantStrip n,
                analyticOrderNatAt (resonantDeterminantExtension hp SpectralWeight.one
                  (sourceWeightedPeriodOne ψ) n) z = if z = ζ then 2 else 0) := by
  let K := resonantCenterRemainderBallConstant p (‖φ‖+1)
  obtain ⟨N₂,_,V,hoV,hφ,h₂⟩ := exists_uniform_sourceResonantCenterClosing hp hp1 φ
  obtain ⟨r,hr,N₁,hN₁,hV,h₁⟩ := exists_uniform_sourceAdaptedClosingInverse_within
    hp hp1 φ V hoV hφ
  refine ⟨r,hr,max N₁ N₂,hN₁.trans (le_max_left _ _),?_⟩
  intro N hN
  obtain ⟨hmem,g,hg,hga,hinv⟩ := h₁ N (by omega)
  have hρ : quantitativeInverseJointRadius r 2 (4*K) < r :=
    (min_le_left _ _).trans_lt (half_lt_self hr)
  have hsmall : ball φ (quantitativeInverseJointRadius r 2 (4*K)) ⊆ ball φ r := ball_subset_ball hρ.le
  refine ⟨g,hg,hga,?_⟩
  intro y hy
  have hi := hinv y hy
  have hψr := hsmall hi.1
  refine ⟨hi.1,hi.2.1,hi.2.2.1,hi.2.2.2,?_⟩
  intro n hn
  have hc := sourceAdaptedClosingInverse_coefficients hp (g y) y N (hmem (g y) hψr) hi.2.1 n hn
  refine ⟨hc,?_⟩
  intro hym hyp
  have hclosed := h₂ (g y) (hV hψr) n (by omega)
    (hc.2.trans hyp) (hc.1.trans hym)
  exact hclosed

end NLS.ZakharovShabat
