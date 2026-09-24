import NLS.ZakharovShabat.SourceCriticalRootRatioGapSideRegularity
import NLS.ZakharovShabat.RealGapCanonicalRootWeightedIntegral

/-!
# The weighted action integral on the upper side of an open real gap

The recentered action integrand has a regular numerator on the closed
gap. Pulling its upper-side path integral back to the real gap identifies
it with the weighted canonical-root boundary integral.
-/

noncomputable section
open Set Complex Filter MeasureTheory intervalIntegral
open scoped ENNReal Topology
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The regular numerator of the recentered action along a selected gap. -/
def sourceActionGapNumerator (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) (q : ℝ) (z : ℂ) : ℂ :=
  (z-(q:ℂ)) * sourceCriticalRootGapNumerator hp hp1 ψ n z

/-- The weighted numerator stays continuous through both endpoints. -/
theorem sourceActionGapNumerator_continuousOn
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ) (q : ℝ) :
    ContinuousOn (sourceActionGapNumerator hp hp1 ψ n q)
      (standardRootGapSegment
        (sourceStandardRootMidpoint hp hp1 ψ n)
        (sourceStandardRootHalfGap hp hp1 ψ n)) := by
  exact (continuousOn_id.sub continuousOn_const).mul
    (sourceCriticalRootGapNumerator_continuousOn hp hp1 ψ hreal n)

/-- The upper weighted path integral is the actual weighted real-gap
boundary integral. -/
theorem sourceAction_upper_gapSidePathIntegral_eq_realIntegral
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re)
    (q : ℝ) :
    gapSidePathIntegral
      (sourceStandardRootMidpoint hp hp1 ψ n)
      (sourceStandardRootHalfGap hp hp1 ψ n)
      (sourceActionGapNumerator hp hp1 ψ n q) (-1) 1 true =
      ∫ x in
        (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
          (periodOnePotential_mem ψ) n).re..
        (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
          (periodOnePotential_mem ψ) n).re,
        ((x-q:ℝ):ℂ) *
          (deriv (canonicalDiscriminant hp (periodOnePotential ψ)) (x:ℂ) /
            realGapCanonicalRootUpperValue hp hp1 ψ n x) := by
  let τ := sourceStandardRootMidpoint hp hp1 ψ n
  let δ := sourceStandardRootHalfGap hp hp1 ψ n
  let a := (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n).re
  let b := (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n).re
  let d : ℝ := (b-a)/2
  let F := sourceCriticalRootGapNumerator hp hp1 ψ n
  let D (z : ℂ) := deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z
  let U := realGapCanonicalRootUpperValue hp hp1 ψ n
  have hδ : δ = (d:ℂ) :=
    sourceStandardRootHalfGap_eq_ofReal_affineJacobian hp hp1 ψ hreal n
  have hδne : δ ≠ 0 :=
    sourceStandardRootHalfGap_ne_zero_of_openRealGap hp hp1 ψ hreal n hopen
  have hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n ≠ 0 := by
    intro h
    have hzero : δ = 0 := by
      change canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n / 2 = 0
      rw [h]
      simp
    exact hδne hzero
  obtain ⟨W,_,_,hWreal,hWdom⟩ :=
    exists_global_source_gapPoint_mem_omittedDomain hp hp1
  have hψ : ψ ∈ W := hWreal hreal
  have hkernel (t : ℝ) (ht : t ∈ Ioo (-1) 1) :
      F (τ+δ*(t:ℂ)) *
        (δ / (-δ*I * (Real.sqrt (1-t^2):ℂ))) =
      d • (D (realGapAffinePoint hp hp1 ψ n t:ℂ) /
        U (realGapAffinePoint hp hp1 ψ n t)) := by
    have hdom := hWdom ψ hψ n t ht.1.le ht.2.le
    have hz : τ+δ*(t:ℂ) = (realGapAffinePoint hp hp1 ψ n t:ℂ) :=
      sourceCanonicalRootGapPoint_eq_ofReal_realGapAffinePoint
        hp hp1 ψ hreal n t
    have hi : realGapInverseCoordinate hp hp1 ψ n
        (realGapAffinePoint hp hp1 ψ n t) = t :=
      realGapInverseCoordinate_affine hp hp1 ψ n hopen t
    have hfactor :=
      discriminant_derivative_div_canonicalRootGapUpperValue_eq_selectedFactor
        hp hp1 ψ n t hgap ht hdom
    change D (τ+δ*(t:ℂ)) /
        sourceCanonicalRootGapUpperValue hp hp1 ψ n t =
      F (τ+δ*(t:ℂ)) /
        (-δ*I*(Real.sqrt (1-t^2):ℂ)) at hfactor
    rw [← hz]
    change F (τ+δ*(t:ℂ)) *
        (δ / (-δ*I*(Real.sqrt (1-t^2):ℂ))) =
      d • (D (τ+δ*(t:ℂ)) /
        sourceCanonicalRootGapUpperValue hp hp1 ψ n
          (realGapInverseCoordinate hp hp1 ψ n
            (realGapAffinePoint hp hp1 ψ n t)))
    rw [hi, hfactor, hδ]
    change F (τ+(d:ℂ)*(t:ℂ)) *
        ((d:ℂ) / (-(d:ℂ)*I*(Real.sqrt (1-t^2):ℂ))) =
      (d:ℂ) * (F (τ+(d:ℂ)*(t:ℂ)) /
        (-(d:ℂ)*I*(Real.sqrt (1-t^2):ℂ)))
    ring
  change (∫ t in (-1:ℝ)..1,
    ((τ+δ*(t:ℂ))-(q:ℂ)) * F (τ+δ*(t:ℂ)) *
      (δ / (-δ*I*(Real.sqrt (1-t^2):ℂ)))) =
    ∫ x in a..b, ((x-q:ℝ):ℂ) * (D (x:ℂ) / U x)
  calc
    _ = ∫ t in (-1:ℝ)..1,
        d • (((realGapAffinePoint hp hp1 ψ n t-q:ℝ):ℂ) *
          (D (realGapAffinePoint hp hp1 ψ n t:ℂ) /
            U (realGapAffinePoint hp hp1 ψ n t))) := by
          apply intervalIntegral.integral_congr_uIoo
          intro t ht
          rw [uIoo_of_le (by norm_num : (-1:ℝ) ≤ 1)] at ht
          have hz := sourceCanonicalRootGapPoint_eq_ofReal_realGapAffinePoint
            hp hp1 ψ hreal n t
          change τ+δ*(t:ℂ) = (realGapAffinePoint hp hp1 ψ n t:ℂ) at hz
          dsimp only
          rw [hz]
          calc
            _ = ((realGapAffinePoint hp hp1 ψ n t-q:ℝ):ℂ) *
                (F (τ+δ*(t:ℂ)) *
                  (δ / (-δ*I*(Real.sqrt (1-t^2):ℂ)))) := by
                    rw [hz]
                    push_cast
                    ring
            _ = _ := by rw [hkernel t ht, mul_smul_comm]
    _ = _ := by
      exact integral_affine_gap_coordinate a b
        (fun x : ℝ => ((x-q:ℝ):ℂ) * (D (x:ℂ) / U x))

/-- The weighted side-path kernel is integrable through both branch
points, so its full endpoint integral is well-defined. -/
theorem sourceAction_upper_gapSidePathIntegrand_intervalIntegrable
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re)
    (q : ℝ) :
    IntervalIntegrable
      (fun t : ℝ =>
        sourceActionGapNumerator hp hp1 ψ n q
          (sourceCanonicalRootGapPoint hp hp1 ψ n t) *
        (sourceStandardRootHalfGap hp hp1 ψ n /
          (-sourceStandardRootHalfGap hp hp1 ψ n*I *
            (Real.sqrt (1-t^2):ℂ)))) volume (-1) 1 := by
  exact gapSidePathIntegrand_intervalIntegrable
    (sourceStandardRootMidpoint hp hp1 ψ n)
    (sourceStandardRootHalfGap hp hp1 ψ n)
    (sourceActionGapNumerator hp hp1 ψ n q)
    (sourceStandardRootHalfGap_ne_zero_of_openRealGap hp hp1 ψ hreal n hopen)
    (sourceActionGapNumerator_continuousOn hp hp1 ψ hreal n q)
    (-1) 1 (by norm_num) (by norm_num) true

/-- Removing both branch-point endpoints preserves the weighted upper
side integral in the limit. -/
theorem sourceAction_upper_gapSidePathIntegral_double_trunc_tendsto
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re)
    (q : ℝ) :
    Tendsto (fun ε : ℝ =>
      gapSidePathIntegral
        (sourceStandardRootMidpoint hp hp1 ψ n)
        (sourceStandardRootHalfGap hp hp1 ψ n)
        (sourceActionGapNumerator hp hp1 ψ n q)
        (-1+ε) (1-ε) true)
      (𝓝[>] (0:ℝ))
      (𝓝 (gapSidePathIntegral
        (sourceStandardRootMidpoint hp hp1 ψ n)
        (sourceStandardRootHalfGap hp hp1 ψ n)
        (sourceActionGapNumerator hp hp1 ψ n q) (-1) 1 true)) := by
  let τ := sourceStandardRootMidpoint hp hp1 ψ n
  let δ := sourceStandardRootHalfGap hp hp1 ψ n
  let F := sourceActionGapNumerator hp hp1 ψ n q
  have hδ : δ ≠ 0 :=
    sourceStandardRootHalfGap_ne_zero_of_openRealGap hp hp1 ψ hreal n hopen
  have hF : ContinuousOn F (standardRootGapSegment τ δ) :=
    sourceActionGapNumerator_continuousOn hp hp1 ψ hreal n q
  have hlim := gapSidePathIntegral_double_trunc_tendsto τ δ F hδ hF true
  have hident := gapSidePathIntegral_eq_boundary τ δ F 1 hδ
    (by norm_num) (by norm_num) true
  rw [← hident] at hlim
  exact hlim

/-- The upper weighted side integral is real and nonzero on every open
real-type canonical gap. -/
theorem sourceAction_upper_gapSidePathIntegral_sign
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re)
    (q : ℝ) :
    let W := gapSidePathIntegral
      (sourceStandardRootMidpoint hp hp1 ψ n)
      (sourceStandardRootHalfGap hp hp1 ψ n)
      (sourceActionGapNumerator hp hp1 ψ n q) (-1) 1 true
    W.im = 0 ∧ W ≠ 0 := by
  rw [sourceAction_upper_gapSidePathIntegral_eq_realIntegral
    hp hp1 ψ hreal n hopen q]
  exact realGapCanonicalRootUpper_weighted_integral_sign
    hp hp1 ψ hreal n hopen q

end NLS.ZakharovShabat
