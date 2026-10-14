import NLS.ZakharovShabat.SourceStandardRootGapSideSourceImproper

/-!
# Actual gap-side traces and endpoint integrals

The side trace is identified with the arbitrary-approach limit of the actual
standard root. Its affine path integral is defined using the trace and the
actual half-gap Jacobian, then identified with the earlier weighted integral.
-/

noncomputable section
open Set Complex Filter MeasureTheory
open scoped ENNReal Topology
namespace NLS.ZakharovShabat

/-- The affine closed gap is exactly the actual canonical periodic segment. -/
theorem sourceStandardRoot_gapSegment_eq_periodicSegment {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ) :
    standardRootGapSegment (sourceStandardRootMidpoint hp hp1 ψ n)
      (sourceStandardRootHalfGap hp hp1 ψ n) = sourcePeriodicSegment hp hp1 ψ n := by
  apply Set.Subset.antisymm
  · rintro z ⟨t,ht,rfl⟩
    refine ⟨(1-t)/2,(1+t)/2,by linarith [ht.2],by linarith [ht.1],by ring,?_⟩
    simp only [Complex.real_smul]
    dsimp [sourceStandardRootMidpoint,sourceStandardRootHalfGap,
      canonicalPeriodicMidpoint,canonicalPeriodicGap]
    push_cast
    ring
  · rintro z ⟨a,b,ha,hb,hab,rfl⟩
    refine ⟨b-a,⟨by linarith,by linarith⟩,?_⟩
    change (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n+
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)/2+
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n-
        canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)/2*((b-a : ℝ):ℂ) = _
    simp only [Complex.real_smul,Complex.ofReal_sub]
    have habC : (a : ℂ)+(b : ℂ) = 1 := by exact_mod_cast hab
    linear_combination
      -((canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n+
        canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)/2)*habC

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Coordinate -1 is the actual left periodic endpoint. -/
theorem sourceStandardRoot_gap_left_endpoint (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) :
    sourceStandardRootMidpoint hp hp1 ψ n+sourceStandardRootHalfGap hp hp1 ψ n*(-1 : ℂ) =
      canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n := by
  dsimp [sourceStandardRootMidpoint,sourceStandardRootHalfGap,
    canonicalPeriodicMidpoint,canonicalPeriodicGap]
  ring

/-- Coordinate 1 is the actual right periodic endpoint. -/
theorem sourceStandardRoot_gap_right_endpoint (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) :
    sourceStandardRootMidpoint hp hp1 ψ n+sourceStandardRootHalfGap hp hp1 ψ n*(1 : ℂ) =
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n := by
  dsimp [sourceStandardRootMidpoint,sourceStandardRootHalfGap,
    canonicalPeriodicMidpoint,canonicalPeriodicGap]
  ring

/-- The upper or lower boundary value of the actual selected standard root. -/
def sourceStandardRootSideTrace (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    (n : ℤ) (t : ℝ) (upper : Bool) : ℂ :=
  (if upper then -sourceStandardRootHalfGap hp hp1 ψ n*Complex.I
    else sourceStandardRootHalfGap hp hp1 ψ n*Complex.I)*(Real.sqrt (1-t^2) : ℂ)

/-- These trace values are actual limits from the corresponding open side. -/
theorem sourceStandardRoot_tendsto_sideTrace (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ)
    (hg : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠ 0)
    (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) (upper : Bool) :
    Tendsto (sourceStandardRoot hp hp1 ψ n)
      (𝓝[if upper then standardRootGapUpperSide (sourceStandardRootMidpoint hp hp1 ψ n)
          (sourceStandardRootHalfGap hp hp1 ψ n)
        else standardRootGapLowerSide (sourceStandardRootMidpoint hp hp1 ψ n)
          (sourceStandardRootHalfGap hp hp1 ψ n)]
        (sourceStandardRootMidpoint hp hp1 ψ n+sourceStandardRootHalfGap hp hp1 ψ n*(t:ℂ)))
      (𝓝 (sourceStandardRootSideTrace hp hp1 ψ n t upper)) := by
  cases upper
  · exact sourceStandardRoot_tendsto_gap_lower_side hp hp1 ψ n t hg ht.1 ht.2
  · exact sourceStandardRoot_tendsto_gap_upper_side hp hp1 ψ n t hg ht.1 ht.2

/-- Each side trace is continuous in the closed gap coordinate, including its endpoints. -/
theorem sourceStandardRootSideTrace_continuous (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) (upper : Bool) :
    Continuous (fun t : ℝ => sourceStandardRootSideTrace hp hp1 ψ n t upper) := by
  unfold sourceStandardRootSideTrace
  fun_prop

/-- The actual affine Jacobian divided by the selected root's side trace. -/
def sourceStandardRootSideIntegrand (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    (n : ℤ) (f : ℂ → ℂ) (upper : Bool) (r : ℝ) : ℂ :=
  f (sourceStandardRootMidpoint hp hp1 ψ n+sourceStandardRootHalfGap hp hp1 ψ n*(r:ℂ))*
    (sourceStandardRootHalfGap hp hp1 ψ n/sourceStandardRootSideTrace hp hp1 ψ n r upper)

/-- The oriented affine side integral between two gap coordinates. -/
def sourceStandardRootSideIntegral (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    (n : ℤ) (f : ℂ → ℂ) (a b : ℝ) (upper : Bool) : ℂ :=
  ∫ r in a..b, sourceStandardRootSideIntegrand hp hp1 ψ n f upper r

/-- The trace-based integral is the independently defined straight side path integral. -/
theorem sourceStandardRootSideIntegral_eq_path (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) (f : ℂ → ℂ) (a b : ℝ) (upper : Bool) :
    sourceStandardRootSideIntegral hp hp1 ψ n f a b upper =
      gapSidePathIntegral (sourceStandardRootMidpoint hp hp1 ψ n)
        (sourceStandardRootHalfGap hp hp1 ψ n) f a b upper := rfl

/-- Continuous data on the actual gap give genuine integrability even at the branch points. -/
theorem sourceStandardRootSideIntegrand_intervalIntegrable (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ)
    (hg : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠ 0)
    (f : ℂ → ℂ) (hf : ContinuousOn f (sourcePeriodicSegment hp hp1 ψ n))
    (a b : ℝ) (ha : a ∈ Icc (-1 : ℝ) 1) (hb : b ∈ Icc (-1 : ℝ) 1) (upper : Bool) :
    IntervalIntegrable (sourceStandardRootSideIntegrand hp hp1 ψ n f upper) volume a b := by
  apply gapSidePathIntegrand_intervalIntegrable
  · exact div_ne_zero hg (by norm_num)
  · rwa [sourceStandardRoot_gapSegment_eq_periodicSegment]
  · exact ha
  · exact hb

/-- The exact signed substitution from the proof of corrected Lemma 10.4. -/
theorem sourceStandardRootSideIntegral_eq_weighted (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ)
    (hg : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠ 0)
    (f : ℂ → ℂ) (a b : ℝ) (ha : a ∈ Icc (-1 : ℝ) 1) (hb : b ∈ Icc (-1 : ℝ) 1)
    (upper : Bool) :
    sourceStandardRootSideIntegral hp hp1 ψ n f a b upper =
      (if upper then Complex.I else -Complex.I)*∫ r in a..b,
        f (sourceStandardRootMidpoint hp hp1 ψ n+sourceStandardRootHalfGap hp hp1 ψ n*(r:ℂ))/
          (Real.sqrt (1-r^2):ℂ) :=
  gapSidePathIntegral_eq_weighted _ _ f a b ha hb (div_ne_zero hg (by norm_num)) upper

/-- At every stopping point the side integral also equals its regular cosine pullback. -/
theorem sourceStandardRootSideIntegral_eq_boundary (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ)
    (hg : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠ 0)
    (f : ℂ → ℂ) (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) (upper : Bool) :
    sourceStandardRootSideIntegral hp hp1 ψ n f (-1) t upper =
      gapSideBoundaryIntegral (sourceStandardRootMidpoint hp hp1 ψ n)
        (sourceStandardRootHalfGap hp hp1 ψ n) f t upper :=
  gapSidePathIntegral_eq_boundary _ _ f t (div_ne_zero hg (by norm_num)) ht.1 ht.2 upper

/-- Omitting the singular left endpoint converges to the actual full side integral. -/
theorem sourceStandardRootSideIntegral_tendsto (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ)
    (hg : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠ 0)
    (f : ℂ → ℂ) (hf : ContinuousOn f (sourcePeriodicSegment hp hp1 ψ n))
    (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) (upper : Bool) :
    Tendsto (fun ε : ℝ => sourceStandardRootSideIntegral hp hp1 ψ n f (-1+ε) t upper)
      (𝓝[>] (0 : ℝ)) (𝓝 (sourceStandardRootSideIntegral hp hp1 ψ n f (-1) t upper)) := by
  rw [sourceStandardRootSideIntegral_eq_boundary hp hp1 ψ n hg f t ht upper]
  apply sourceStandardRoot_gapSidePathIntegral_tendsto hp hp1 ψ n hg f
  · rwa [sourceStandardRoot_gapSegment_eq_periodicSegment]
  · exact ht.1
  · exact ht.2

/-- Omitting both endpoints converges to the full side integral between the two branch points. -/
theorem sourceStandardRootSideIntegral_double_trunc_tendsto (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ)
    (hg : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠ 0)
    (f : ℂ → ℂ) (hf : ContinuousOn f (sourcePeriodicSegment hp hp1 ψ n)) (upper : Bool) :
    Tendsto (fun ε : ℝ => sourceStandardRootSideIntegral hp hp1 ψ n f (-1+ε) (1-ε) upper)
      (𝓝[>] (0 : ℝ)) (𝓝 (sourceStandardRootSideIntegral hp hp1 ψ n f (-1) 1 upper)) := by
  rw [sourceStandardRootSideIntegral_eq_boundary hp hp1 ψ n hg f 1 (by norm_num) upper]
  apply sourceStandardRoot_gapSidePathIntegral_double_trunc_tendsto hp hp1 ψ n hg f
  rwa [sourceStandardRoot_gapSegment_eq_periodicSegment]

end NLS.ZakharovShabat
