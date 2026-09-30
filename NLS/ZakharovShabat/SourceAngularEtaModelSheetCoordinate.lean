import NLS.ZakharovShabat.SourceAngularEtaPrescribedSheet

/-!
# Logarithmic eta coordinates on regular prescribed sheets

The selected prescribed root satisfies the same quadratic equation as
the canonical standard root. Its logarithmic spectral coordinate is
analytic and nonzero on every regular sheet of an open gap, including
on the cut interior. At either periodic endpoint it has the common
nonzero boundary value `endpoint - midpoint`, independent of the sheet.
-/

noncomputable section
open Set Filter Topology Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def sourceAngularEtaModelSheetCoordinate (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (ψ : CoeffPair p) (w z : ℂ) : ℂ :=
  z-sourceStandardRootMidpoint hp hp1 ψ n-sourceAngularEtaSelectedSheetRoot hp hp1 n ψ w z

theorem sourceAngularEtaSelectedSheetRoot_sq_eq_quadratic
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (ψ : CoeffPair p) (w z : ℂ)
    (hw : w ≠ 0) (hz : z ∈ sourceStandardRootOmittedDomain hp hp1 ψ n) :
    sourceAngularEtaSelectedSheetRoot hp hp1 n ψ w z^2 =
      quadraticRootPolynomial (sourceStandardRootMidpoint hp hp1 ψ n)
        ((canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)^2/4) z := by
  rw [sourceAngularEtaSelectedSheetRoot_sq hp hp1 n ψ w z hw hz,
    sourcePeriodicPair_factorization hp hp1 ψ n z]
  simp only [quadraticRootPolynomial,sourceStandardRootMidpoint,sub_sq_comm]

theorem sourceAngularEtaModelSheetCoordinate_analyticOnNhd
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (ψ : CoeffPair p) (w : ℂ)
    (c : ℂ) (R : ℝ)
    (hother : closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n)
    (hdata : SourceAngularEndpointSpectralData hp hp1 ψ n) :
    AnalyticOnNhd ℂ (sourceAngularEtaModelSheetCoordinate hp hp1 n ψ w)
      (sourceAngularRegularSheetDisc hp ψ c R w) :=
  (analyticOnNhd_id.sub analyticOnNhd_const).sub
    (sourceAngularEtaSelectedSheetRoot_analyticOnNhd hp hp1 n ψ w c R hother hdata)

/-- The open gap makes the logarithmic coordinate nonzero even on
the interior cut, without choosing either canonical approach. -/
theorem sourceAngularEtaModelSheetCoordinate_ne_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (ψ : CoeffPair p) (w z : ℂ)
    (hw : w ≠ 0) (hz : z ∈ sourceStandardRootOmittedDomain hp hp1 ψ n)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠ 0) :
    sourceAngularEtaModelSheetCoordinate hp hp1 n ψ w z ≠ 0 := by
  intro hzero
  have heq : sourceAngularEtaSelectedSheetRoot hp hp1 n ψ w z =
      z-sourceStandardRootMidpoint hp hp1 ψ n := by
    change z-sourceStandardRootMidpoint hp hp1 ψ n-sourceAngularEtaSelectedSheetRoot hp hp1 n ψ w z = 0 at hzero
    linear_combination -hzero
  have hsq := sourceAngularEtaSelectedSheetRoot_sq_eq_quadratic hp hp1 n ψ w z hw hz
  rw [heq] at hsq
  apply pow_ne_zero 2 hgap
  dsimp only [quadraticRootPolynomial] at hsq
  linear_combination 4*hsq

theorem I_mul_sourceAngularEtaModelSheetIntegrand
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (ψ : CoeffPair p) (w z : ℂ) :
    I*sourceAngularEtaModelSheetIntegrand hp hp1 n ψ w z =
      -(sourceAngularEtaSelectedSheetRoot hp hp1 n ψ w z)⁻¹ := by
  rw [sourceAngularEtaModelSheetIntegrand_eq_selectedRoot]
  simp only [div_eq_mul_inv,← mul_assoc,I_mul_I,neg_one_mul]

/-- The prescribed coordinate has logarithmic derivative `i` times
the literal prescribed-sheet model differential. -/
theorem hasDerivAt_sourceAngularEtaModelSheetCoordinate
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (ψ : CoeffPair p) (w : ℂ) (hw : w ≠ 0)
    (c : ℂ) (R : ℝ)
    (hother : closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n)
    (hdata : SourceAngularEndpointSpectralData hp hp1 ψ n)
    (z : ℂ) (hz : z ∈ sourceAngularRegularSheetDisc hp ψ c R w) :
    HasDerivAt (sourceAngularEtaModelSheetCoordinate hp hp1 n ψ w)
      ((I*sourceAngularEtaModelSheetIntegrand hp hp1 n ψ w z)*
        sourceAngularEtaModelSheetCoordinate hp hp1 n ψ w z) z := by
  let Q := sourceAngularEtaSelectedSheetRoot hp hp1 n ψ w
  let τ := sourceStandardRootMidpoint hp hp1 ψ n
  let d := (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)^2/4
  have hQne : Q z ≠ 0 := sourceAngularEtaSelectedSheetRoot_ne_zero hp hp1 n ψ w z hw hz.2
    (hother (ball_subset_closedBall hz.1))
  have hQa : AnalyticAt ℂ Q z :=
    sourceAngularEtaSelectedSheetRoot_analyticOnNhd hp hp1 n ψ w c R hother hdata z hz
  have hsq : (fun u => Q u^2) =ᶠ[𝓝 z] quadraticRootPolynomial τ d := by
    filter_upwards [isOpen_ball.mem_nhds hz.1] with u hu
    exact sourceAngularEtaSelectedSheetRoot_sq_eq_quadratic hp hp1 n ψ w u hw
      (hother (ball_subset_closedBall hu))
  have hQd := hasDerivAt_root_of_sq_eq_quadratic Q τ d z hQa hQne hsq
  have h := ((hasDerivAt_id z).sub_const τ).sub hQd
  change HasDerivAt (sourceAngularEtaModelSheetCoordinate hp hp1 n ψ w) (1-(z-τ)/Q z) z at h
  rw [I_mul_sourceAngularEtaModelSheetIntegrand]
  convert h using 1
  unfold sourceAngularEtaModelSheetCoordinate
  change -(Q z)⁻¹*(z-τ-Q z) = 1-(z-τ)/Q z
  field_simp [hQne]
  ring

/-- The selected sheet root tends to zero at either periodic endpoint
along every approach inside the enclosing disc, irrespective of sign. -/
theorem sourceAngularEtaSelectedSheetRoot_tendsto_endpoint_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (ψ : CoeffPair p) (w : ℂ) (hw : w ≠ 0)
    (c : ℂ) (R : ℝ)
    (hother : closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n)
    (a : ℂ) (ha : a ∈
      ({canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n,
        canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n} : Set ℂ)) :
    Tendsto (sourceAngularEtaSelectedSheetRoot hp hp1 n ψ w) (𝓝[ball c R] a) (𝓝 0) := by
  apply tendsto_zero_of_sq_tendsto_zero
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  have hpoly : Tendsto (fun z : ℂ => (l-z)*(r-z)) (𝓝[ball c R] a) (𝓝 0) := by
    have hc : Continuous (fun z : ℂ => (l-z)*(r-z)) := by fun_prop
    have h0 : (l-a)*(r-a) = 0 := by
      simp only [mem_insert_iff,mem_singleton_iff] at ha
      rcases ha with rfl | rfl <;> simp [l,r]
    simpa only [h0] using (hc.continuousAt (x := a)).tendsto.mono_left
      (show 𝓝[ball c R] a ≤ 𝓝 a from nhdsWithin_le_nhds)
  apply hpoly.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact (sourceAngularEtaSelectedSheetRoot_sq hp hp1 n ψ w z hw
    (hother (ball_subset_closedBall hz))).symm

/-- The model coordinate has sheet-independent endpoint limits. -/
theorem sourceAngularEtaModelSheetCoordinate_tendsto_endpoint
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (ψ : CoeffPair p) (w : ℂ) (hw : w ≠ 0)
    (c : ℂ) (R : ℝ)
    (hother : closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n)
    (a : ℂ) (ha : a ∈
      ({canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n,
        canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n} : Set ℂ)) :
    Tendsto (sourceAngularEtaModelSheetCoordinate hp hp1 n ψ w) (𝓝[ball c R] a)
      (𝓝 (a-sourceStandardRootMidpoint hp hp1 ψ n)) := by
  have h := ((tendsto_id.mono_left nhdsWithin_le_nhds).sub
    (tendsto_const_nhds (x := sourceStandardRootMidpoint hp hp1 ψ n))).sub
      (sourceAngularEtaSelectedSheetRoot_tendsto_endpoint_zero hp hp1 n ψ w hw c R hother a ha)
  change Tendsto (fun z => z-sourceStandardRootMidpoint hp hp1 ψ n-
    sourceAngularEtaSelectedSheetRoot hp hp1 n ψ w z) (𝓝[ball c R] a)
    (𝓝 (a-sourceStandardRootMidpoint hp hp1 ψ n))
  simpa only [id_eq,sub_zero] using h

theorem sourceAngularEtaModelSheetCoordinate_endpoint_value
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (ψ : CoeffPair p) (w : ℂ) (hw : w ≠ 0)
    (a : ℂ) (hother : a ∈ sourceStandardRootOmittedDomain hp hp1 ψ n)
    (ha : a ∈
      ({canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n,
        canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n} : Set ℂ)) :
    sourceAngularEtaModelSheetCoordinate hp hp1 n ψ w a = a-sourceStandardRootMidpoint hp hp1 ψ n := by
  have hroot : sourceAngularEtaSelectedSheetRoot hp hp1 n ψ w a = 0 := by
    apply sq_eq_zero_iff.mp
    rw [sourceAngularEtaSelectedSheetRoot_sq hp hp1 n ψ w a hw hother]
    simp only [mem_insert_iff,mem_singleton_iff] at ha
    rcases ha with rfl | rfl <;> simp
  simp only [sourceAngularEtaModelSheetCoordinate,hroot,sub_zero]

theorem sourceAngularEtaModelSheetCoordinate_continuousWithinAt_endpoint
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (ψ : CoeffPair p) (w : ℂ) (hw : w ≠ 0)
    (c : ℂ) (R : ℝ)
    (hother : closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n)
    (a : ℂ) (haBall : a ∈ ball c R) (ha : a ∈
      ({canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n,
        canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n} : Set ℂ)) :
    ContinuousWithinAt (sourceAngularEtaModelSheetCoordinate hp hp1 n ψ w) (ball c R) a := by
  change Tendsto _ (𝓝[ball c R] a) (𝓝 (sourceAngularEtaModelSheetCoordinate hp hp1 n ψ w a))
  rw [sourceAngularEtaModelSheetCoordinate_endpoint_value hp hp1 n ψ w hw a
    (hother (ball_subset_closedBall haBall)) ha]
  exact sourceAngularEtaModelSheetCoordinate_tendsto_endpoint hp hp1 n ψ w hw c R hother a ha

end NLS.ZakharovShabat
