import NLS.ZakharovShabat.ClassicalSeparatedPhysicalChains
import NLS.ZakharovShabat.PhysicalForcedEquation

/-!
# Reconstructing physical boundary chains from forced initial-value solutions

For the actual interval operator, a domain vector whose pencil image is
another domain vector agrees on `[0,1]` with the unique classical forced
solution driven by that source. This is the converse ODE link needed to
recover scalar Taylor jets from generalized eigenvectors.
-/

noncomputable section
open Set Complex MeasureTheory NLS.LinearVolterra NLS.Fourier NLS.ComplexAnalysis
namespace NLS.ZakharovShabat
open BoundaryCondition

/-- The original interval pencil equation gives the corresponding forced
solution on the closed physical unit interval. -/
theorem classicalIntervalDomain_eq_classicalForcedSolution
    (b : BoundaryCondition) (Φ : Curve (ℂ × ℂ))
    (hΦ : MemLp (extend Φ) 2 (volume.restrict (Ioc 0 1)))
    (z : ℂ) (f g : ClassicalIntervalDomain b)
    (he : classicalPencil b (intervalL2OfFunction (extend Φ) hΦ) z f =
      classicalInclusion b g) :
    EqOn (physicalDomain (classicalIntervalEquiv b f).val)
      (classicalForcedSolution Φ z
        (physicalDomainCurve (classicalIntervalEquiv b g).val)
        (physicalDomain (classicalIntervalEquiv b f).val 0)) (Icc 0 1) := by
  let φ := intervalPotentialCoefficients (intervalL2OfFunction (extend Φ) hΦ)
  have hpot : physicalBase φ =ᵐ[volume.restrict (Ioc 0 1)] extend Φ := by
    simpa only [φ,intervalPotentialCoefficients_ofFunction] using
      physicalBase_dirichletPotentialCoefficients_restrict (extend Φ) hΦ
  have hcoeff := congrArg (intervalL2Equiv b) he
  rw [intervalL2Equiv_classicalPencil,intervalL2Equiv_classicalInclusion] at hcoeff
  have hp : spectralPencil (by simp) φ z (classicalIntervalEquiv b f).val =
      domainInclusion (classicalIntervalEquiv b g).val := by
    exact congrArg Subtype.val hcoeff
  exact physicalDomain_eq_classicalForcedSolution φ Φ hpot z
    (classicalIntervalEquiv b f).val (classicalIntervalEquiv b g).val hp

/-- The stored interval function, viewed as a continuous physical curve. -/
def classicalDomainCurve (b : BoundaryCondition) (f : ClassicalIntervalDomain b) :
    Curve (ℂ × ℂ) :=
  ⟨f.val,b.continuous_classicalIntervalDomain f⟩

/-- The interval curve is the restriction of its signed Fourier extension. -/
theorem classicalDomainCurve_eq_physicalDomainCurve
    (b : BoundaryCondition) (f : ClassicalIntervalDomain b) :
    classicalDomainCurve b f = physicalDomainCurve (classicalIntervalEquiv b f).val := by
  apply ContinuousMap.ext
  intro t
  have h := classicalIntervalEquiv_symm_apply b (classicalIntervalEquiv b f) t
  rw [(classicalIntervalEquiv b).symm_apply_apply] at h
  exact h

/-- In original interval coordinates, the domain vector solves the forced
initial-value problem driven by the preceding domain vector. -/
theorem classicalDomainCurve_eq_forced_of_pencil
    (b : BoundaryCondition) (Φ : Curve (ℂ × ℂ))
    (hΦ : MemLp (extend Φ) 2 (volume.restrict (Ioc 0 1)))
    (z : ℂ) (f g : ClassicalIntervalDomain b)
    (he : classicalPencil b (intervalL2OfFunction (extend Φ) hΦ) z f =
      classicalInclusion b g) (t : Icc (0 : ℝ) 1) :
    classicalDomainCurve b f t =
      classicalForcedSolution Φ z (classicalDomainCurve b g)
        (classicalDomainCurve b f ⟨0,by norm_num⟩) t := by
  have h := classicalIntervalDomain_eq_classicalForcedSolution b Φ hΦ z f g he t.property
  rw [classicalDomainCurve_eq_physicalDomainCurve b f,
    classicalDomainCurve_eq_physicalDomainCurve b g]
  exact h

/-- The physical interval curve remembers both endpoint conditions. -/
theorem classicalDomainCurve_left (b : BoundaryCondition)
    (f : ClassicalIntervalDomain b) :
    separatedEndpointDefectCLM b
      (classicalDomainCurve b f ⟨0,by norm_num⟩) = 0 := by
  change (f.val ⟨0,by norm_num⟩).1 -
    extensionSign b * (f.val ⟨0,by norm_num⟩).2 = 0
  exact sub_eq_zero.mpr (b.classicalIntervalDomain_left f)

theorem classicalDomainCurve_right (b : BoundaryCondition)
    (f : ClassicalIntervalDomain b) :
    separatedEndpointDefectCLM b
      (classicalDomainCurve b f ⟨1,by norm_num⟩) = 0 := by
  change (f.val ⟨1,by norm_num⟩).1 -
    extensionSign b * (f.val ⟨1,by norm_num⟩).2 = 0
  exact sub_eq_zero.mpr (b.classicalIntervalDomain_right f)

/-- An initial vector satisfies the left boundary condition precisely when
it is a scalar multiple of the normalized boundary vector. -/
theorem eq_smul_normalized_of_separated_left (b : BoundaryCondition)
    (v : ℂ × ℂ) (hv : separatedEndpointDefectCLM b v = 0) :
    v = v.1 • (1,extensionSign b) := by
  have hleft : v.1 = extensionSign b * v.2 := sub_eq_zero.mp hv
  have hv2 : v.2 = extensionSign b * v.1 := by
    rw [hleft,← mul_assoc,extensionSign_sq,one_mul]
  apply Prod.ext
  · simp
  · simpa only [Prod.smul_snd,smul_eq_mul,mul_comm] using hv2

/-- The zero domain vector has the zero continuous interval curve. -/
@[simp] theorem classicalDomainCurve_zero (b : BoundaryCondition) :
    classicalDomainCurve b (0 : ClassicalIntervalDomain b) = 0 := by
  apply ContinuousMap.ext
  intro t
  rfl

/-- With zero forcing, the forced solution is the homogeneous solution. -/
theorem classicalForcedSolution_zero_source (Φ : Curve (ℂ × ℂ)) (z : ℂ)
    (v : ℂ × ℂ) (t : Icc (0 : ℝ) 1) :
    classicalForcedSolution Φ z 0 v t = classicalSolution Φ z v t := by
  rw [classicalForcedSolution_eq_homogeneous_add]
  have hzero : classicalForcedSolution Φ z 0 0 t = 0 := by
    rw [← classicalChainOperator_apply Φ z 0 t]
    simp
  rw [hzero,add_zero]

/-- Endpoint conditions alone put a finite forced solution in the actual
interval domain, without assuming it came from a scalar Taylor kernel. -/
theorem hasClassicalIntervalDomain_classicalJetSolution_of_endpoints
    (b : BoundaryCondition) (Φ : Curve (ℂ × ℂ)) (z : ℂ)
    (v : ℕ → ℂ × ℂ) (n : ℕ)
    (hleft : separatedEndpointDefectCLM b (v n) = 0)
    (hright : separatedEndpointDefectCLM b
      (classicalJetCurve Φ z v n ⟨1,by norm_num⟩) = 0) :
    HasClassicalIntervalDomain b (classicalJetSolution Φ z v n) := by
  have hc := contDiff_classicalJetSolution Φ z v n
  refine ⟨hasIntervalH1Regularity_of_contDiff hc.fst,
    hasIntervalH1Regularity_of_contDiff hc.snd,?_,?_⟩
  · rw [classicalJetSolution_initial]
    exact sub_eq_zero.mp hleft
  · have h := congrArg (separatedEndpointDefectCLM b)
      (classicalJetSolution_restrict Φ z v n ⟨1,by norm_num⟩)
    exact sub_eq_zero.mp (h.trans hright)

/-- Equality of physical classes recovers equality of continuous domain
curves, including the endpoint values. -/
theorem classicalDomainCurve_eq_jetCurve_of_inclusion_eq
    (b : BoundaryCondition) (Φ : Curve (ℂ × ℂ)) (z : ℂ)
    (v : ℕ → ℂ × ℂ) (n : ℕ) (g : ClassicalIntervalDomain b)
    (hv : HasClassicalIntervalDomain b (classicalJetSolution Φ z v n))
    (he : classicalInclusion b g = classicalJetPhysical Φ z v n) :
    classicalDomainCurve b g = classicalJetCurve Φ z v n := by
  have hd : g = classicalDomainOfFunction b (classicalJetSolution Φ z v n) hv := by
    apply classicalInclusion_injective b
    rw [classicalInclusion_ofFunction]
    exact he
  subst g
  apply ContinuousMap.ext
  intro t
  exact (classicalJetSolution_restrict Φ z v n t)

/-- If the source is the physical class of a finite jet, its next domain
vector is the next forced jet determined by its own initial value. -/
theorem classicalDomainCurve_eq_jetCurve_succ_of_pencil
    (b : BoundaryCondition) (Φ : Curve (ℂ × ℂ))
    (hΦ : MemLp (extend Φ) 2 (volume.restrict (Ioc 0 1)))
    (z : ℂ) (v : ℕ → ℂ × ℂ) (n : ℕ)
    (hv : HasClassicalIntervalDomain b (classicalJetSolution Φ z v n))
    (f g : ClassicalIntervalDomain b)
    (he : classicalPencil b (intervalL2OfFunction (extend Φ) hΦ) z f =
      classicalInclusion b g)
    (hg : classicalInclusion b g = classicalJetPhysical Φ z v n)
    (t : Icc (0 : ℝ) 1) :
    classicalDomainCurve b f t = classicalForcedSolution Φ z
      (classicalJetCurve Φ z v n) (classicalDomainCurve b f ⟨0,by norm_num⟩) t := by
  rw [classicalDomainCurve_eq_forced_of_pencil b Φ hΦ z f g he t,
    classicalDomainCurve_eq_jetCurve_of_inclusion_eq b Φ z v n g hv hg]

/-- A pointwise identity with a domain curve identifies the corresponding
physical `L²` classes. -/
theorem classicalJetPhysical_eq_inclusion_of_curve_eq
    (b : BoundaryCondition) (Φ : Curve (ℂ × ℂ)) (z : ℂ)
    (v : ℕ → ℂ × ℂ) (n : ℕ) (f : ClassicalIntervalDomain b)
    (hv : HasClassicalIntervalDomain b (classicalJetSolution Φ z v n))
    (he : classicalDomainCurve b f = classicalJetCurve Φ z v n) :
    classicalJetPhysical Φ z v n = classicalInclusion b f := by
  have hd : classicalDomainOfFunction b (classicalJetSolution Φ z v n) hv = f := by
    apply Subtype.ext
    funext t
    exact (classicalJetSolution_restrict Φ z v n t).trans
      (congrArg (fun c : Curve (ℂ × ℂ) => c t) he.symm)
  rw [← hd,classicalInclusion_ofFunction]
  rfl

/-- Every physical generalized eigenvector has a compatible finite
initial-value chain, with both separated endpoint conditions at each level. -/
theorem exists_classicalJet_of_mem_classicalRootSpace (b : BoundaryCondition)
    (Φ : Curve (ℂ × ℂ))
    (hΦ : MemLp (extend Φ) 2 (volume.restrict (Ioc 0 1)))
    (z : ℂ) (n : ℕ) (x : IntervalPairL2)
    (hx : x ∈ b.classicalRootSpace (intervalL2OfFunction (extend Φ) hΦ) z (n+1)) :
    ∃ v : ℕ → ℂ × ℂ,
      (∀ j ≤ n, separatedEndpointDefectCLM b (v j) = 0) ∧
      (∀ j ≤ n, separatedEndpointDefectCLM b
        (classicalJetCurve Φ z v j ⟨1,by norm_num⟩) = 0) ∧
      classicalJetPhysical Φ z v n = x := by
  induction n generalizing x with
  | zero =>
    obtain ⟨f,hf,hp⟩ := (b.mem_classicalRootSpace_succ _ z 0 x).mp hx
    have hp0 : classicalPencil b (intervalL2OfFunction (extend Φ) hΦ) z f = 0 := by
      simpa using hp
    let v : ℕ → ℂ × ℂ := fun _ => classicalDomainCurve b f ⟨0,by norm_num⟩
    have hcurve : classicalDomainCurve b f = classicalJetCurve Φ z v 0 := by
      apply ContinuousMap.ext
      intro t
      have h := classicalDomainCurve_eq_forced_of_pencil b Φ hΦ z f 0
        (by simpa using hp0) t
      simpa only [classicalDomainCurve_zero,classicalForcedSolution_zero_source,
        classicalJetCurve_zero,classicalSolutionCurve_apply] using h
    refine ⟨v,?_,?_,?_⟩
    · intro j hj
      have : j = 0 := by omega
      subst j
      exact classicalDomainCurve_left b f
    · intro j hj
      have : j = 0 := by omega
      subst j
      rw [← hcurve]
      exact classicalDomainCurve_right b f
    · have hv : HasClassicalIntervalDomain b (classicalJetSolution Φ z v 0) :=
        hasClassicalIntervalDomain_classicalJetSolution_of_endpoints b Φ z v 0
          (classicalDomainCurve_left b f) (by rw [← hcurve]; exact classicalDomainCurve_right b f)
      exact (classicalJetPhysical_eq_inclusion_of_curve_eq b Φ z v 0 f hv hcurve).trans hf
  | succ n ih =>
    obtain ⟨f,hf,hp⟩ := (b.mem_classicalRootSpace_succ _ z (n+1) x).mp hx
    obtain ⟨g,hg⟩ := b.exists_domain_of_mem_classicalRootSpace _ z (n+1)
      (classicalPencil b (intervalL2OfFunction (extend Φ) hΦ) z f) hp
    obtain ⟨v,hl,hr,hv⟩ := ih _ hp
    let v' : ℕ → ℂ × ℂ := Function.update v (n+1)
      (classicalDomainCurve b f ⟨0,by norm_num⟩)
    have hprev : ∀ j ≤ n, v' j = v j := by
      intro j hj
      simp only [v',Function.update_apply,if_neg (show j ≠ n+1 by omega)]
    have hcurveprev : classicalJetCurve Φ z v' n = classicalJetCurve Φ z v n :=
      classicalJetCurve_congr Φ z v' v n hprev
    have hcurve : classicalDomainCurve b f = classicalJetCurve Φ z v' (n+1) := by
      apply ContinuousMap.ext
      intro t
      have hp' : classicalPencil b (intervalL2OfFunction (extend Φ) hΦ) z f =
          classicalInclusion b g := hg.symm
      rw [classicalDomainCurve_eq_jetCurve_succ_of_pencil b Φ hΦ z v n
        (hasClassicalIntervalDomain_classicalJetSolution_of_endpoints b Φ z v n
          (hl n le_rfl) (hr n le_rfl)) f g hp' (hg.trans hv.symm) t,
        classicalJetCurve_succ_apply,hcurveprev]
      simp [v']
    refine ⟨v',?_,?_,?_⟩
    · intro j hj
      by_cases h : j ≤ n
      · rw [hprev j h]
        exact hl j h
      · have heq : j = n+1 := by omega
        subst j
        simpa [v'] using classicalDomainCurve_left b f
    · intro j hj
      by_cases h : j ≤ n
      · rw [classicalJetCurve_congr Φ z v' v j (fun k hk => hprev k (by omega))]
        exact hr j h
      · have heq : j = n+1 := by omega
        subst j
        rw [← hcurve]
        exact classicalDomainCurve_right b f
    · have hdom : HasClassicalIntervalDomain b (classicalJetSolution Φ z v' (n+1)) :=
        hasClassicalIntervalDomain_classicalJetSolution_of_endpoints b Φ z v' (n+1)
          (by simpa [v'] using classicalDomainCurve_left b f)
          (by rw [← hcurve]; exact classicalDomainCurve_right b f)
      exact (classicalJetPhysical_eq_inclusion_of_curve_eq b Φ z v' (n+1) f hdom hcurve).trans hf

/-- The left endpoint condition allows recovery of the finite scalar
Taylor coefficients from the vector initial values. -/
theorem separatedSignedInitialJet_of_left_conditions (b : BoundaryCondition)
    (v : ℕ → ℂ × ℂ) (n : ℕ)
    (hl : ∀ j ≤ n, separatedEndpointDefectCLM b (v j) = 0)
    (j : ℕ) (hj : j ≤ n) :
    separatedSignedInitialJet b (n+1)
      (fun k => (-1 : ℂ)^k.val * (v k.val).1) j = v j := by
  have hlt : j < n+1 := by omega
  rw [eq_smul_normalized_of_separated_left b (v j) (hl j hj)]
  simp only [separatedSignedInitialJet,dif_pos hlt,smul_smul]
  have hsign : (-1 : ℂ)^j * (-1 : ℂ)^j = 1 := by
    calc
      (-1 : ℂ)^j * (-1 : ℂ)^j = ((-1 : ℂ)^j)^2 := by ring
      _ = ((-1 : ℂ)^2)^j := by rw [← pow_mul,← pow_mul]; congr 1; omega
      _ = 1 := by norm_num
  rw [← mul_assoc,hsign,one_mul]

/-- Every finite physical generalized eigenspace is exhausted by the scalar
Taylor-kernel construction. -/
theorem classicalSeparatedJetRootMap_surjective (b : BoundaryCondition)
    (Φ : Curve (ℂ × ℂ))
    (hΦ : MemLp (extend Φ) 2 (volume.restrict (Ioc 0 1)))
    (z : ℂ) (n : ℕ) :
    Function.Surjective (classicalSeparatedJetRootMap b Φ hΦ z n) := by
  intro x
  obtain ⟨v,hl,hr,hv⟩ := exists_classicalJet_of_mem_classicalRootSpace
    b Φ hΦ z n x.val x.property
  let w : Fin (n+1) → ℂ := fun k => (-1 : ℂ)^k.val * (v k.val).1
  have hcongr (j : ℕ) (hj : j ≤ n) :
      classicalJetCurve Φ z (separatedSignedInitialJet b (n+1) w) j =
        classicalJetCurve Φ z v j := by
    apply classicalJetCurve_congr
    intro k hk
    exact separatedSignedInitialJet_of_left_conditions b v n hl k (by omega)
  have hw : w ∈ LinearMap.ker
      (scalarTaylorJetMap (scalarFormalTaylor (classicalSeparatedEndpointSeries b Φ z)) (n+1)) := by
    apply (mem_ker_classicalSeparatedTaylorJetMap_iff b Φ z (n+1) w).mpr
    intro k
    rw [hcongr k.val (by omega)]
    exact hr k.val (by omega)
  refine ⟨⟨w,hw⟩,?_⟩
  apply Subtype.ext
  change classicalJetPhysical Φ z (separatedSignedInitialJet b (n+1) w) n = x.val
  have hinit : ∀ j ≤ n, separatedSignedInitialJet b (n+1) w j = v j :=
    fun j hj => separatedSignedInitialJet_of_left_conditions b v n hl j hj
  have hcurve := classicalJetCurve_congr Φ z (separatedSignedInitialJet b (n+1) w) v n hinit
  have hsolution : classicalJetSolution Φ z (separatedSignedInitialJet b (n+1) w) n =
      classicalJetSolution Φ z v n := by
    cases n with
    | zero => simp only [classicalJetSolution]; rw [hinit 0 le_rfl]
    | succ n =>
      simp only [classicalJetSolution]
      rw [hinit (n+1) le_rfl,
        classicalJetCurve_congr Φ z (separatedSignedInitialJet b (n+1+1) w) v n
          (fun j hj => hinit j (by omega))]
  simpa only [classicalJetPhysical,hsolution] using hv

/-- Finite physical root spaces have exactly the scalar Taylor-kernel
dimension, including the levels before stabilization. -/
theorem finrank_classicalRootSpace_eq_min_analyticOrder
    (b : BoundaryCondition) (Φ : Curve (ℂ × ℂ))
    (hΦ : MemLp (extend Φ) 2 (volume.restrict (Ioc 0 1)))
    (z : ℂ) (m n : ℕ)
    (hm : analyticOrderAt (classicalSeparatedCharacteristic b Φ) z = m) :
    Module.finrank ℂ
      (b.classicalRootSpace (intervalL2OfFunction (extend Φ) hΦ) z (n+1)) =
        min (n+1) m := by
  let e := LinearEquiv.ofBijective (classicalSeparatedJetRootMap b Φ hΦ z n)
    ⟨classicalSeparatedJetRootMap_injective b Φ hΦ z n,
      classicalSeparatedJetRootMap_surjective b Φ hΦ z n⟩
  calc
    _ = Module.finrank ℂ (LinearMap.ker (scalarTaylorJetMap
        (scalarFormalTaylor (classicalSeparatedEndpointSeries b Φ z)) (n+1))) :=
      e.finrank_eq.symm
    _ = min (n+1) m := finrank_classicalSeparatedTaylorKernel b Φ z m (n+1) hm

/-- The analytic order of the classical separated characteristic equals the
algebraic multiplicity of the actual original interval operator. -/
theorem analyticOrder_classicalSeparated_eq_physicalMultiplicity
    (b : BoundaryCondition) (Φ : Curve (ℂ × ℂ))
    (hΦ : MemLp (extend Φ) 2 (volume.restrict (Ioc 0 1)))
    (z : ℂ) (m : ℕ)
    (hm : analyticOrderAt (classicalSeparatedCharacteristic b Φ) z = m) :
    m = b.classicalAlgebraicMultiplicity
      (intervalL2OfFunction (extend Φ) hΦ) z := by
  let u := intervalL2OfFunction (extend Φ) hΦ
  obtain ⟨k,hk⟩ := b.exists_classicalRootSpace_eq_top u z
  have htop : b.classicalRootSpace u z (k+1) = b.classicalRootSpaceTop u z := by
    apply le_antisymm
    · exact le_iSup (b.classicalRootSpace u z) (k+1)
    · rw [← hk]
      exact b.classicalRootSpace_mono u z (Nat.le_succ k)
  have hdim := finrank_classicalRootSpace_eq_min_analyticOrder b Φ hΦ z m k hm
  rw [htop] at hdim
  have hle : b.classicalAlgebraicMultiplicity u z ≤ m := by
    change Module.finrank ℂ (b.classicalRootSpaceTop u z) ≤ m
    rw [hdim]
    exact min_le_right _ _
  exact Nat.le_antisymm (analyticOrder_classicalSeparated_le_physicalMultiplicity b Φ hΦ z m hm) hle

/-- The extended order has the exact physical multiplicity value. -/
theorem analyticOrderAt_classicalSeparated_eq_physicalMultiplicity
    (b : BoundaryCondition) (Φ : Curve (ℂ × ℂ))
    (hΦ : MemLp (extend Φ) 2 (volume.restrict (Ioc 0 1)))
    (z : ℂ) :
    analyticOrderAt (classicalSeparatedCharacteristic b Φ) z =
      (b.classicalAlgebraicMultiplicity
        (intervalL2OfFunction (extend Φ) hΦ) z : ℕ∞) := by
  obtain ⟨m,hm⟩ := ENat.ne_top_iff_exists.mp
    (analyticOrderAt_classicalSeparated_ne_top b Φ hΦ z)
  rw [← hm]
  exact_mod_cast analyticOrder_classicalSeparated_eq_physicalMultiplicity b Φ hΦ z m hm.symm

end NLS.ZakharovShabat
