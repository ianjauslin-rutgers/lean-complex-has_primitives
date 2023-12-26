import HasPrimitives.Basic
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

open Set

open scoped Interval

/-- Given a function `f` and curve `γ`, `CurvInt` is the integral from `t₁` to `t₂` of
  `f (γ t) * γ'(t)`. -/
noncomputable def CurvInt (t₁ t₂ : ℝ) (f : ℂ → ℂ) (γ : ℝ → ℂ) : ℂ :=
   ∫ t in t₁..t₂, deriv γ t • f (γ t)

-- TO DO: move to `Mathlib.Data.Intervals.UnorderedInterval` (Yael add API?)
def uIoo {α : Type*} [LinearOrder α]  : α → α → Set α := fun a b => Ioo (a ⊓ b) (a ⊔ b)

-- TO DO: move to `Mathlib.Data.Intervals.UnorderedInterval` (Yael add API?)
theorem uIoo_comm {α : Type*} [LinearOrder α] [Lattice α] (a : α) (b : α) :
    uIoo a b = uIoo b a := by
  sorry
  -- dsimp [uIoo]
  -- rw [inf_comm (a := a) (b := b), sup_comm]
  --   --, inf_comm, sup_comm]


-- -- TO DO: move to `Mathlib.Data.Intervals.UnorderedInterval` (Yael add API?)
-- --@[simp]
-- lemma uIoo_of_le {α : Type*} [LinearOrder α] [Lattice α] {a : α} {b : α} (h : a ≤ b) :
--     uIoo a b = Ioo a b := by
--   simp [uIoo, inf_eq_left.mpr h, sup_eq_right.mpr h]
--   --simp [uIoo, h, inf_eq_left.mpr h, sup_eq_right.mpr h]
-- #exit

-- -- an open interval is equal to a closed one up to measure zero
-- lemma uIoo_eqM_uIcc (a b : ℝ) : uIoo a b =ᵐ[MeasureTheory.volume] uIcc a b := by
--   wlog h : a ≤ b
--   · convert this b a (by linarith) using 1
--     · rw [uIoo_comm]
--     · rw [uIcc_comm]
--   rw [uIcc_of_le h, uIoo_of_le h]
--   refine MeasureTheory.ae_eq_set.mpr ?_
--   constructor
--   · -- convert volume of empty is zero
--     convert MeasureTheory.measure_empty using 2
--     refine diff_eq_empty.mpr ?h.e'_2.h.e'_3.a
--     exact Ioo_subset_Icc_self
--   · rw [Icc_diff_Ioo_same h]
--     refine Finite.measure_zero ?right.h MeasureTheory.volume
--     exact toFinite {a, b}

/-- If a function `f` on an open domain `U` has a primitive, then it is holomorphic. -/
theorem holomorphic_of_primitive {f F : ℂ → ℂ} {U : Set ℂ} (U_open : IsOpen U)
    (F_primitive : ∀ z ∈ U, HasDerivAt F (f z) z) :
    DifferentiableOn ℂ f U := by
  have F_analyticOn : AnalyticOn ℂ F U :=
    DifferentiableOn.analyticOn U_open (hd := fun z hz ↦ ⟨_, (F_primitive z hz).hasDerivWithinAt⟩)
  have f_analyticOn : AnalyticOn ℂ f U :=
    F_analyticOn.deriv.congr U_open (fun z hz ↦ (F_primitive z hz).deriv)
  exact f_analyticOn.differentiableOn

-- move near `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le`
theorem intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le' {E : Type*} [NormedAddCommGroup E] [CompleteSpace E] [NormedSpace ℝ E] {f : ℝ → E} {f' : ℝ → E} {a : ℝ} {b : ℝ} (hab : a ≤ b) (hcont : ContinuousOn f (Icc a b)) (hderiv : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x) (hInt : IntervalIntegrable f' MeasureTheory.volume a b) :
∫ (y : ℝ) in a..b, f' y = f b - f a :=
    integral_eq_sub_of_hasDeriv_right_of_le hab hcont
      (fun x hx ↦ (hderiv x hx).hasDerivWithinAt) hInt

-- idea: try to use `[[t₁, t₂]]` as much as possible (even though `t₁ ≤ t₂` is known)
/-- Main theorem: if `f` has primitive `F` and `γ` is continuously differentiable in `U`, then
  `∫ t in t₁..t₂, f (γ t) * γ'(t) dt = F (γ t₂) - F (γ t₁)`. -/
theorem curvInt_eval_of_primitive {t₁ t₂ : ℝ} (ht : t₁ ≤ t₂) {γ γ' : ℝ → ℂ} {f F : ℂ → ℂ}
    {U : Set ℂ} (U_open : IsOpen U) (γ_in_U : ∀ t, t ∈ [[t₁, t₂]] → γ t ∈ U)
    (F_prim : ∀ z ∈ U, HasDerivAt F (f z) z)
    (γ_deriv : ∀ t ∈ [[t₁, t₂]], HasDerivAt γ (γ' t) t)
    (γ_cont : ContinuousOn γ ([[t₁, t₂]]))
    (γ'_cont : ContinuousOn γ' ([[t₁, t₂]])) :
    CurvInt t₁ t₂ f γ = F (γ t₂) - F (γ t₁) := by
  have F_differentiableOn : DifferentiableOn ℂ F U := fun z hz ↦
    (F_prim z hz).differentiableAt.differentiableWithinAt
  have f_holo : DifferentiableOn ℂ f U := holomorphic_of_primitive U_open F_prim
  have uIcc_eq_Icc : [[t₁, t₂]] = Icc t₁ t₂ := by simp [ht]
  have cont₁ : ∀ t ∈ [[t₁, t₂]], ContinuousWithinAt (fun {t₂} => F (γ t₂)) ([[t₁, t₂]]) t
  · intro t ht'
    rw [uIcc_eq_Icc] at γ_cont γ_in_U ht' ⊢
    apply ContinuousWithinAt.comp (s := Icc t₁ t₂) (hf := γ_cont.continuousWithinAt ht')
      (t := γ '' Icc t₁ t₂) (h := mapsTo_image γ (Icc t₁ t₂))
    apply ContinuousAt.continuousWithinAt
    apply (F_prim (γ t) (γ_in_U t ht')).continuousAt
  have cont₂ : ∀ t ∈ [[t₁, t₂]], ContinuousWithinAt (fun y => deriv γ y • f (γ y)) [[t₁, t₂]] t
  · intro t ht'
    rw [uIcc_eq_Icc] at γ'_cont γ_deriv γ_in_U ht' ⊢
    apply ContinuousWithinAt.smul
    · exact (γ'_cont.continuousWithinAt ht').congr (fun y hy ↦ (γ_deriv y hy).deriv) (γ_deriv t ht').deriv
    · apply ContinuousWithinAt.comp (s := Icc t₁ t₂) --(hf := γ_cont.continuousWithinAt ?_)
        (t := γ '' Icc t₁ t₂) (h := mapsTo_image γ (Icc t₁ t₂))
      · apply ContinuousAt.continuousWithinAt
        have := (f_holo (γ t) (γ_in_U t ht')).differentiableAt (U_open.mem_nhds (γ_in_U t ht'))
        exact this.continuousAt
      · exact (γ_deriv t ht').continuousAt.continuousWithinAt
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht (f := F ∘ γ) ?_ ?_ (ContinuousOn.intervalIntegrable (fun t ht' ↦ cont₂ t ht'))
  · intro t ht'
    rw [uIcc_eq_Icc] at γ_cont γ_in_U
    apply ContinuousOn.continuousWithinAt
    apply ContinuousOn.comp (s := Icc t₁ t₂) (t := γ '' Icc t₁ t₂) (h := mapsTo_image γ (Icc t₁ t₂))
      (hf := γ_cont)
    · intro z hz
      refine (F_prim z ?_).differentiableAt.continuousAt.continuousWithinAt (s := γ '' Icc t₁ t₂)
      obtain ⟨t', ht'', ht'''⟩ := hz
      rw [← ht''']
      exact γ_in_U t' ht''
    · exact ht'
  · intro t ht'
    have := mem_Icc_of_Ioo ht'
    rw [uIcc_eq_Icc] at γ_in_U γ_deriv
    convert HasDerivAt.comp (h₂ := F) (h := γ) (x := t) (h₂' := f (γ t)) (h' := deriv γ t) (F_prim (γ t)
      (γ_in_U t this)) ?_ using 1
    · simp only [smul_eq_mul]; ring
    · rw [hasDerivAt_deriv_iff]
      exact (γ_deriv t this).differentiableAt

/-- Two curves are `Homotopic` in `U` if there exists a homotopy through differentiable curves -/
def Homotopic (t₁ t₂ : ℝ) (γ₀ γ₁ : ℝ → ℂ) (U : Set ℂ) : Prop := ∃ (γ : ℝ × ℝ → ℂ),
    (γ '' (Icc 0 1 ×ˢ [[t₁, t₂]]) ⊆ U) ∧ -- image is contained in U
    (ContinuousOn γ (Icc 0 1 ×ˢ [[t₁, t₂]])) ∧ -- jointly continuous
    (∀ t ∈ [[t₁, t₂]], γ ⟨0, t⟩ = γ₀ t) ∧ (∀ t ∈ [[t₁, t₂]], γ ⟨1, t⟩ = γ₁ t) ∧ -- starts at γ₀ and ends at γ₁
    (∀ s ∈ Icc 0 1, γ ⟨s, t₁⟩ = γ₀ t₁) ∧ (∀ s ∈ Icc 0 1, γ ⟨s, t₂⟩ = γ₁ t₂) -- fixed endpoints

theorem Homotopic.symm (t₁ t₂ : ℝ) (γ₀ γ₁ : ℝ → ℂ) (U : Set ℂ)
    (h : Homotopic t₁ t₂ γ₀ γ₁ U) : Homotopic t₂ t₁ γ₀ γ₁ U := by
  sorry

/-- Two curves are `DifferentiablyHomotopic` in `U` if there exists a homotopy through differentiable curves -/
def DifferentiablyHomotopic (t₁ t₂ : ℝ) (γ₀ γ₁ : ℝ → ℂ) (U : Set ℂ) : Prop := ∃ (γ : ℝ × ℝ → ℂ),
    (γ '' (Icc 0 1 ×ˢ [[t₁, t₂]]) ⊆ U) ∧ -- image is contained in U
    (ContinuousOn γ (Icc 0 1 ×ˢ [[t₁, t₂]])) ∧ -- jointly continuous
    (∀ s ∈ Icc 0 1, DifferentiableOn ℝ γ ({s} ×ˢ (uIoo t₁ t₂))) ∧ -- differentiable in second variable
    (∀ t ∈ [[t₁, t₂]], γ ⟨0, t⟩ = γ₀ t) ∧ (∀ t ∈ [[t₁, t₂]], γ ⟨1, t⟩ = γ₁ t) ∧ -- starts at γ₀ and ends at γ₁
    (∀ s ∈ Icc 0 1, γ ⟨s, t₁⟩ = γ₀ t₁) ∧ (∀ s ∈ Icc 0 1, γ ⟨s, t₂⟩ = γ₁ t₂) -- fixed endpoints


/-- If two curves are `DiffHomotopic`, then the `CurvInt` of a holomorphic function over the two curves is the same. -/
theorem curvInt_eq_of_diffHomotopic {t₁ t₂ : ℝ} {γ₀ γ₁ : ℝ → ℂ} {f : ℂ → ℂ} {U : Set ℂ}
    (hom : DifferentiablyHomotopic t₁ t₂ γ₀ γ₁ U)
    (f_holo : DifferentiableOn ℂ f U) :
    CurvInt t₁ t₂ f γ₀ = CurvInt t₁ t₂ f γ₁ := by
  wlog ht : t₁ ≤ t₂
  · sorry
  obtain ⟨γ, hU, hcont, hdiff, h₀, h₁, h₂, h₃⟩ := hom
  have icc_is : [[t₁, t₂]] = Icc t₁ t₂ := by simp [ht]
  let K := γ '' (Icc 0 1 ×ˢ [[t₁, t₂]])
  have K_cpt : IsCompact K
  · refine IsCompact.image_of_continuousOn ?hK.hs hcont
    refine IsCompact.prod ?_ (isCompact_uIcc (a := t₁) (b := t₂))
    have := isCompact_uIcc (a := (0:ℝ)) (b := 1)
    rwa [(by simp : [[(0 : ℝ), 1]] = Icc 0 1)] at this
  have : ∃ ε > 0, ∀ z ∈ K, Metric.ball z (3 * ε) ⊆ U := sorry
  obtain ⟨ε, ε_pos, ε_ballWithinU⟩ := this
  have : ∃ δ > 0, ∀ s₁ ∈ Icc 0 1, ∀ s₂ ∈ Icc 0 1, ∀ t ∈ [[t₁, t₂]], |s₁ - s₂| < δ →
    Complex.abs (γ ⟨s₁, t⟩ - γ ⟨s₂, t⟩) < ε := sorry
  obtain ⟨δ, δ_pos, δ_UnifCont⟩ := this
  suffices : ∀ s₁ ∈ Icc 0 1, ∀ s₂ ∈ Icc 0 1, |s₁ - s₂| < δ →
    CurvInt t₁ t₂ f (fun t ↦ γ ⟨s₁, t⟩) = CurvInt t₁ t₂ f (fun t ↦ γ ⟨s₂,t⟩)
  · have : ∃ s : ℕ → ℝ, ∃ N, s 0 = 0 ∧ s N = 1 ∧
      ∀ i < N, s i ∈ Icc 0 1 ∧ |s i - s (i+1)| < δ := sorry
    obtain ⟨s, N, s₀, s₁, s_diff⟩ := this
    have : ∀ i ≤ N, CurvInt t₁ t₂ f (fun t ↦ γ ⟨s 0, t⟩) = CurvInt t₁ t₂ f (fun t ↦ γ ⟨s i, t⟩) := sorry
    convert this N (by simp) using 1
    · rw [s₀]
      apply intervalIntegral.integral_congr
      intro t ht'
      simp_rw [h₀ t ht']
      congr! 1
      sorry
    · rw [s₁]
      apply intervalIntegral.integral_congr
      intro t ht'
      simp_rw [h₁ t ht']
      congr! 1
      sorry
  · intro s₁ hs₁ s₂ hs₂ hdiff
    sorry -- main Stein-Shakarchi argument p. 95



-- #exit
--     obtain ⟨s, N, s₀, s₁, s_diff⟩ := this
--     have : ∀ i ∈ Fin N, CurvInt t₁ t₂ f (fun t ↦ γ ⟨s i, t⟩) = CurvInt t₁ t₂ f (fun t ↦ γ ⟨s (i+1),t⟩)
--     · intro i hi
--       exact this (s i) (mem_Icc.mpr ⟨s_diff i hi, s_diff (i+1) (Fin.succ_mem hi)⟩) (s (i+1)) (mem_Icc.mpr ⟨s_diff i hi, s_diff (i+1) (Fin.succ_mem hi)⟩)
--     rw [← Fin.sum_const_zero (CurvInt t₁ t₂ f (fun t ↦ γ ⟨s 0, t⟩))]
--     simp only [Fin.sum_range_succ, this]
-- #exit
--     rw [← h₀, ← h₁]
--     exact this 0 (by simp) 1 (by simp) (by linarith)
--   ·

--   sorry

-- #exit

theorem DifferentiablyHomotopic_of_OpenHomotopic {t₁ t₂ : ℝ} {γ₀ γ₁ : ℝ → ℂ} {U : Set ℂ} (U_open : IsOpen U) (γ₀_diffble : DifferentiableOn ℝ γ₀ (Ioo t₁ t₂))
(γ₁_diffble : DifferentiableOn ℝ γ₁ (Ioo t₁ t₂))
    (h : Homotopic t₁ t₂ γ₀ γ₁ U) : DifferentiablyHomotopic t₁ t₂ γ₀ γ₁ U := by
  sorry


theorem curvInt_eq_of_homotopic {t₁ t₂ : ℝ} {γ₀ γ₁ : ℝ → ℂ} {f : ℂ → ℂ} {U : Set ℂ}
    (U_open : IsOpen U) (hom : Homotopic t₁ t₂ γ₀ γ₁ U)
    (γ₀_diffble : DifferentiableOn ℝ γ₀ (Ioo t₁ t₂))
    (γ₁_diffble : DifferentiableOn ℝ γ₁ (Ioo t₁ t₂))
    (f_holo : DifferentiableOn ℂ f U) :
    CurvInt t₁ t₂ f γ₀ = CurvInt t₁ t₂ f γ₁ :=
  curvInt_eq_of_diffHomotopic (DifferentiablyHomotopic_of_OpenHomotopic
    U_open γ₀_diffble γ₁_diffble hom) f_holo


-- main theorem: holomorphic functions on simply connected open sets have primitives
theorem HasPrimitivesOfSimplyConnected (U : Set ℂ) (hSc : SimplyConnectedSpace U) (hO : IsOpen U) :
    HasPrimitives U := by
  sorry
