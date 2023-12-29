import HasPrimitives.Basic
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

open Set BigOperators

open scoped Interval

/-- Given a function `f` and curve `γ`, `CurvInt` is the integral from `t₁` to `t₂` of
  `f (γ t) * γ'(t)`. -/
noncomputable def CurvInt (t₁ t₂ : ℝ) (f : ℂ → ℂ) (γ : ℝ → ℂ) : ℂ :=
   ∫ t in t₁..t₂, deriv γ t • f (γ t)



-- ADDING 12/18/23 from Heather ** NOt needed?***
-- Put near `derivWithin_zero_of_nmem_closure`
-- theorem hasDerivWithinAt_of_nmem_closure {𝕜 : Type*} [NontriviallyNormedField 𝕜] {F : Type*}
--     [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : 𝕜 → F} {x : 𝕜} {f' : F} {s : Set 𝕜}
--     (h : x ∉ closure s) : HasDerivWithinAt f f' s x := sorry
--  .of_nhdsWithin_eq_bot <| eq_bot_mono (nhdsWithin_mono _ (diff_subset _ _)) <| by
--    rwa [mem_closure_iff_nhdsWithin_neBot, not_neBot] at h
-- #exit
--   rw [HasDerivWithinAt, HasDerivAtFilter]
--   apply fderivWithin_zero_of_isolated




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
  -- can assume `t₁ ≤ t₂`
  wlog ht : t₁ ≤ t₂
  · sorry
  -- get a homotopy `γ` through differentiable curves
  obtain ⟨γ, hU, hcont, hdiff, h_start_γ₀, h_end_γ₁, h_start_t, h_end_t⟩ := hom
  have icc_is : [[t₁, t₂]] = Icc t₁ t₂ := by simp [ht]
  -- the image of `γ`, called `K`, is compact
  let K := γ '' (Icc 0 1 ×ˢ [[t₁, t₂]])
  have K_cpt : IsCompact K
  · refine IsCompact.image_of_continuousOn ?hK.hs hcont
    refine IsCompact.prod ?_ (isCompact_uIcc (a := t₁) (b := t₂))
    have := isCompact_uIcc (a := (0:ℝ)) (b := 1)
    rwa [(by simp : [[(0 : ℝ), 1]] = Icc 0 1)] at this
  -- fix an `ε` so that all `z ∈ K` are at least `3 * ε` from `U` complement
  have : ∃ ε > 0, ∀ z ∈ K, Metric.ball z (3 * ε) ⊆ U := sorry
  obtain ⟨ε, ε_pos, ε_ballWithinU⟩ := this
  -- By compactness, there is a `δ` so that if `s₁` and `s₂` are within `δ` of each other, then
  -- `γ ⟨s₁, t⟩` and `γ ⟨s₂, t⟩` are within `ε` of each other, uniformly in `t`
  have : ∃ δ > 0, ∀ s₁ ∈ Icc 0 1, ∀ s₂ ∈ Icc 0 1, ∀ t ∈ [[t₁, t₂]], |s₁ - s₂| < δ →
    Complex.abs (γ ⟨s₁, t⟩ - γ ⟨s₂, t⟩) < ε := sorry
  obtain ⟨δ, δ_pos, δ_UnifCont⟩ := this
  -- It suffices to show that `CurvInt` is the same if `s₁` and `s₂` differ by at most `δ`
  suffices : ∀ s₁ ∈ Icc 0 1, ∀ s₂ ∈ Icc 0 1, |s₁ - s₂| < δ →
    CurvInt t₁ t₂ f (fun t ↦ γ ⟨s₁, t⟩) = CurvInt t₁ t₂ f (fun t ↦ γ ⟨s₂,t⟩)
  · -- the interval `[0, 1]` can be covered by finitely many intervals of length at most `δ`
    -- Note: only need `s` from `0` to `N`, but just make `s` constant after `N`
    have : ∃ s : ℕ → ℝ, ∃ N, s 0 = 0 ∧ s N = 1 ∧
      ∀ i, s i ∈ Icc 0 1 ∧ |s i - s (i + 1)| < δ := sorry
    obtain ⟨s, N, s₀, s₁, s_diff⟩ := this
    -- Claim: `CurvInt` at `s i` is equal to that at `s 0`
    have : ∀ i, CurvInt t₁ t₂ f (fun t ↦ γ ⟨s 0, t⟩) = CurvInt t₁ t₂ f (fun t ↦ γ ⟨s i, t⟩) := sorry
    -- Now use this fact with `i = N`
    convert this N using 1
    · -- `CurvInt` at `s 0` is equal to that on `γ₀`
      rw [s₀]
      apply intervalIntegral.integral_congr
      intro t ht'
      simp_rw [h_start_γ₀ t ht']
      congr! 1
      sorry
    · -- `CurvInt` at `s N` is equal to that on `γ₁`
      rw [s₁]
      apply intervalIntegral.integral_congr
      intro t ht'
      simp_rw [h_end_γ₁ t ht']
      congr! 1
      sorry
  · -- given `s₁` and `s₂` in `[0, 1]` that differ by at most `δ`, we want to show that
    -- their `CurvInt`s are equal
    intro s₁ hs₁ s₂ hs₂ hdiff
    -- make a sequence `t i` of points from `t₁` to `t₂` such that `γ ⟨s₁, t i⟩` and `γ ⟨s₂, t i⟩`
    --  are within `ε` of each other
    have : ∃ t : ℕ → ℝ, ∃ N : ℕ, t 0 = t₁ ∧ t N = t₂ ∧
      ∀ i, t i ∈ [[t₁, t₂]] ∧ Complex.abs (γ ⟨s₁, t i⟩  - γ ⟨s₁, t (i + 1)⟩) < ε := sorry
    obtain ⟨t, N, t0_eq_t₁, tN_eq_t₂, t_diff⟩ := this
    -- make `2 * ε` balls centered at each `γ ⟨s₁, t i⟩`
    let D : ℕ → Set ℂ := fun i ↦ Metric.ball (γ ⟨s₁, t i⟩) (2 * ε)
    -- there are sequences `tz i` and `tw i` of points starting at `t₁` and ending at `t₂` such
    -- that both `γ ⟨s₁, tz i⟩` and `γ ⟨s₂, tw i⟩` are in `D i` and `D (i + 1)`
    have : ∃ tz tw : ℕ → ℝ, tz 0 = t₁ ∧ tw 0 = t₁ ∧ tz (N + 1) = t₂ ∧ tw (N + 1) = t₂ ∧
      ∀ i, γ ⟨s₁, tz i⟩ ∈ D i ∧ γ ⟨s₂, tw i⟩ ∈ D i ∧
        γ ⟨s₁, tz i⟩ ∈ D (i + 1) ∧ γ ⟨s₂, tw i⟩ ∈ D (i + 1) := sorry
    obtain ⟨tz, tw, tz₀, tw₀, tz_N, tw_N, h_tz_tw⟩ := this
    -- on each disc `D i`, `f` has a primitive `F i`
    have : ∃ F : ℕ → ℂ → ℂ, ∀ i, ∀ z ∈ D i, HasDerivAt (F i) (f z) z := sorry
    obtain ⟨F, hF⟩ := this
    -- primitives differ by a constant
    have : ∃ C : ℕ → ℂ, ∀ i, ∀ z ∈ D i, z ∈ D (i + 1) → F (i + 1) z = F i z + C i := sorry
    obtain ⟨C, hC⟩ := this
    -- so the `CurvInt` from `tz i` to `tz (i + 1)`
    -- is equal to `F i (γ ⟨s₁, tz (i + 1)⟩) - F i (γ ⟨s₁, tz i⟩)`
    have tz_CurvInt : ∀ i,
      CurvInt (tz i) (tz (i + 1)) f (fun t ↦ γ ⟨s₁, t⟩) =
        F i (γ ⟨s₁, tz (i + 1)⟩) - F i (γ ⟨s₁, tz i⟩) := sorry
    have tw_CurvInt : ∀ i,
      CurvInt (tw i) (tw (i + 1)) f (fun t ↦ γ ⟨s₂, t⟩) =
        F i (γ ⟨s₂, tw (i + 1)⟩) - F i (γ ⟨s₂, tw i⟩) := sorry
    -- the `CurvInt` at `s₁` is equal to the sum of the `CurvInt`s from `tz 0` to `tz (N + 1)`
    have CurvInt_eq_tz : CurvInt t₁ t₂ f (fun t ↦ γ ⟨s₁, t⟩) =
      ∑ i in Finset.range (N + 1), CurvInt (tz i) (tz (i + 1)) f (fun t ↦ γ ⟨s₁, t⟩) := sorry
    rw [CurvInt_eq_tz]
    -- the `CurvInt` at `s₂` is equal to the sum of the `CurvInt`s from `tw 0` to `tw (N + 1)`
    have CurvInt_eq_tw : CurvInt t₁ t₂ f (fun t ↦ γ ⟨s₂, t⟩) =
      ∑ i in Finset.range (N + 1), CurvInt (tw i) (tw (i + 1)) f (fun t ↦ γ ⟨s₂, t⟩) := sorry
    rw [CurvInt_eq_tw]
    -- almost there...



#exit


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
