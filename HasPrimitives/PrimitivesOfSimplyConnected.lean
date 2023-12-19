import HasPrimitives.Basic



open scoped Interval

noncomputable def CurvInt (t₁ t₂ : ℝ) (f : ℂ → ℂ) (γ : ℝ → ℂ) : ℂ :=
   ∫ t in t₁..t₂, deriv γ t • f (γ t)

-- TO DO: move to `Mathlib.Data.Set.Intervals.UnorderedInterval` (Yael add API?)
def Set.uIoo {α : Type*} [LinearOrder α]  : α → α → Set α := fun a b => Set.Ioo (min a b) (max a b)

-- TO DO: move to `Mathlib.Data.Set.Intervals.UnorderedInterval` (Yael add API?)
theorem Set.uIoo_comm {α : Type*} [LinearOrder α] [Lattice α] (a : α) (b : α) : Set.uIoo a b = Set.uIoo b a := sorry

-- TO DO: move to `Mathlib.Data.Set.Intervals.UnorderedInterval` (Yael add API?)
theorem Set.uIoo_of_le {α : Type*} [LinearOrder α] [Lattice α] {a : α} {b : α} (h : a ≤ b) :
    Set.uIoo a b = Set.Ioo a b := sorry

-- an open interval is equal to a closed one up to measure zero
lemma uIoo_eqM_uIcc (a b : ℝ) : Set.uIoo a b =ᵐ[MeasureTheory.volume] Set.uIcc a b := by
  wlog h : a ≤ b
  · convert this b a (by linarith) using 1
    · rw [Set.uIoo_comm]
    · rw [Set.uIcc_comm]
  rw [Set.uIcc_of_le h, Set.uIoo_of_le h]
  refine MeasureTheory.ae_eq_set.mpr ?_
  constructor
  · -- convert volume of empty is zero
    convert MeasureTheory.measure_empty using 2
    refine Set.diff_eq_empty.mpr ?h.e'_2.h.e'_3.a
    exact Set.Ioo_subset_Icc_self
  · rw [Set.Icc_diff_Ioo_same h]
    refine Set.Finite.measure_zero ?right.h MeasureTheory.volume
    exact Set.toFinite {a, b}


-- example (a b : ℝ) (p : ℝ → Prop) (h : ∀ x ∈ Set.uIoo a b, p x) : ∀ᵐ (x : ℝ) ∂MeasureTheory.volume, x ∈ [[a, b]] → p x := by
--     filter_upwards [uIoo_eqM_uIcc a b]
--     intro x hx hx'
--     rw [← hx] at hx'


-- #exit

-- move near `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le`
theorem intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le' {E : Type*} [NormedAddCommGroup E] [CompleteSpace E] [NormedSpace ℝ E] {f : ℝ → E} {f' : ℝ → E} {a : ℝ} {b : ℝ} (hab : a ≤ b) (hcont : ContinuousOn f (Set.Icc a b)) (hderiv : ∀ x ∈ Set.Ioo a b, HasDerivAt f (f' x) x) (hint : IntervalIntegrable f' MeasureTheory.volume a b) :
∫ (y : ℝ) in a..b, f' y = f b - f a := by sorry


theorem curvInt_eval_of_primitive {t₁ t₂ : ℝ} (ht : t₁ ≤ t₂) {γ : ℝ → ℂ} {f F : ℂ → ℂ} {U : Set ℂ}
    (U_open : IsOpen U) (γ_in_U : ∀ t, t ∈ [[t₁, t₂]] → γ t ∈ U)
    (F_holo : DifferentiableOn ℂ F U)
    (F_prim : Set.EqOn (deriv F) f U)
    (hγ : DifferentiableOn ℝ γ ([[t₁, t₂]])) :
    CurvInt t₁ t₂ f γ = F (γ t₂) - F (γ t₁) := by
  dsimp [CurvInt]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le


#exit
  convert intervalIntegral.integral_deriv_eq_sub (f := F ∘ γ) (a := t₁) (b := t₂) ?_ ?_ using 1
  · apply intervalIntegral.integral_congr_ae
    filter_upwards [uIoo_eqM_uIcc t₁ t₂]
    intro t ht ht'
    have : t ∈ Set.uIoo t₁ t₂
    ·

#exit
    have : Set.uIoo t₁ t₂ ⊆ [[t₁, t₂]] := sorry
    filter_upwards [this]
    intro t ht
    simp only
    rw [deriv.comp (h₂ := F) (h := γ) (x := t), F_prim (γ_in_U t ht)]; ring
    · apply F_holo.differentiableAt
      rw [mem_nhds_iff]
      exact ⟨U, Eq.subset rfl, U_open, γ_in_U t ht⟩
    · apply hγ.differentiableAt
      rw [mem_nhds_iff]
      exact ⟨[[t₁, t₂]], Eq.subset rfl, is_open_Icc, ht⟩



#exit
  have := @intervalIntegral.integral_deriv_eq_sub ℂ _ _ _ (F ∘ γ) t₁ t₂ ?_ ?_
  convert @intervalIntegral.integral_deriv_eq_sub ℂ _ _ _ (F ∘ γ) t₁ t₂ ?_ ?_
  · convert (deriv.comp (h₂ := F) (h := γ) _ ?_ ?_).symm using 1
    ·
  -- apply deriv_comp
--

  · ext1 t
    have := @deriv.comp ℝ _ t ℂ _ _ γ F --(F_holo (γ t) (γ_in_U t (hγ t).1 (hγ t).2)) --(hγ t).1 (F_holo (γ t) (γ_in_U t (hγ t).1 (hγ t).2))
    --ext1 t

    -- chain rule for derivatives
    have h₁ : deriv (F ∘ γ) t = deriv F (γ t) * deriv γ t := deriv.comp_deriv_eq_deriv_comp _ _ _
  sorry

-- main theorem: holomorphic functions on simply connected open sets have primitives
theorem HasPrimitivesOfSimplyConnected (U : Set ℂ) (hSc : SimplyConnectedSpace U) (hO : IsOpen U) :
    HasPrimitives U := by
  sorry
