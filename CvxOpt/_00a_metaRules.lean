import Init.Prelude

import CvxOpt._00_IntroToOptProblems

section meta_rules

variable {D : Type*} {R : Type*} {f: D → R} {S: Set D}

/- Rule 1: min/max transforms -/

/--
Convert a min expression to a max via the equation:

$$
\min_x f(x) = -\max_x (-f(x))
$$
-/
theorem min_obj_to_neg_max_neg_obj
    [OrderedAddCommGroup R]
    {min : R}
    (hmin : MinimumOn f S min)
    : MaximumOn (fun x: D => -(f x)) S (-min)
    := by
        constructor
        case left => simp; exact hmin.left
        simp [upperBounds]
        have hr := hmin.right
        simp [lowerBounds] at hr
        exact hr

/--
Convert a max expression to a min via the equation:

$$
\max_x f(x) = -\min_x (-f(x))
$$
-/
theorem max_obj_to_neg_min_neg_obj
    [OrderedAddCommGroup R]
    {max : R}
    (hmax : MaximumOn f S max)
    : MinimumOn (fun x: D => -(f x)) S (-max)
    := by
        constructor
        case left => simp; exact hmax.left
        simp [lowerBounds]
        have hr := hmax.right
        simp [upperBounds] at hr
        exact hr

/--
Convert an inf expression to a sup via the equation:

$$
\inf_x f(x) = -\sup_x (-f(x))
$$
-/
theorem inf_obj_to_neg_sup_neg_obj
    [OrderedAddCommGroup R]
    {inf: R}
    (hinf : InfimumOn f S inf)
    : SupremumOn (fun x: D => -(f x)) S (-inf)
    := by
        constructor
        case left =>
            simp [upperBounds]
            have hinfl := hinf.left
            simp [lowerBounds] at hinfl
            exact hinfl
        case right =>
            simp [upperBounds, lowerBounds]
            intro y hNegObjLeY
            have hinfr := hinf.right
            simp [upperBounds, lowerBounds] at hinfr
            rw [neg_le]
            apply hinfr
            intro x hXInS
            rw [neg_le]
            exact hNegObjLeY x hXInS
/--
Convert a sup expression to an inf via the equation:

$$
\sup_x f(x) = -\inf_x (-f(x))
$$
-/
theorem sup_obj_to_neg_inf_neg_obj
    [OrderedAddCommGroup R]
    {sup: R}
    (hsup : SupremumOn f S sup)
    : InfimumOn (fun x: D => -(f x)) S (-sup)
    := by
        constructor
        case left =>
            simp [lowerBounds]
            have hsupl := hsup.left
            simp [upperBounds] at hsupl
            exact hsupl
        case right =>
            simp [upperBounds, lowerBounds]
            intro y hYLeNegObj
            have hsupr := hsup.right
            simp [upperBounds, lowerBounds] at hsupr
            rw [le_neg]
            apply hsupr
            intro x hXInS
            rw [le_neg]
            exact hYLeNegObj x hXInS

/--
Convert an argmin expression to an argmax via the equation:

$$
\text{argmin}_x f(x) = \text{argmax}_x (-f(x))
$$
-/
theorem argmin_obj_to_argmax_neg_obj
    [OrderedAddCommGroup R]
    : ArgumentMinimumOn f S = ArgumentMaximumOn (fun x: D => -(f x)) S
    := by
        unfold ArgumentMinimumOn ArgumentMaximumOn
        unfold MinimumOn MaximumOn
        unfold IsLeast IsGreatest
        unfold lowerBounds upperBounds
        simp

/--
Convert an argmax expression to an argmin via the equation:

$$
\text{argmax}_x f(x) = \text{argmin}_x (-f(x))
$$
-/
theorem argmax_obj_to_argmin_neg_obj
    [OrderedAddCommGroup R]
    : ArgumentMaximumOn f S = ArgumentMinimumOn (fun x: D => -(f x)) S
    := by
        unfold ArgumentMinimumOn ArgumentMaximumOn
        unfold MinimumOn MaximumOn
        unfold IsLeast IsGreatest
        unfold lowerBounds upperBounds
        simp

/-
Minimizing over a non-decreasing function φ allows for additional optimal points:

$$
\text{argmin}_x f(x) ⊆ \text{argmin}_x φ(f(x))
$$
-/
theorem argmin_obj_subset_argmin_non_decreasing_comp_obj
    [LinearOrder R]
    (φ : R → R)
    (hφ : MonotoneOn φ (S.image f))
    : ArgumentMinimumOn f S ⊆ ArgumentMinimumOn (φ ∘ f) S
    := by
        unfold ArgumentMinimumOn
        unfold MinimumOn
        unfold IsLeast
        unfold lowerBounds
        simp

        constructor
        case left =>
            intro x1
            simp
            intro hX1InS x2 hX2InS hFEq _ _
            constructor
            case left => exact hX1InS
            exists x2
            constructor
            case right.left => exact hX2InS
            rewrite [hFEq]
            rfl
        case right =>

        intro x1
        simp
        intro hX1InS x2 hX2InS hFEq hX1InS hLeF1ThenF1Le
        constructor
        case left => exact hX1InS
        case right =>
        intro x3 hX3InS
        apply hφ
        exists x1
        exists x3
        apply hLeF1ThenF1Le
        exact hX3InS

/-
Minimizing over an inSreasing function φ does not affect the optimal points:

$$
\text{argmin}_x f(x) = \text{argmin}_x φ(f(x))
$$
-/
theorem argmin_obj_eq_argmin_inSreasing_comp_obj
    [LinearOrder R]
    (φ : R → R)
    (hφ : StrictMonoOn φ (S.image f))
    : ArgumentMinimumOn f S = ArgumentMinimumOn (φ ∘ f) S
    := by
        rw [Set.Subset.antisymm_iff]
        constructor
        case left => exact argmin_obj_subset_argmin_non_decreasing_comp_obj φ (hφ.monotoneOn)
        case right =>

        unfold ArgumentMinimumOn
        unfold MinimumOn
        unfold IsLeast
        unfold lowerBounds
        simp

        constructor
        case left =>
            intro x1
            simp
            intro hX1InS _ _ _ _ _
            constructor
            case left => exact hX1InS
            exists x1
        case right =>

        intro x1
        simp
        intro hX1InS x2 hX2InS hφ2Eqφ1 hX1InS hLeφ1Thenφ1Le
        constructor
        case left => exact hX1InS
        case right =>

        intro x3 hX3InS
        rw [← hφ.le_iff_le]
        case ha => exists x1
        case hb => exists x3
        exact hLeφ1Thenφ1Le x3 hX3InS

/- Rule 2 -/

theorem subset_then_min_le_min
    [LinearOrder R]
    {fmin : R}
    {S2 : Set D}
    {fmin2 : R}
    (min : MinimumOn f S fmin)
    (min2 : MinimumOn f S2 fmin2)
    : S ⊆ S2 → fmin2 ≤ fmin
    := by
    simp [MinimumOn, IsLeast, lowerBounds] at min
    simp [MinimumOn, IsLeast, lowerBounds] at min2

    intro hsubset; rw [Set.subset_def] at hsubset
    induction le_or_lt fmin2 fmin
    case inl h => exact h
    case inr hFMinLtFMin2 =>

    rw [← min.left.choose_spec.right]
    apply min2.right
    apply hsubset
    exact min.left.choose_spec.left

/- Rule 3 -/

theorem sum_min_le_min_sum
    [LinearOrderedField R]
    {g : D → R}
    {fmin : R}
    {gmin : R}
    {fgmin : R}
    (minF : MinimumOn f S fmin)
    (minG : MinimumOn g S gmin)
    (minFG : MinimumOn (fun x => f x + g x) S fgmin)
    : fmin + gmin ≤ fgmin
    := by
    simp [MinimumOn, IsLeast, lowerBounds] at minF
    simp [MinimumOn, IsLeast, lowerBounds] at minG
    simp [MinimumOn, IsLeast, lowerBounds] at minFG

    rw [← minFG.left.choose_spec.right]
    apply add_le_add
    case h₁ =>
        induction le_or_lt fmin (f minFG.left.choose) with
        | inl h => exact h
        | inr h => exact minF.right minFG.left.choose minFG.left.choose_spec.left
    case h₂ =>
        induction le_or_lt gmin (g minFG.left.choose) with
        | inl h => exact h
        | inr h => exact minG.right minFG.left.choose minFG.left.choose_spec.left

/- Rule 4 -/

theorem minx_miny_iff_minxy
    [LinearOrder R]
    {D2 : Type*}
    {S2 : Set D2}
    {f : D → D2 → R}
    {fmin : R}
    {fxmin : D2 → R}
    {hfxmin : ∀ y ∈ S2, MinimumOn (fun x => f x y) S (fxmin y)}
    : MinimumOn fxmin S2 fmin ↔ MinimumOn (fun xy : D × D2 => f xy.1 xy.2) (S ×ˢ S2) fmin
    := by
    simp [MinimumOn, IsLeast, lowerBounds] at hfxmin
    constructor
    case mp =>
        simp [MinimumOn, IsLeast, lowerBounds]
        intro yopt hYoptInS2 hFxminYoptEqFmin hFminLeFxmin
        have xopt := (hfxmin yopt hYoptInS2).left.choose
        constructor
        case left =>
            exists (hfxmin yopt hYoptInS2).left.choose, yopt
            constructor
            case left => exact ⟨(hfxmin yopt hYoptInS2).left.choose_spec.left, hYoptInS2⟩
            case right =>
                rw [(hfxmin yopt hYoptInS2).left.choose_spec.right]
                apply hFxminYoptEqFmin
        case right =>
            intro z x y hXInS hYInS2 fxyEqZ
            rw [← fxyEqZ]
            apply le_trans
            apply hFminLeFxmin y hYInS2
            exact (hfxmin y hYInS2).right x hXInS
    case mpr =>
        simp [MinimumOn, IsLeast, lowerBounds]
        intro xopt yopt hXoptInS hYoptInS2 hFXYoptEqFmin hFminLeF
        constructor
        case left =>
            exists yopt
            constructor
            case left => exact hYoptInS2
            case right =>

            rw [← hFXYoptEqFmin]
            rw [← hFXYoptEqFmin] at hFminLeF
            rw [eq_iff_le_not_lt]
            constructor
            case left => exact (hfxmin yopt hYoptInS2).right xopt hXoptInS
            case right =>

            rw [not_lt]
            apply hFminLeF
            exact (hfxmin yopt hYoptInS2).left.choose_spec.left
            exact hYoptInS2
            exact (hfxmin yopt hYoptInS2).left.choose_spec.right
        case right =>
            intro y hYInS2
            rw [← (hfxmin y hYInS2).left.choose_spec.right]
            apply hFminLeF
            exact (hfxmin y hYInS2).left.choose_spec.left
            exact hYInS2
            rfl

theorem miny_minx_iff_minxy
    [LinearOrder R]
    {D2 : Type*}
    {S2 : Set D2}
    {f : D → D2 → R}
    {fmin : R}
    {fymin : D → R}
    {hfymin : ∀ x ∈ S, MinimumOn (fun y => f x y) S2 (fymin x)}
    : MinimumOn fymin S fmin ↔ MinimumOn (fun xy : D × D2 => f xy.1 xy.2) (S ×ˢ S2) fmin
    := by
    simp [MinimumOn, IsLeast, lowerBounds] at hfymin
    constructor
    case mp =>
        simp [MinimumOn, IsLeast, lowerBounds]
        intro xopt hXoptInS hFyminXoptEqFmin hFminLeFymin
        have yopt := (hfymin xopt hXoptInS).left.choose
        constructor
        case left =>
            exists xopt, (hfymin xopt hXoptInS).left.choose
            constructor
            case left => exact ⟨hXoptInS, (hfymin xopt hXoptInS).left.choose_spec.left⟩
            case right =>
                rw [(hfymin xopt hXoptInS).left.choose_spec.right]
                apply hFyminXoptEqFmin
        case right =>
            intro z x y hXInS hYInS2 fxyEqZ
            rw [← fxyEqZ]
            apply le_trans
            apply hFminLeFymin x hXInS
            exact (hfymin x hXInS).right y hYInS2
    case mpr =>
        simp [MinimumOn, IsLeast, lowerBounds]
        intro xopt yopt hXoptInS hYoptInS2 hFXYoptEqFmin hFminLeF
        constructor
        case left =>
            exists xopt
            constructor
            case left => exact hXoptInS
            case right =>

            rw [← hFXYoptEqFmin]
            rw [← hFXYoptEqFmin] at hFminLeF
            rw [eq_iff_le_not_lt]
            constructor
            case left => exact (hfymin xopt hXoptInS).right yopt hYoptInS2
            case right =>

            rw [not_lt]
            apply hFminLeF
            exact hXoptInS
            exact (hfymin xopt hXoptInS).left.choose_spec.left
            exact (hfymin xopt hXoptInS).left.choose_spec.right
        case right =>
            intro x hXInS
            rw [← (hfymin x hXInS).left.choose_spec.right]
            apply hFminLeF
            exact hXInS
            exact (hfymin x hXInS).left.choose_spec.left
            rfl

theorem min_comm'
    [LinearOrder R]
    {D2 : Type*}
    {S2 : Set D2}
    {f : D → D2 → R}
    {fxmin : D2 → R}
    {hfxmin : ∀ y ∈ S2, MinimumOn (fun x => f x y) S (fxmin y)}
    {fymin : D → R}
    {hfymin : ∀ x ∈ S, MinimumOn (fun y => f x y) S2 (fymin x)}
    {fmin : R}
    : MinimumOn fxmin S2 fmin ↔ MinimumOn fymin S fmin
    := by
    constructor
    case mp =>
        rw [minx_miny_iff_minxy, ← miny_minx_iff_minxy]
        intro h
        exact h
        exact f
        exact hfymin
        exact hfxmin
    case mpr =>
        rw [miny_minx_iff_minxy, ← minx_miny_iff_minxy]
        intro h
        exact h
        exact f
        exact hfxmin
        exact hfymin

theorem saddle_point_inequality
    [LE R]
    {D2 : Type*}
    {S2 : Set D2}
    {f : D → D2 → R}
    {fxmax : D2 → R}
    {hfxmax : MaximumOn f S fxmax}
    {fymin : D → R}
    {hfymin : MinimumOn (fun y => fun x => f x y) S2 fymin}
    (fminmax : R)
    (hfminmax : MinimumOn fxmax S2 fminmax)
    (fmaxmin : R)
    (hfmaxmin : MaximumOn fxmin S fmaxmin)
    : fmaxmin ≤ fminmax
    := by
    sorry

end meta_rules
