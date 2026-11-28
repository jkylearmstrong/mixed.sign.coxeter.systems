/-
Copyright (c) 2026 Johnathon Kyle Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MixedSignCoxeter.ReflectionSystem

/-!
# Disconnected Components (Section 2.5) and Tree Principal Elements (Section 2.6)

Formalization of Proposition 2.45 and Theorem 2.58 of:
Johnathon Kyle Armstrong, *Principal Elements of Mixed-Sign Coxeter Systems* (FSU, 2012).

## Main results
* `wordProd_split_components` (Proposition 2.45): If `Γ` decomposes into two disconnected
  components `N₁` and `N₂`, then every word `w ∈ W(Γ)` factors as `(word in S₁) * (word in S₂)`.
* `component_fixes_other` (Proposition 2.45): `W(Γ₁)` pointwise fixes `V₂` (i.e. acts as
  the identity on basis vectors `e_j` with `j ∈ N₂`).
* `leaf_insert_conj` (Theorem 2.58): If node `t` is a leaf (connected to at most one node `i`),
  inserting `s_t` anywhere in a word `w₀` yields an element conjugate to `w₀ * s_t`.
-/

open Matrix BigOperators

namespace ReflectionSystem

variable {n : ℕ}

section Components

/-- If `part : Fin n → Bool` separates `Γ` into two disconnected components
(`part i ≠ part j → B i j = 0`), then generators in different components commute. -/
lemma comm_of_diff_component (S : ReflectionSystem n) (part : Fin n → Bool)
    (hsep : ∀ i j : Fin n, part i ≠ part j → S.B i j = 0)
    {i j : Fin n} (hij : part i ≠ part j) :
    reflectionMatrix S.B i * reflectionMatrix S.B j =
      reflectionMatrix S.B j * reflectionMatrix S.B i :=
  reflectionMatrix_comm_of_orthogonal S (hsep i j hij)

lemma comm_wordProd_of_diff_component (S : ReflectionSystem n) (part : Fin n → Bool)
    (hsep : ∀ i j : Fin n, part i ≠ part j → S.B i j = 0)
    {a : Fin n} (ha : part a = false) (w : List (Fin n)) (hw : ∀ b ∈ w, part b = true) :
    reflectionMatrix S.B a * wordProd S w = wordProd S w * reflectionMatrix S.B a := by
  induction w with
  | nil => simp [wordProd]
  | cons b t ih =>
    simp only [wordProd, List.map_cons, List.prod_cons]
    have hb : part b = true := hw b (List.mem_cons_self)
    have ht : ∀ x ∈ t, part x = true := fun x hx => hw x (List.mem_cons_of_mem b hx)
    have hcomm : reflectionMatrix S.B a * reflectionMatrix S.B b =
        reflectionMatrix S.B b * reflectionMatrix S.B a := by
      apply comm_of_diff_component S part hsep
      rw [ha, hb]
      decide
    have ih' := ih ht
    simp only [wordProd] at ih'
    rw [← Matrix.mul_assoc, hcomm, Matrix.mul_assoc, ih', ← Matrix.mul_assoc]

/-- **Proposition 2.45 (word decomposition)**: Any word `w` in `S` factors as
`(letters in S₁) * (letters in S₂)`. -/
theorem wordProd_split_components (S : ReflectionSystem n) (part : Fin n → Bool)
    (hsep : ∀ i j : Fin n, part i ≠ part j → S.B i j = 0) (w : List (Fin n)) :
    wordProd S w =
      wordProd S (w.filter fun i => part i) * wordProd S (w.filter fun i => !part i) := by
  induction w with
  | nil => simp [wordProd]
  | cons a t ih =>
    simp only [wordProd] at ih
    cases ha : part a
    · -- part a = false, so a goes to the second component
      simp only [wordProd, List.map_cons, List.prod_cons, List.filter_cons, ha,
        Bool.false_eq_true, ↓reduceIte, Bool.not_false]
      rw [ih]
      have hcomm := comm_wordProd_of_diff_component S part hsep ha (t.filter fun i => part i)
        (fun b hb => (List.mem_filter.mp hb).2)
      simp only [wordProd] at hcomm
      rw [← Matrix.mul_assoc, hcomm, Matrix.mul_assoc]
    · -- part a = true, so a goes to the first component
      simp only [wordProd, List.map_cons, List.prod_cons, List.filter_cons, ha, ↓reduceIte,
        Bool.not_true, Bool.false_eq_true]
      rw [ih, ← Matrix.mul_assoc]

/-- **Proposition 2.45 (pointwise action)**: `W(Γ₁)` fixes `e_j` for every `j ∈ N₂`. -/
theorem component_fixes_other (S : ReflectionSystem n) (part : Fin n → Bool)
    (hsep : ∀ i j : Fin n, part i ≠ part j → S.B i j = 0)
    (w : List (Fin n)) (hw : ∀ a ∈ w, part a = true)
    {j : Fin n} (hj : part j = false) (r : Fin n) :
    wordProd S w r j = if r = j then 1 else 0 := by
  induction w generalizing r with
  | nil => simp [wordProd, Matrix.one_apply]
  | cons a t ih =>
    have ha : part a = true := hw a List.mem_cons_self
    have ht : ∀ x ∈ t, part x = true := fun x hx => hw x (List.mem_cons_of_mem a hx)
    simp only [wordProd, List.map_cons, List.prod_cons, Matrix.mul_apply]
    have hcol : ∀ k : Fin n, (List.map (reflectionMatrix S.B) t).prod k j = if k = j then 1 else 0 :=
      fun k => ih ht k
    simp_rw [hcol]
    have hterm : ∀ k : Fin n,
        reflectionMatrix S.B a r k * (if k = j then (1 : ℝ) else 0) =
        if k = j then reflectionMatrix S.B a r k else 0 := by
      intro k; split_ifs <;> ring
    rw [Finset.sum_congr rfl (fun k _ => hterm k)]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, reflectionMatrix_apply]
    have hne : a ≠ j := by
      intro h; rw [h, hj] at ha; exact absurd ha (by decide)
    have h0 : S.B a j = 0 := by
      apply hsep
      rw [ha, hj]
      decide
    by_cases hra : r = a
    · subst hra
      simp [hne, h0]
    · simp [hra]

end Components

section Trees

/-- **Theorem 2.58 (leaf-insertion conjugacy)**: If node `t` is a leaf connected to at most
one node `i` (`∀ j ≠ i, B t j = 0`), then inserting `s_t` anywhere in a word `u ++ v`
yields an element conjugate (by `1` or `s_t`) to `(u ++ v) * s_t`. -/
theorem leaf_insert_conj (S : ReflectionSystem n) (t i : Fin n)
    (hleaf : ∀ j : Fin n, j ≠ i → j ≠ t → S.B t j = 0)
    (u v : List (Fin n)) (hu : t ∉ u) (hv : t ∉ v) (huv : i ∉ u ∨ i ∉ v) :
    ∃ g : Matrix (Fin n) (Fin n) ℝ,
      g * g = 1 ∧
      g * wordProd S (u ++ [t] ++ v) * g = wordProd S (u ++ v ++ [t]) := by
  have hcomm_of_not_mem : ∀ w : List (Fin n), i ∉ w → t ∉ w →
      reflectionMatrix S.B t * wordProd S w = wordProd S w * reflectionMatrix S.B t := by
    intro w hiw htw
    induction w with
    | nil => simp [wordProd]
    | cons a rest ih =>
      simp only [wordProd, List.map_cons, List.prod_cons]
      have hai : a ≠ i := fun h => hiw (h ▸ List.mem_cons_self)
      have hat : a ≠ t := fun h => htw (h ▸ List.mem_cons_self)
      have hcomm : reflectionMatrix S.B t * reflectionMatrix S.B a =
          reflectionMatrix S.B a * reflectionMatrix S.B t :=
        reflectionMatrix_comm_of_orthogonal S (hleaf a hai hat)
      have ih' := ih (fun h => hiw (List.mem_cons_of_mem a h))
        (fun h => htw (List.mem_cons_of_mem a h))
      simp only [wordProd] at ih'
      rw [← Matrix.mul_assoc, hcomm, Matrix.mul_assoc, ih', ← Matrix.mul_assoc]
  rcases huv with hiu | hiv
  · -- Case 1: `i ∉ u`, so `s_t` commutes past `u` to the front, then conjugate by `s_t`!
    refine ⟨reflectionMatrix S.B t, reflectionMatrix_mul_self S t, ?_⟩
    have hcomm_u := hcomm_of_not_mem u hiu hu
    have hst : reflectionMatrix S.B t * reflectionMatrix S.B t = 1 :=
      reflectionMatrix_mul_self S t
    simp only [wordProd, List.append_assoc, List.map_append, List.prod_append,
      List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Matrix.mul_one] at hcomm_u ⊢
    rw [← Matrix.mul_assoc (reflectionMatrix S.B t) (List.map (reflectionMatrix S.B) u).prod, hcomm_u]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (reflectionMatrix S.B t) (reflectionMatrix S.B t), hst, Matrix.one_mul]
  · -- Case 2: `i ∉ v`, so `s_t` commutes past `v` to the end (`g = 1`).
    refine ⟨1, Matrix.one_mul 1, ?_⟩
    have hcomm_v := hcomm_of_not_mem v hiv hv
    simp only [Matrix.one_mul, Matrix.mul_one]
    simp only [wordProd, List.append_assoc, List.map_append, List.prod_append,
      List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Matrix.mul_one] at hcomm_v ⊢
    rw [hcomm_v]

end Trees

/-! ### Corollary 2.46: `k` Disconnected Components and Direct Product Isomorphism -/

section KComponents

/-- The reflection subgroup `W(Γ_c)` generated by reflections in component `c : Fin k`. -/
noncomputable def W_component {k : ℕ} (S : ReflectionSystem n) (comp : Fin n → Fin k)
    (c : Fin k) : Submonoid (Matrix (Fin n) (Fin n) ℝ) :=
  Submonoid.closure { M | ∃ i : Fin n, comp i = c ∧ M = reflectionMatrix S.B i }

lemma W_component_le_W_group {k : ℕ} (S : ReflectionSystem n) (comp : Fin n → Fin k) (c : Fin k) :
    W_component S comp c ≤ W_group S := by
  rw [W_component, Submonoid.closure_le]
  rintro M ⟨i, _, rfl⟩
  exact Submonoid.subset_closure ⟨i, rfl⟩

lemma wordProd_mem_W_component {k : ℕ} (S : ReflectionSystem n) (comp : Fin n → Fin k)
    (c : Fin k) (w : List (Fin n)) (hw : ∀ a ∈ w, comp a = c) :
    wordProd S w ∈ W_component S comp c := by
  induction w with
  | nil => simp [wordProd]
  | cons a t ih =>
    simp only [wordProd, List.map_cons, List.prod_cons]
    exact (W_component S comp c).mul_mem
      (Submonoid.subset_closure ⟨a, hw a List.mem_cons_self, rfl⟩)
      (ih fun b hb => hw b (List.mem_cons_of_mem a hb))

lemma comm_W_component {k : ℕ} (S : ReflectionSystem n) (comp : Fin n → Fin k)
    (hsep : ∀ i j : Fin n, comp i ≠ comp j → S.B i j = 0)
    {c₁ c₂ : Fin k} (hc : c₁ ≠ c₂)
    {x y : Matrix (Fin n) (Fin n) ℝ}
    (hx : x ∈ W_component S comp c₁) (hy : y ∈ W_component S comp c₂) :
    x * y = y * x := by
  induction hx using Submonoid.closure_induction with
  | mem M hM =>
    rcases hM with ⟨i, hi, rfl⟩
    induction hy using Submonoid.closure_induction with
    | mem N hN =>
      rcases hN with ⟨j, hj, rfl⟩
      exact reflectionMatrix_comm_of_orthogonal S (hsep i j (by rw [hi, hj]; exact hc))
    | one => simp
    | mul N₁ N₂ _ _ ih₁ ih₂ =>
      rw [← Matrix.mul_assoc, ih₁, Matrix.mul_assoc, ih₂, ← Matrix.mul_assoc]
  | one => simp
  | mul M₁ M₂ _ _ ih₁ ih₂ =>
    rw [Matrix.mul_assoc, ih₂, ← Matrix.mul_assoc, ih₁, Matrix.mul_assoc]

private lemma comm_reflectionMatrix_wordProd_filter {k : ℕ} (S : ReflectionSystem n)
    (comp : Fin n → Fin k) (hsep : ∀ i j : Fin n, comp i ≠ comp j → S.B i j = 0)
    (a : Fin n) (c : Fin k) (hca : comp a ≠ c) (t : List (Fin n)) :
    reflectionMatrix S.B a * wordProd S (t.filter fun i => comp i == c) =
      wordProd S (t.filter fun i => comp i == c) * reflectionMatrix S.B a := by
  exact comm_W_component S comp hsep hca
    (Submonoid.subset_closure ⟨a, rfl, rfl⟩)
    (wordProd_mem_W_component S comp c _ fun b hb => beq_iff_eq.mp (List.mem_filter.mp hb).2)

private lemma wordProd_split_list {k : ℕ} (S : ReflectionSystem n) (comp : Fin n → Fin k)
    (hsep : ∀ i j : Fin n, comp i ≠ comp j → S.B i j = 0)
    (a : Fin n) (t : List (Fin n)) (L : List (Fin k))
    (hL : L.Nodup) (ha : comp a ∈ L) :
    reflectionMatrix S.B a *
        (L.map fun c => wordProd S (t.filter fun i => comp i == c)).prod =
      (L.map fun c => wordProd S ((a :: t).filter fun i => comp i == c)).prod := by
  induction L with
  | nil => simp at ha
  | cons c rest ih =>
    simp only [List.nodup_cons] at hL
    simp only [List.mem_cons] at ha
    simp only [List.map_cons, List.prod_cons]
    by_cases hca : comp a = c
    · subst hca
      have hmap : rest.map (fun c' => wordProd S ((a :: t).filter fun i => comp i == c')) =
          rest.map (fun c' => wordProd S (t.filter fun i => comp i == c')) := by
        refine List.map_congr_left fun c' hc' => ?_
        have hne : comp a ≠ c' := fun h => hL.1 (h ▸ hc')
        simp [hne]
      rw [hmap]
      simp [wordProd, Matrix.mul_assoc]
    · have ha' : comp a ∈ rest := ha.resolve_left hca
      have hcomm := comm_reflectionMatrix_wordProd_filter S comp hsep a c hca t
      have hfilt : (a :: t).filter (fun i => comp i == c) = t.filter (fun i => comp i == c) := by
        simp [hca]
      rw [hfilt, ← Matrix.mul_assoc, hcomm, Matrix.mul_assoc, ih hL.2 ha']

/-- **Corollary 2.46 (word factorization)**: If `Γ` decomposes into `k` disconnected components
`comp : Fin n → Fin k`, then every word `w` factors as the product of its `k` component
subwords. -/
theorem wordProd_split_k_components {k : ℕ} (S : ReflectionSystem n) (comp : Fin n → Fin k)
    (hsep : ∀ i j : Fin n, comp i ≠ comp j → S.B i j = 0) (w : List (Fin n)) :
    wordProd S w =
      ((List.finRange k).map fun c => wordProd S (w.filter fun i => comp i == c)).prod := by
  induction w with
  | nil =>
    have h1 : ∀ c ∈ List.finRange k, wordProd S (([] : List (Fin n)).filter fun i => comp i == c) = 1 :=
      fun _ _ => by simp [wordProd]
    rw [List.prod_eq_one (by intro M hM; rcases List.mem_map.mp hM with ⟨c, hc, rfl⟩; exact h1 c hc)]
    simp [wordProd]
  | cons a t ih =>
    simp only [wordProd, List.map_cons, List.prod_cons] at ih ⊢
    rw [ih]
    exact wordProd_split_list S comp hsep a t (List.finRange k) (List.nodup_finRange k)
      (List.mem_finRange (comp a))

/-- Each component subgroup `W(Γ_c)` pointwise fixes every basis vector `e_j` with `comp j ≠ c`. -/
theorem k_component_fixes_other {k : ℕ} (S : ReflectionSystem n) (comp : Fin n → Fin k)
    (hsep : ∀ i j : Fin n, comp i ≠ comp j → S.B i j = 0)
    (c : Fin k) {x : Matrix (Fin n) (Fin n) ℝ} (hx : x ∈ W_component S comp c)
    {j : Fin n} (hj : comp j ≠ c) :
    x *ᵥ Pi.single j (1 : ℝ) = Pi.single j (1 : ℝ) := by
  induction hx using Submonoid.closure_induction with
  | mem M hM =>
    rcases hM with ⟨i, hi, rfl⟩
    ext r
    simp only [Matrix.mulVec, dotProduct, Pi.single_apply]
    have hterm : ∀ m : Fin n,
        reflectionMatrix S.B i r m * (if m = j then (1 : ℝ) else 0) =
          if m = j then reflectionMatrix S.B i r m else 0 := by
      intro m; split_ifs <;> ring
    rw [Finset.sum_congr rfl fun m _ => hterm m]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    have h0 : S.B i j = 0 := hsep i j (by rw [hi]; exact hj.symm)
    rw [reflectionMatrix_apply]
    by_cases hri : r = i
    · subst hri
      have hne : r ≠ j := fun h => hj (h ▸ hi)
      simp [hne, h0]
    · simp [hri]
  | one => exact Matrix.one_mulVec _
  | mul M₁ M₂ _ _ ih₁ ih₂ =>
    rw [← Matrix.mulVec_mulVec, ih₂, ih₁]

private lemma list_prod_mul_list_prod {k : ℕ} (S : ReflectionSystem n) (comp : Fin n → Fin k)
    (hsep : ∀ i j : Fin n, comp i ≠ comp j → S.B i j = 0)
    (L : List (Fin k)) (hL : L.Nodup)
    (f g : ∀ c : Fin k, W_component S comp c) :
    (L.map fun c => (f c).1).prod * (L.map fun c => (g c).1).prod =
      (L.map fun c => (f c).1 * (g c).1).prod := by
  induction L with
  | nil => simp
  | cons c rest ih =>
    simp only [List.nodup_cons] at hL
    simp only [List.map_cons, List.prod_cons]
    have hcomm : (rest.map fun c' => (f c').1).prod * (g c).1 =
        (g c).1 * (rest.map fun c' => (f c').1).prod := by
      have haux : ∀ (R : List (Fin k)), (∀ c' ∈ R, c' ≠ c) →
          (R.map fun c' => (f c').1).prod * (g c).1 =
            (g c).1 * (R.map fun c' => (f c').1).prod := by
        intro R hR
        induction R with
        | nil => simp
        | cons d ds ihR =>
          simp only [List.map_cons, List.prod_cons]
          have hd : d ≠ c := hR d List.mem_cons_self
          have hds : ∀ c' ∈ ds, c' ≠ c := fun c' hc' => hR c' (List.mem_cons_of_mem d hc')
          rw [Matrix.mul_assoc, ihR hds, ← Matrix.mul_assoc,
            comm_W_component S comp hsep hd (f d).2 (g c).2, Matrix.mul_assoc]
      exact haux rest fun c' hc' h => hL.1 (h ▸ hc')
    calc
      (f c).1 * (rest.map fun c' => (f c').1).prod *
          ((g c).1 * (rest.map fun c' => (g c').1).prod)
        = (f c).1 * (((rest.map fun c' => (f c').1).prod * (g c).1) *
            (rest.map fun c' => (g c').1).prod) := by simp [Matrix.mul_assoc]
      _ = (f c).1 * ((g c).1 * ((rest.map fun c' => (f c').1).prod *
            (rest.map fun c' => (g c').1).prod)) := by rw [hcomm]; simp [Matrix.mul_assoc]
      _ = ((f c).1 * (g c).1) * (rest.map fun c' => (f c').1 * (g c').1).prod := by
          rw [ih hL.2, Matrix.mul_assoc]

private lemma list_prod_mulVec_single {k : ℕ} (S : ReflectionSystem n) (comp : Fin n → Fin k)
    (hsep : ∀ i j : Fin n, comp i ≠ comp j → S.B i j = 0)
    (L : List (Fin k)) (hL : L.Nodup)
    (f : ∀ c : Fin k, W_component S comp c) (j : Fin n) (hj : comp j ∈ L) :
    (L.map fun c => (f c).1).prod *ᵥ Pi.single j (1 : ℝ) =
      (f (comp j)).1 *ᵥ Pi.single j (1 : ℝ) := by
  induction L with
  | nil => simp at hj
  | cons c rest ih =>
    simp only [List.nodup_cons] at hL
    simp only [List.mem_cons] at hj
    simp only [List.map_cons, List.prod_cons]
    rw [← Matrix.mulVec_mulVec]
    by_cases hc : comp j = c
    · subst hc
      have hfix : (rest.map fun c' => (f c').1).prod *ᵥ Pi.single j (1 : ℝ) =
          Pi.single j (1 : ℝ) := by
        have haux : ∀ (R : List (Fin k)), (∀ c' ∈ R, comp j ≠ c') →
            (R.map fun c' => (f c').1).prod *ᵥ Pi.single j (1 : ℝ) = Pi.single j (1 : ℝ) := by
          intro R hR
          induction R with
          | nil => exact Matrix.one_mulVec _
          | cons d ds ihR =>
            simp only [List.map_cons, List.prod_cons]
            rw [← Matrix.mulVec_mulVec, ihR fun c' hc' => hR c' (List.mem_cons_of_mem d hc')]
            exact k_component_fixes_other S comp hsep d (f d).2 (hR d List.mem_cons_self)
        exact haux rest fun c' hc' h => hL.1 (h ▸ hc')
      rw [hfix]
    · rw [ih hL.2 (hj.resolve_left hc)]
      have hcomm : (f c).1 * (f (comp j)).1 = (f (comp j)).1 * (f c).1 :=
        comm_W_component S comp hsep (Ne.symm hc) (f c).2 (f (comp j)).2
      rw [Matrix.mulVec_mulVec, hcomm, ← Matrix.mulVec_mulVec,
        k_component_fixes_other S comp hsep c (f c).2 hc]

private lemma W_group_eq_wordProd (S : ReflectionSystem n) {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : M ∈ W_group S) :
    ∃ w : List (Fin n), M = wordProd S w := by
  induction hM using Submonoid.closure_induction with
  | mem x hx =>
    rcases hx with ⟨i, rfl⟩
    exact ⟨[i], by simp [wordProd]⟩
  | one => exact ⟨[], by simp [wordProd]⟩
  | mul x y _ _ ihx ihy =>
    rcases ihx with ⟨wx, rfl⟩
    rcases ihy with ⟨wy, rfl⟩
    exact ⟨wx ++ wy, (wordProd_append' S wx wy).symm⟩

/-- **Corollary 2.46**: If `Γ` decomposes into `k` disconnected components `Γ_1, ..., Γ_k`,
then `W(Γ) ≃* ∀ c : Fin k, W(Γ_c)`. -/
noncomputable def k_component_mulEquiv {k : ℕ} (S : ReflectionSystem n) (comp : Fin n → Fin k)
    (hsep : ∀ i j : Fin n, comp i ≠ comp j → S.B i j = 0) :
    W_group S ≃* ∀ c : Fin k, W_component S comp c := by
  let φ : (∀ c : Fin k, W_component S comp c) →* W_group S :=
    { toFun := fun f =>
        ⟨((List.finRange k).map fun c => (f c).1).prod, by
          apply Submonoid.list_prod_mem
          intro M hM
          rcases List.mem_map.mp hM with ⟨c, _, rfl⟩
          exact W_component_le_W_group S comp c (f c).2⟩
      map_one' := by
        ext1
        show ((List.finRange k).map fun _ => (1 : Matrix (Fin n) (Fin n) ℝ)).prod = 1
        exact List.prod_eq_one fun M hM => by
          rcases List.mem_map.mp hM with ⟨_, _, rfl⟩; rfl
      map_mul' := fun f g => by
        ext1
        show ((List.finRange k).map fun c => (f c).1 * (g c).1).prod =
          ((List.finRange k).map fun c => (f c).1).prod *
            ((List.finRange k).map fun c => (g c).1).prod
        exact (list_prod_mul_list_prod S comp hsep (List.finRange k) (List.nodup_finRange k) f g).symm }
  have hbij : Function.Bijective φ := by
    constructor
    · intro f g hfg
      have hmat : ((List.finRange k).map fun c => (f c).1).prod =
          ((List.finRange k).map fun c => (g c).1).prod := congr_arg Subtype.val hfg
      funext c
      ext r j
      by_cases hj : comp j = c
      · have h1 := congr_arg (fun M => M *ᵥ Pi.single j (1 : ℝ)) hmat
        rw [list_prod_mulVec_single S comp hsep (List.finRange k) (List.nodup_finRange k) f j
              (List.mem_finRange _),
            list_prod_mulVec_single S comp hsep (List.finRange k) (List.nodup_finRange k) g j
              (List.mem_finRange _),
            hj] at h1
        have h2 := congr_fun h1 r
        simpa [Matrix.mulVec, dotProduct, Pi.single_apply, Finset.sum_ite_eq'] using h2
      · have hf := k_component_fixes_other S comp hsep c (f c).2 hj
        have hg := k_component_fixes_other S comp hsep c (g c).2 hj
        have h2 := congr_fun (hf.trans hg.symm) r
        simpa [Matrix.mulVec, dotProduct, Pi.single_apply, Finset.sum_ite_eq'] using h2
    · intro x
      rcases W_group_eq_wordProd S x.2 with ⟨w, hw⟩
      refine ⟨fun c => ⟨wordProd S (w.filter fun i => comp i == c),
        wordProd_mem_W_component S comp c _ fun b hb =>
          beq_iff_eq.mp (List.mem_filter.mp hb).2⟩, ?_⟩
      ext1
      show ((List.finRange k).map fun c => wordProd S (w.filter fun i => comp i == c)).prod = x.1
      rw [hw, wordProd_split_k_components S comp hsep w]
  exact (MulEquiv.ofBijective φ hbij).symm

end KComponents

end ReflectionSystem
