/-
Copyright (c) 2026 Johnathon Kyle Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MixedSignCoxeter.Basic
import MixedSignCoxeter.FiniteReduction
import MixedSignCoxeter.ParabolicTransfer
import MixedSignCoxeter.SpectralClassification

/-!
# Chapter 2 Foundations: Roots, k-Components, Signature, Node Deletion, and Spectral Radius

Formalizes the six remaining Chapter 2 definitions and corollaries from:
Johnathon Kyle Armstrong, *Principal Elements of Mixed-Sign Coxeter Systems* (FSU, 2012):

* **Definition 2.12** (`roots`, `positiveRoots`): The root system `Φ = W Π_+ = {w e_i | w ∈ W}`,
  with basic properties (`simple_mem_roots`, `roots_mulVec_mem`, `roots_neg_mem`,
  `roots_ne_zero`, `roots_quadForm_eq`).
* **Corollary 2.46** (`wordProd_split_k_components`, `k_component_mulEquiv`): If a reflection
  diagram decomposes into `k` disconnected components `Γ_1, ..., Γ_k`, then every word factors
  into commuting component words and `W(Γ) ≃* ∀ c : Fin k, W(Γ_c)`.
* **Definition 2.47** (`signature`, `posEigenCount`, `negEigenCount`, `zeroEigenCount`):
  The eigenvalue signature triple `sig(B) = (p, q, l)` with `p + q + l = n` (`signature_sum`)
  and equivalence with definiteness (`isPosDef_iff_signature`, `isNegDef_iff_signature`).
* **Definition 2.51** (`SignatureType`, `signatureType`): Full four-way classification into
  `spherical`, `affine`, `hyperbolic`, and `higherRank`, explicitly separating hyperbolic from
  higher-rank indefinite systems (`signatureType_eq_hyperbolic_iff`,
  `signatureType_eq_higherRank_of_two_pos_two_neg`).
* **Definition 2.56** (`deleteNode`): Node deletion `Γ / (r_i)` via `Matrix.submatrix` with
  `Fin.succAbove i`, together with subdiagram relation transfer (`deleteNode_wordProd_sub_of_map`,
  `deleteNode_wordProd_eq_iff`).
* **Definition 2.61** (`spectralRadius`): The spectral radius `λ(M) = sup {‖μ‖ | HasEigenC M μ}`,
  with boundedness, nonnegativity, upper-bound, and lower-bound lemmas.
-/

open Matrix BigOperators

namespace ReflectionSystem

variable {n : ℕ}

/-! ### Definition 2.12: Root System `Φ = W Π_+` -/

section Roots

/-- **Definition 2.12**: The set of roots `Φ := W Π_+ = {w e_i | w ∈ W}` of a reflection
system `(W, S, B)`. -/
def roots (S : ReflectionSystem n) : Set (Fin n → ℝ) :=
  { v | ∃ (w : List (Fin n)) (i : Fin n), v = wordProd S w *ᵥ Pi.single i (1 : ℝ) }

/-- **Definition 2.13**: The set of positive roots `Φ_+ ⊆ Φ` (nonzero roots with all
coordinates nonnegative). -/
def positiveRoots (S : ReflectionSystem n) : Set (Fin n → ℝ) :=
  { v ∈ S.roots | (∀ j : Fin n, 0 ≤ v j) ∧ v ≠ 0 }

lemma wordProd_append' (S : ReflectionSystem n) (u w : List (Fin n)) :
    wordProd S (u ++ w) = wordProd S u * wordProd S w := by
  simp [wordProd, List.map_append, List.prod_append]

lemma wordProd_reverse_mul' (S : ReflectionSystem n) (w : List (Fin n)) :
    wordProd S w.reverse * wordProd S w = 1 := by
  induction w with
  | nil => simp [wordProd]
  | cons a t ih =>
    simp only [List.reverse_cons, wordProd_append']
    simp only [wordProd, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      Matrix.mul_one] at ih ⊢
    calc
      (List.map (reflectionMatrix S.B) t.reverse).prod * reflectionMatrix S.B a *
          (reflectionMatrix S.B a * (List.map (reflectionMatrix S.B) t).prod)
        = (List.map (reflectionMatrix S.B) t.reverse).prod *
            (reflectionMatrix S.B a * reflectionMatrix S.B a) *
            (List.map (reflectionMatrix S.B) t).prod := by simp [Matrix.mul_assoc]
      _ = (List.map (reflectionMatrix S.B) t.reverse).prod *
            (List.map (reflectionMatrix S.B) t).prod := by
          rw [reflectionMatrix_mul_self S a, Matrix.mul_one]
      _ = 1 := ih

lemma wordProd_mem_W_group (S : ReflectionSystem n) (w : List (Fin n)) :
    wordProd S w ∈ W_group S := by
  induction w with
  | nil => simp [wordProd]
  | cons a t ih =>
    simp only [wordProd, List.map_cons, List.prod_cons]
    exact (W_group S).mul_mem (Submonoid.subset_closure ⟨a, rfl⟩) ih

lemma reflectionMatrix_mulVec_single_self (S : ReflectionSystem n) (i : Fin n) :
    reflectionMatrix S.B i *ᵥ Pi.single i (1 : ℝ) = -Pi.single i (1 : ℝ) := by
  ext r
  simp only [Matrix.mulVec, dotProduct, Pi.neg_apply, Pi.single_apply]
  have hterm : ∀ j : Fin n,
      reflectionMatrix S.B i r j * (if j = i then (1 : ℝ) else 0) =
        if j = i then reflectionMatrix S.B i r j else 0 := by
    intro j; split_ifs <;> ring
  rw [Finset.sum_congr rfl fun j _ => hterm j]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  by_cases hri : r = i
  · subst hri
    rw [reflectionMatrix_apply_self S.B (S.B_diag_ne_zero r)]
    simp
  · rw [reflectionMatrix_apply]
    simp [hri]

/-- Every simple basis vector `e_i` is a root. -/
theorem simple_mem_roots (S : ReflectionSystem n) (i : Fin n) :
    Pi.single i (1 : ℝ) ∈ S.roots :=
  ⟨[], i, by rw [show wordProd S [] = 1 from by simp [wordProd], Matrix.one_mulVec]⟩

/-- Every simple basis vector `e_i` is a positive root. -/
theorem simple_mem_positiveRoots (S : ReflectionSystem n) (i : Fin n) :
    Pi.single i (1 : ℝ) ∈ S.positiveRoots := by
  refine ⟨simple_mem_roots S i, fun j => ?_, fun h0 => ?_⟩
  · by_cases h : j = i <;> simp [h]
  · have := congr_fun h0 i
    simp at this

/-- The root system `Φ` is `W`-invariant. -/
theorem roots_mulVec_mem (S : ReflectionSystem n) {v : Fin n → ℝ} (hv : v ∈ S.roots)
    (u : List (Fin n)) :
    wordProd S u *ᵥ v ∈ S.roots := by
  rcases hv with ⟨w, i, rfl⟩
  exact ⟨u ++ w, i, by rw [wordProd_append', Matrix.mulVec_mulVec]⟩

/-- The root system `Φ` is closed under negation: `v ∈ Φ → -v ∈ Φ`. -/
theorem roots_neg_mem (S : ReflectionSystem n) {v : Fin n → ℝ} (hv : v ∈ S.roots) :
    -v ∈ S.roots := by
  rcases hv with ⟨w, i, rfl⟩
  refine ⟨w ++ [i], i, ?_⟩
  rw [wordProd_append', ← Matrix.mulVec_mulVec]
  have hsi : wordProd S [i] = reflectionMatrix S.B i := by simp [wordProd]
  rw [hsi, reflectionMatrix_mulVec_single_self, Matrix.mulVec_neg]

/-- Every root is nonzero. -/
theorem roots_ne_zero (S : ReflectionSystem n) {v : Fin n → ℝ} (hv : v ∈ S.roots) :
    v ≠ 0 := by
  rcases hv with ⟨w, i, rfl⟩
  intro h0
  have h1 : wordProd S w.reverse *ᵥ (wordProd S w *ᵥ Pi.single i (1 : ℝ)) = 0 := by
    rw [h0, Matrix.mulVec_zero]
  rw [Matrix.mulVec_mulVec, wordProd_reverse_mul', Matrix.one_mulVec] at h1
  have h2 := congr_fun h1 i
  simp at h2

lemma quadForm_eq_dotProduct (B : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    quadForm B v = dotProduct v (B *ᵥ v) := by
  simp only [quadForm, dotProduct, Matrix.mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

lemma quadForm_mulVec (B M : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    quadForm B (M *ᵥ v) = quadForm (Mᵀ * B * M) v := by
  rw [quadForm_eq_dotProduct, quadForm_eq_dotProduct]
  calc
    (M *ᵥ v) ⬝ᵥ (B *ᵥ (M *ᵥ v))
      = (v ᵥ* Mᵀ) ⬝ᵥ (B *ᵥ (M *ᵥ v)) := by rw [Matrix.vecMul_transpose]
    _ = v ⬝ᵥ (Mᵀ *ᵥ (B *ᵥ (M *ᵥ v))) := (Matrix.dotProduct_mulVec v Mᵀ _).symm
    _ = v ⬝ᵥ ((Mᵀ * B * M) *ᵥ v) := by
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]

/-- Every root `v = w e_i ∈ Φ` has the same quadratic-form value as `e_i`: `Q(w e_i) = B(e_i, e_i)`. -/
theorem roots_quadForm_eq (S : ReflectionSystem n) {v : Fin n → ℝ} (hv : v ∈ S.roots) :
    ∃ i : Fin n, quadForm S.B v = S.B i i := by
  rcases hv with ⟨w, i, rfl⟩
  refine ⟨i, ?_⟩
  rw [quadForm_mulVec, W_group_preserves_B S (wordProd_mem_W_group S w)]
  rw [quadForm_eq_dotProduct]
  simp only [dotProduct, Matrix.mulVec, Pi.single_apply]
  have h1 : ∀ r : Fin n, (if r = i then (1 : ℝ) else 0) *
      ∑ j : Fin n, S.B r j * (if j = i then (1 : ℝ) else 0) =
      if r = i then S.B r i else 0 := by
    intro r
    split_ifs with hr
    · subst hr
      simp [Finset.sum_ite_eq']
    · simp
  rw [Finset.sum_congr rfl fun r _ => h1 r]
  simp

end Roots

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

/-! ### Definitions 2.47 & 2.51: Eigenvalue Signature Triple and 4-Way Classification -/

section Signature

/-- Every `ReflectionSystem` has a real Hermitian (symmetric) bilinear form matrix `S.B`. -/
lemma B_isHermitian (S : ReflectionSystem n) : S.B.IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, S.B_symm]

/-- Number of strictly positive eigenvalues of `S.B` (counted with multiplicity). -/
noncomputable def posEigenCount (S : ReflectionSystem n) : ℕ :=
  (Finset.univ.filter fun i : Fin n => 0 < S.B_isHermitian.eigenvalues i).card

/-- Number of strictly negative eigenvalues of `S.B` (counted with multiplicity). -/
noncomputable def negEigenCount (S : ReflectionSystem n) : ℕ :=
  (Finset.univ.filter fun i : Fin n => S.B_isHermitian.eigenvalues i < 0).card

/-- Number of zero eigenvalues of `S.B` (nullity). -/
noncomputable def zeroEigenCount (S : ReflectionSystem n) : ℕ :=
  (Finset.univ.filter fun i : Fin n => S.B_isHermitian.eigenvalues i = 0).card

/-- **Definition 2.47**: The signature `sig(B) = (p, q, l)` of the bilinear form `B`, where
`p`, `q`, `l` are the counts of positive, negative, and zero eigenvalues of `B`. -/
noncomputable def signature (S : ReflectionSystem n) : ℕ × ℕ × ℕ :=
  (S.posEigenCount, S.negEigenCount, S.zeroEigenCount)

/-- The eigenvalue counts satisfy `p + q + l = n`. -/
theorem signature_sum (S : ReflectionSystem n) :
    S.posEigenCount + S.negEigenCount + S.zeroEigenCount = n := by
  unfold posEigenCount negEigenCount zeroEigenCount
  have hd12 : Disjoint
      (Finset.univ.filter fun i : Fin n => 0 < S.B_isHermitian.eigenvalues i)
      (Finset.univ.filter fun i : Fin n => S.B_isHermitian.eigenvalues i < 0) := by
    rw [Finset.disjoint_filter]
    intro i _ h1 h2; linarith
  have hd12_3 : Disjoint
      ((Finset.univ.filter fun i : Fin n => 0 < S.B_isHermitian.eigenvalues i) ∪
        (Finset.univ.filter fun i : Fin n => S.B_isHermitian.eigenvalues i < 0))
      (Finset.univ.filter fun i : Fin n => S.B_isHermitian.eigenvalues i = 0) := by
    rw [Finset.disjoint_left]
    intro i hi1 hi2
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hi1 hi2
    rcases hi1 with h | h <;> linarith
  rw [← Finset.card_union_of_disjoint hd12, ← Finset.card_union_of_disjoint hd12_3]
  have hunion :
      ((Finset.univ.filter fun i : Fin n => 0 < S.B_isHermitian.eigenvalues i) ∪
        (Finset.univ.filter fun i : Fin n => S.B_isHermitian.eigenvalues i < 0)) ∪
      (Finset.univ.filter fun i : Fin n => S.B_isHermitian.eigenvalues i = 0) = Finset.univ := by
    ext i
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    rcases lt_trichotomy (S.B_isHermitian.eigenvalues i) 0 with h | h | h
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
    · exact Or.inl (Or.inl h)
  rw [hunion, Finset.card_univ, Fintype.card_fin]

lemma isPosDef_iff_posDef (S : ReflectionSystem n) :
    S.IsPosDef ↔ S.B.PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  constructor
  · intro h
    refine ⟨S.B_isHermitian, fun v hv => ?_⟩
    simpa [quadForm_eq_dotProduct] using h v hv
  · intro h v hv
    simpa [quadForm_eq_dotProduct] using h.2 hv

/-- `S` is positive definite iff `sig(B) = (n, 0, 0)`. -/
theorem isPosDef_iff_signature (S : ReflectionSystem n) :
    S.IsPosDef ↔ S.signature = (n, 0, 0) := by
  rw [isPosDef_iff_posDef, S.B_isHermitian.posDef_iff_eigenvalues_pos]
  constructor
  · intro hpos
    have hp : S.posEigenCount = n := by
      unfold posEigenCount
      rw [Finset.filter_true_of_mem fun i _ => hpos i, Finset.card_univ, Fintype.card_fin]
    have hsum := S.signature_sum
    have hq : S.negEigenCount = 0 := by omega
    have hl : S.zeroEigenCount = 0 := by omega
    simp [signature, hp, hq, hl]
  · intro hsig i
    have hp : S.posEigenCount = n := congr_arg Prod.fst hsig
    unfold posEigenCount at hp
    have hall : (Finset.univ.filter fun j : Fin n => 0 < S.B_isHermitian.eigenvalues j) =
        Finset.univ := Finset.eq_univ_of_card _ (by simpa using hp)
    have hi : i ∈ Finset.univ.filter fun j : Fin n => 0 < S.B_isHermitian.eigenvalues j := by
      rw [hall]; exact Finset.mem_univ i
    exact (Finset.mem_filter.mp hi).2

/-- `S` is negative definite iff `sig(B) = (0, n, 0)`. -/
theorem isNegDef_iff_signature (S : ReflectionSystem n) :
    S.IsNegDef ↔ S.signature = (0, n, 0) := by
  have hneg : S.IsNegDef ↔ (-S.B).PosDef := by
    rw [Matrix.posDef_iff_dotProduct_mulVec]
    constructor
    · intro h
      have hH : (-S.B).IsHermitian := by
        rw [Matrix.IsHermitian, Matrix.conjTranspose_neg,
          Matrix.conjTranspose_eq_transpose_of_trivial, S.B_symm]
      refine ⟨hH, fun v hv => ?_⟩
      have h1 := h v hv
      rw [quadForm_eq_dotProduct] at h1
      simpa [Matrix.neg_mulVec, dotProduct_neg] using h1
    · intro h v hv
      have h1 := h.2 hv
      rw [quadForm_eq_dotProduct]
      simpa [Matrix.neg_mulVec, dotProduct_neg] using h1
  have hall_neg : (-S.B).PosDef ↔ ∀ i : Fin n, S.B_isHermitian.eigenvalues i < 0 := by
    rw [Matrix.posDef_iff_dotProduct_mulVec]
    constructor
    · intro hpos i
      have hv_ne : (⇑(S.B_isHermitian.eigenvectorBasis i) : Fin n → ℝ) ≠ 0 := by
        intro h0
        apply S.B_isHermitian.eigenvectorBasis.orthonormal.ne_zero i
        ext j; simpa using congr_fun h0 j
      have h1 := hpos.2 hv_ne
      have heig := S.B_isHermitian.mulVec_eigenvectorBasis i
      rw [star_trivial, Matrix.neg_mulVec, heig, dotProduct_neg, dotProduct_smul,
        smul_eq_mul] at h1
      have hnorm : 0 < dotProduct (⇑(S.B_isHermitian.eigenvectorBasis i) : Fin n → ℝ)
          (⇑(S.B_isHermitian.eigenvectorBasis i) : Fin n → ℝ) := by
        have hnn : 0 ≤ dotProduct (⇑(S.B_isHermitian.eigenvectorBasis i) : Fin n → ℝ)
            (⇑(S.B_isHermitian.eigenvectorBasis i) : Fin n → ℝ) :=
          Finset.sum_nonneg fun j _ => mul_self_nonneg _
        rcases lt_or_eq_of_le hnn with hlt | heq
        · exact hlt
        · exfalso
          apply hv_ne
          ext j
          have hj0 : (S.B_isHermitian.eigenvectorBasis i j) *
              (S.B_isHermitian.eigenvectorBasis i j) = 0 :=
            (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => mul_self_nonneg
              (S.B_isHermitian.eigenvectorBasis i k))).mp heq.symm j (Finset.mem_univ j)
          exact mul_self_eq_zero.mp hj0
      nlinarith
    · intro hall
      have hH : (-S.B).IsHermitian := by
        rw [Matrix.IsHermitian, Matrix.conjTranspose_neg,
          Matrix.conjTranspose_eq_transpose_of_trivial, S.B_symm]
      refine ⟨hH, fun v hv => ?_⟩
      let U : Matrix (Fin n) (Fin n) ℝ := S.B_isHermitian.eigenvectorUnitary.1
      have hU : S.B = U * Matrix.diagonal S.B_isHermitian.eigenvalues * star U :=
        S.B_isHermitian.spectral_theorem
      have hUU : U * star U = 1 := by
        exact Unitary.coe_mul_star_self S.B_isHermitian.eigenvectorUnitary
      have hv' : (star U) *ᵥ v ≠ 0 := by
        intro h0
        apply hv
        have hmul := congr_arg (fun w => U *ᵥ w) h0
        rw [Matrix.mulVec_mulVec, hUU, Matrix.one_mulVec, Matrix.mulVec_zero] at hmul
        exact hmul
      set y := (star U) *ᵥ v
      have hquad : dotProduct v (S.B *ᵥ v) = ∑ i : Fin n, S.B_isHermitian.eigenvalues i * (y i) ^ 2 := by
        conv_lhs => rw [hU]
        rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
          Matrix.dotProduct_mulVec]
        have hvec : v ᵥ* U = y := by
          ext j
          simp only [y, Matrix.vecMul, Matrix.mulVec, dotProduct, Matrix.star_apply,
            star_trivial]
          exact Finset.sum_congr rfl fun x _ => mul_comm _ _
        rw [hvec]
        simp only [dotProduct, Matrix.mulVec_diagonal]
        refine Finset.sum_congr rfl fun i _ => by ring
      have hneg_sum : dotProduct v (S.B *ᵥ v) < 0 := by
        rw [hquad]
        have hex : ∃ i : Fin n, y i ≠ 0 := by
          by_contra h
          push Not at h
          exact hv' (funext h)
        rcases hex with ⟨i₀, hi₀⟩
        have hle : ∀ i ∈ (Finset.univ : Finset (Fin n)),
            S.B_isHermitian.eigenvalues i * (y i) ^ 2 ≤ (0 : ℝ) := fun i _ =>
          mul_nonpos_of_nonpos_of_nonneg (le_of_lt (hall i)) (sq_nonneg _)
        have hlt : S.B_isHermitian.eigenvalues i₀ * (y i₀) ^ 2 < (0 : ℝ) :=
          mul_neg_of_neg_of_pos (hall i₀) (sq_pos_of_ne_zero hi₀)
        have hsum := Finset.sum_lt_sum hle ⟨i₀, Finset.mem_univ i₀, hlt⟩
        simpa using hsum
      simpa [Matrix.neg_mulVec, dotProduct_neg] using hneg_sum
  rw [hneg, hall_neg]
  constructor
  · intro hneg_eigs
    have hq : S.negEigenCount = n := by
      unfold negEigenCount
      rw [Finset.filter_true_of_mem fun i _ => hneg_eigs i, Finset.card_univ, Fintype.card_fin]
    have hsum := S.signature_sum
    have hp : S.posEigenCount = 0 := by omega
    have hl : S.zeroEigenCount = 0 := by omega
    simp [signature, hp, hq, hl]
  · intro hsig i
    have hq : S.negEigenCount = n := congr_arg (fun t => t.2.1) hsig
    unfold negEigenCount at hq
    have hall : (Finset.univ.filter fun j : Fin n => S.B_isHermitian.eigenvalues j < 0) =
        Finset.univ := Finset.eq_univ_of_card _ (by simpa using hq)
    have hi : i ∈ Finset.univ.filter fun j : Fin n => S.B_isHermitian.eigenvalues j < 0 := by
      rw [hall]; exact Finset.mem_univ i
    exact (Finset.mem_filter.mp hi).2

/-- **Definition 2.51**: The four signature classes of a reflection system:
`spherical`, `affine`, `hyperbolic`, and `higherRank`. -/
inductive SignatureType
  | spherical
  | affine
  | hyperbolic
  | higherRank
  deriving DecidableEq, Repr

/-- **Definition 2.51**: Classification of a rank-`n` reflection system by its signature
`sig(B) = (p, q, l)`:
1. `spherical` if `sig = (n, 0, 0)` or `(0, n, 0)`;
2. `affine` if `sig = (n - 1, 0, 1)` or `(0, n - 1, 1)`;
3. `hyperbolic` if `2 ≤ n` and `sig = (n - 1, 1, 0)` or `(1, n - 1, 0)`;
4. `higherRank` otherwise. -/
noncomputable def signatureType (S : ReflectionSystem n) : SignatureType :=
  if S.signature = (n, 0, 0) ∨ S.signature = (0, n, 0) then .spherical
  else if 1 ≤ n ∧ (S.signature = (n - 1, 0, 1) ∨ S.signature = (0, n - 1, 1)) then .affine
  else if 2 ≤ n ∧ (S.signature = (n - 1, 1, 0) ∨ S.signature = (1, n - 1, 0)) then .hyperbolic
  else .higherRank

/-- A reflection system is spherical iff it is positive or negative definite. -/
theorem signatureType_eq_spherical_iff (S : ReflectionSystem n) :
    S.signatureType = .spherical ↔ S.IsPosDef ∨ S.IsNegDef := by
  unfold signatureType
  rw [isPosDef_iff_signature, isNegDef_iff_signature]
  split_ifs <;> simp_all

/-- A reflection system is hyperbolic iff `2 ≤ n` and `sig(B) = (n - 1, 1, 0)` or `(1, n - 1, 0)`. -/
theorem signatureType_eq_hyperbolic_iff (S : ReflectionSystem n) :
    S.signatureType = .hyperbolic ↔
      2 ≤ n ∧ (S.signature = (n - 1, 1, 0) ∨ S.signature = (1, n - 1, 0)) := by
  unfold signatureType
  constructor
  · intro h
    split_ifs at h with h1 h2 h3
    exact h3
  · rintro ⟨hn, hsig⟩
    have hnot1 : ¬ (S.signature = (n, 0, 0) ∨ S.signature = (0, n, 0)) := by
      rcases hsig with h | h <;> rw [h] <;> simp <;> omega
    have hnot2 : ¬ (1 ≤ n ∧ (S.signature = (n - 1, 0, 1) ∨ S.signature = (0, n - 1, 1))) := by
      rintro ⟨_, h2⟩
      rcases hsig with h | h <;> rw [h] at h2 <;> simp at h2
    simp only [hnot1, hnot2, hn, hsig, and_self, ↓reduceIte]

/-- Any reflection system with at least 2 positive and at least 2 negative eigenvalues is
`higherRank` (explicitly separating higher-rank from hyperbolic indefinite systems). -/
theorem signatureType_eq_higherRank_of_two_pos_two_neg (S : ReflectionSystem n)
    (hp : 2 ≤ S.posEigenCount) (hq : 2 ≤ S.negEigenCount) :
    S.signatureType = .higherRank := by
  unfold signatureType
  have h1 : ¬ (S.signature = (n, 0, 0) ∨ S.signature = (0, n, 0)) := by
    simp only [signature, Prod.mk.injEq]; omega
  have h2 : ¬ (1 ≤ n ∧ (S.signature = (n - 1, 0, 1) ∨ S.signature = (0, n - 1, 1))) := by
    rintro ⟨_, h⟩; simp only [signature, Prod.mk.injEq] at h; omega
  have h3 : ¬ (2 ≤ n ∧ (S.signature = (n - 1, 1, 0) ∨ S.signature = (1, n - 1, 0))) := by
    rintro ⟨_, h⟩; simp only [signature, Prod.mk.injEq] at h; omega
  simp only [h1, h2, h3, ↓reduceIte]

end Signature

/-! ### Definition 2.56: Node Deletion `Γ / (r_i)` -/

section NodeDeletion

/-- **Definition 2.56**: The reflection system `Γ / (r_i)` obtained by deleting node `i`
and all incident edges from `S : ReflectionSystem (n + 1)`. -/
def deleteNode (S : ReflectionSystem (n + 1)) (i : Fin (n + 1)) : ReflectionSystem n where
  B := S.B.submatrix i.succAbove i.succAbove
  B_symm := by
    ext j k
    simp only [Matrix.transpose_apply, Matrix.submatrix_apply]
    exact congr_fun (congr_fun S.B_symm (i.succAbove j)) (i.succAbove k)
  B_diag_ne_zero j := S.B_diag_ne_zero (i.succAbove j)

@[simp]
lemma deleteNode_B (S : ReflectionSystem (n + 1)) (i : Fin (n + 1)) (j k : Fin n) :
    (S.deleteNode i).B j k = S.B (i.succAbove j) (i.succAbove k) := rfl

/-- Any relation among the remaining generators in `Γ` already holds in `Γ / (r_i)`. -/
theorem deleteNode_wordProd_sub_of_map (S : ReflectionSystem (n + 1)) (i : Fin (n + 1))
    (w₁ w₂ : List (Fin n))
    (h : wordProd S (w₁.map i.succAbove) = wordProd S (w₂.map i.succAbove)) :
    wordProd (S.deleteNode i) w₁ = wordProd (S.deleteNode i) w₂ :=
  wordProd_sub_eq_of_map S.B i.succAbove Fin.succAbove_right_injective w₁ w₂ h

/-- When `B(Γ / (r_i))` is nonsingular, relations in `Γ` on the remaining generators coincide
with relations in `Γ / (r_i)`. -/
theorem deleteNode_wordProd_eq_iff (S : ReflectionSystem (n + 1)) (i : Fin (n + 1))
    (hdet : (S.deleteNode i).B.det ≠ 0) (w₁ w₂ : List (Fin n)) :
    wordProd S (w₁.map i.succAbove) = wordProd S (w₂.map i.succAbove) ↔
      wordProd (S.deleteNode i) w₁ = wordProd (S.deleteNode i) w₂ :=
  ⟨deleteNode_wordProd_sub_of_map S i w₁ w₂,
   wordProd_map_eq_of_sub S.B i.succAbove hdet w₁ w₂⟩

end NodeDeletion

/-! ### Definition 2.61: Spectral Radius `λ(w)` -/

section SpectralRadius

/-- **Definition 2.61**: The spectral radius `λ(M) = sup {‖μ‖ | μ is a complex eigenvalue of M}`
of a real `n × n` matrix `M` (in particular, of a principal element `w ∈ W`). -/
noncomputable def spectralRadius (M : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  sSup { r : ℝ | ∃ μ : ℂ, MixedSignCoxeter.HasEigenC M μ ∧ r = ‖μ‖ }

/-- Every complex eigenvalue `μ` of `M` is bounded in modulus by `∑ i, ∑ j, ‖M i j‖`. -/
lemma norm_le_l1_of_hasEigenC (M : Matrix (Fin n) (Fin n) ℝ) {μ : ℂ}
    (hμ : MixedSignCoxeter.HasEigenC M μ) :
    ‖μ‖ ≤ ∑ i : Fin n, ∑ j : Fin n, ‖M i j‖ := by
  rcases hμ with ⟨v, hv, heig⟩
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    apply hv
    ext i
    exact absurd (Finset.mem_univ i) (by rw [hemp]; simp)
  obtain ⟨i₀, _, hi₀max⟩ := Finset.exists_max_image Finset.univ (fun i => ‖v i‖) hne
  have hvi₀ : 0 < ‖v i₀‖ := by
    by_contra hle
    push Not at hle
    apply hv
    ext j
    have hj : ‖v j‖ ≤ 0 := le_trans (hi₀max j (Finset.mem_univ j)) hle
    exact norm_eq_zero.mp (le_antisymm hj (norm_nonneg _))
  have hrow := congr_fun heig i₀
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.smul_apply, smul_eq_mul] at hrow
  have hbound : ‖μ‖ * ‖v i₀‖ ≤ (∑ j : Fin n, ‖M i₀ j‖) * ‖v i₀‖ := by
    rw [← norm_mul, ← hrow]
    calc
      ‖∑ j : Fin n, (M i₀ j : ℂ) * v j‖
        ≤ ∑ j : Fin n, ‖(M i₀ j : ℂ) * v j‖ := norm_sum_le _ _
      _ = ∑ j : Fin n, ‖M i₀ j‖ * ‖v j‖ := by
          refine Finset.sum_congr rfl fun j _ => by rw [norm_mul, Complex.norm_real]
      _ ≤ ∑ j : Fin n, ‖M i₀ j‖ * ‖v i₀‖ :=
          Finset.sum_le_sum fun j _ =>
            mul_le_mul_of_nonneg_left (hi₀max j (Finset.mem_univ j)) (norm_nonneg _)
      _ = (∑ j : Fin n, ‖M i₀ j‖) * ‖v i₀‖ := (Finset.sum_mul _ _ _).symm
  have hrow_le : ‖μ‖ ≤ ∑ j : Fin n, ‖M i₀ j‖ := le_of_mul_le_mul_right hbound hvi₀
  have hsum_le : ∑ j : Fin n, ‖M i₀ j‖ ≤ ∑ i : Fin n, ∑ j : Fin n, ‖M i j‖ :=
    Finset.single_le_sum (f := fun i => ∑ j : Fin n, ‖M i j‖)
      (fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _) (Finset.mem_univ i₀)
  exact le_trans hrow_le hsum_le

lemma hasEigenC_norms_bddAbove (M : Matrix (Fin n) (Fin n) ℝ) :
    BddAbove { r : ℝ | ∃ μ : ℂ, MixedSignCoxeter.HasEigenC M μ ∧ r = ‖μ‖ } := by
  refine ⟨∑ i : Fin n, ∑ j : Fin n, ‖M i j‖, ?_⟩
  rintro r ⟨μ, hμ, rfl⟩
  exact norm_le_l1_of_hasEigenC M hμ

/-- Every complex eigenvalue `μ` of `M` satisfies `‖μ‖ ≤ spectralRadius M`. -/
theorem norm_le_spectralRadius (M : Matrix (Fin n) (Fin n) ℝ) {μ : ℂ}
    (hμ : MixedSignCoxeter.HasEigenC M μ) :
    ‖μ‖ ≤ spectralRadius M :=
  le_csSup (hasEigenC_norms_bddAbove M) ⟨μ, hμ, rfl⟩

/-- If every complex eigenvalue of `M` has modulus `≤ C` (with `0 ≤ C`), then
`spectralRadius M ≤ C`. -/
theorem spectralRadius_le_of_forall (M : Matrix (Fin n) (Fin n) ℝ) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ μ : ℂ, MixedSignCoxeter.HasEigenC M μ → ‖μ‖ ≤ C) :
    spectralRadius M ≤ C := by
  apply Real.sSup_le
  · rintro r ⟨μ, hμ, rfl⟩
    exact h μ hμ
  · exact hC

/-- The spectral radius of any real matrix is nonnegative. -/
theorem spectralRadius_nonneg (M : Matrix (Fin n) (Fin n) ℝ) :
    0 ≤ spectralRadius M := by
  apply Real.sSup_nonneg
  rintro r ⟨μ, _, rfl⟩
  exact norm_nonneg μ

/-- If `M` has a complex eigenvalue `μ` with `c < ‖μ‖`, then `c < spectralRadius M`. -/
theorem lt_spectralRadius_of_eigen (M : Matrix (Fin n) (Fin n) ℝ) {μ : ℂ} {c : ℝ}
    (hμ : MixedSignCoxeter.HasEigenC M μ) (hc : c < ‖μ‖) :
    c < spectralRadius M :=
  lt_of_lt_of_le hc (norm_le_spectralRadius M hμ)

end SpectralRadius

end ReflectionSystem
