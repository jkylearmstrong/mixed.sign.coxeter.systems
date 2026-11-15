/-
Copyright (c) 2026 Johnathon Kyle Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MixedSignCoxeter.Basic

/-!
# Bipartite Reflection Diagrams and Theorem 1.4

Formalization of Section 2.4 and Theorem 1.4 of:
Johnathon Kyle Armstrong, *Principal Elements of Mixed-Sign Coxeter Systems* (FSU, 2012).

## Main results
* `bipartiteConjugator_mul_self`: `P * P = 1` (so `P ∈ 𝒪`).
* `bipartite_conjugation_theorem` (Theorem 1.4): For a bipartite reflection diagram `Γ`,
  `Pᵀ * B(Γ) * P = - B(Γ_-)`.
* `bipartite_conjugates_reflections`: `Pᵀ * s_i(Γ) * P = s_i(Γ_-)`.
-/

open Matrix BigOperators

namespace ReflectionSystem

variable {n : ℕ}

/-- Negate all diagonal node weights of `B` to form `B(Γ_-)` (Definition 2.43). -/
def negateDiag (B : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  of fun i j => if i = j then -B i j else B i j

@[simp]
lemma negateDiag_apply (B : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    negateDiag B i j = if i = j then -B i j else B i j := rfl

/-- A bipartite reflection system: nodes are partitioned by `part : Fin n → Bool`
into `N₁` (`true`) and `N₂` (`false`) with no edges within `N₁` or `N₂` (Definition 2.40). -/
structure BipartiteReflectionSystem (n : ℕ) extends ReflectionSystem n where
  part : Fin n → Bool
  bipartite_edges : ∀ i j : Fin n, part i = part j → i ≠ j → B i j = 0

/-- The orthogonal conjugator `P ∈ 𝒪` from the proof of Theorem 1.4:
`P = diag(±1)` with `-1` on `N₁` (`part i = true`) and `+1` on `N₂` (`part i = false`). -/
def bipartiteConjugator (part : Fin n → Bool) : Matrix (Fin n) (Fin n) ℝ :=
  diagonal fun i => if part i then -1 else 1

@[simp]
lemma bipartiteConjugator_apply (part : Fin n → Bool) (i j : Fin n) :
    bipartiteConjugator part i j = if i = j then (if part i then -1 else 1) else 0 :=
  diagonal_apply _ i j

lemma bipartiteConjugator_transpose (part : Fin n → Bool) :
    (bipartiteConjugator part)ᵀ = bipartiteConjugator part :=
  diagonal_transpose _

lemma bipartiteConjugator_mul_self (part : Fin n → Bool) :
    bipartiteConjugator part * bipartiteConjugator part = 1 := by
  ext i j
  simp only [bipartiteConjugator, diagonal_mul_diagonal, one_apply]
  by_cases hij : i = j
  · subst hij
    cases h : part i <;> simp [h]
  · simp [hij]

/-- **Theorem 1.4**: If `Γ` is a bipartite reflection diagram, then
`Pᵀ * B(Γ) * P = - B(Γ_-)` where `P ∈ 𝒪` is `bipartiteConjugator`. -/
theorem bipartite_conjugation_theorem (G : BipartiteReflectionSystem n) :
    (bipartiteConjugator G.part)ᵀ * G.B * bipartiteConjugator G.part =
      -negateDiag G.B := by
  rw [bipartiteConjugator_transpose]
  ext i j
  simp only [bipartiteConjugator, diagonal_mul, mul_diagonal]
  by_cases hij : i = j
  · subst hij
    cases h : G.part i <;> simp
  · have hdiff : G.part i ≠ G.part j ∨ G.B i j = 0 := by
      by_cases hp : G.part i = G.part j
      · exact Or.inr (G.bipartite_edges i j hp hij)
      · exact Or.inl hp
    rcases hdiff with hp | h0
    · cases hi : G.part i <;> cases hj : G.part j <;> simp_all
    · simp [hij, h0]

/-- Conjugating each generating reflection `s_i(Γ)` by `P` yields `s_i(Γ_-)`. -/
theorem bipartite_conjugates_reflections (G : BipartiteReflectionSystem n) (i : Fin n) :
    (bipartiteConjugator G.part)ᵀ * reflectionMatrix G.B i * bipartiteConjugator G.part =
      reflectionMatrix (negateDiag G.B) i := by
  rw [bipartiteConjugator_transpose]
  ext r c
  simp only [bipartiteConjugator, diagonal_mul, mul_diagonal, reflectionMatrix_apply,
    negateDiag_apply]
  by_cases hrc : r = c
  · subst hrc
    by_cases hri : r = i
    · subst hri
      cases h : G.part r <;> simp [G.B_diag_ne_zero r]
    · cases h : G.part r <;> simp [hri]
  · by_cases hri : r = i
    · subst hri
      have hne : r ≠ c := hrc
      by_cases hp : G.part r = G.part c
      · have h0 := G.bipartite_edges r c hp hne
        simp [hne, h0]
      · cases hr : G.part r <;> cases hc : G.part c <;> simp_all <;> ring
    · cases hr : G.part r <;> cases hc : G.part c <;> simp [hrc, hri]

/-- Conjugating any word product in `W(Γ)` by `P` yields the corresponding word product in `W(Γ_-)`. -/
theorem bipartite_conjugates_wordProd (G : BipartiteReflectionSystem n) (w : List (Fin n)) :
    (bipartiteConjugator G.part)ᵀ * wordProd G.toReflectionSystem w * bipartiteConjugator G.part =
      (w.map (reflectionMatrix (negateDiag G.B))).prod := by
  induction w with
  | nil =>
    simp [wordProd, bipartiteConjugator_transpose, bipartiteConjugator_mul_self]
  | cons a t ih =>
    simp only [wordProd, List.map_cons, List.prod_cons]
    have ha := bipartite_conjugates_reflections G a
    have hP : bipartiteConjugator G.part * (bipartiteConjugator G.part)ᵀ = 1 := by
      rw [bipartiteConjugator_transpose]
      exact bipartiteConjugator_mul_self G.part
    calc
      (bipartiteConjugator G.part)ᵀ *
          (reflectionMatrix G.B a * (List.map (reflectionMatrix G.B) t).prod) *
          bipartiteConjugator G.part
          = ((bipartiteConjugator G.part)ᵀ * reflectionMatrix G.B a * bipartiteConjugator G.part) *
              ((bipartiteConjugator G.part)ᵀ * (List.map (reflectionMatrix G.B) t).prod *
                bipartiteConjugator G.part) := by
            simp only [Matrix.mul_assoc]
            rw [← Matrix.mul_assoc (bipartiteConjugator G.part) (bipartiteConjugator G.part)ᵀ, hP,
              Matrix.one_mul]
      _ = reflectionMatrix (negateDiag G.B) a * (List.map (reflectionMatrix (negateDiag G.B)) t).prod := by
            simp only [wordProd] at ih
            rw [ha, ih]

/-- **Theorem 1.4 (principal polynomial equality)**: Conjugation by `P` preserves the
characteristic polynomial of every word (and in particular every principal element). -/
theorem bipartite_conjugates_charpoly (G : BipartiteReflectionSystem n) (w : List (Fin n)) (x : ℝ) :
    (x • (1 : Matrix (Fin n) (Fin n) ℝ) - wordProd G.toReflectionSystem w).det =
      (x • (1 : Matrix (Fin n) (Fin n) ℝ) -
        (w.map (reflectionMatrix (negateDiag G.B))).prod).det := by
  have hP : (bipartiteConjugator G.part)ᵀ * bipartiteConjugator G.part = 1 := by
    rw [bipartiteConjugator_transpose]
    exact bipartiteConjugator_mul_self G.part
  have hconj :
      (bipartiteConjugator G.part)ᵀ *
          (x • (1 : Matrix (Fin n) (Fin n) ℝ) - wordProd G.toReflectionSystem w) *
          bipartiteConjugator G.part =
        x • (1 : Matrix (Fin n) (Fin n) ℝ) -
          (w.map (reflectionMatrix (negateDiag G.B))).prod := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hP,
      bipartite_conjugates_wordProd]
  have hdet := congr_arg Matrix.det hconj
  rw [Matrix.det_mul, Matrix.det_mul, mul_comm _ (x • (1 : Matrix (Fin n) (Fin n) ℝ) - wordProd G.toReflectionSystem w).det,
    mul_assoc, ← Matrix.det_mul, hP, Matrix.det_one, mul_one] at hdet
  exact hdet

/-- **Proposition 2.41 / 3.32 (same-part commutativity)**: In a bipartite reflection
system, any two generating reflections in the same part commute. -/
theorem bipartite_same_part_comm (G : BipartiteReflectionSystem n) {i j : Fin n}
    (hij : G.part i = G.part j) :
    reflectionMatrix G.B i * reflectionMatrix G.B j =
      reflectionMatrix G.B j * reflectionMatrix G.B i := by
  by_cases h : i = j
  · subst h; rfl
  · exact reflectionMatrix_comm_of_orthogonal G.toReflectionSystem (G.bipartite_edges i j hij h)

/-- Any permutation of a word whose letters all lie in the same part `b` produces the
exact same group element. -/
theorem bipartite_wordProd_perm (G : BipartiteReflectionSystem n) (b : Bool)
    {l₁ l₂ : List (Fin n)} (hperm : l₁.Perm l₂) (hb : ∀ i ∈ l₁, G.part i = b) :
    wordProd G.toReflectionSystem l₁ = wordProd G.toReflectionSystem l₂ := by
  induction hperm with
  | nil => rfl
  | @cons x l₁ l₂ _ ih =>
    simp only [wordProd, List.map_cons, List.prod_cons]
    congr 1
    exact ih (fun i hi => hb i (List.mem_cons_of_mem x hi))
  | @swap x y l =>
    simp only [wordProd, List.map_cons, List.prod_cons, ← mul_assoc]
    have hx : G.part x = b := hb x (by simp)
    have hy : G.part y = b := hb y (by simp)
    have hcomm := bipartite_same_part_comm G (hx.trans hy.symm)
    rw [hcomm]
  | @trans l₁ l₂ l₃ h₁₂ _ ih₁ ih₂ =>
    have hb₂ : ∀ i ∈ l₂, G.part i = b := fun i hi => hb i (h₁₂.symm.mem_iff.mp hi)
    exact (ih₁ hb).trans (ih₂ hb₂)

/-- Every word product has an explicit inverse `wordProd S w.reverse`. -/
lemma wordProd_mul_reverse (S : ReflectionSystem n) (w : List (Fin n)) :
    wordProd S w * wordProd S w.reverse = 1 := by
  induction w with
  | nil => simp [wordProd]
  | cons a t ih =>
    simp only [wordProd, List.reverse_cons, List.map_append, List.prod_append,
      List.map_cons, List.prod_cons, List.map_nil, List.prod_nil, mul_one]
    calc reflectionMatrix S.B a * (t.map (reflectionMatrix S.B)).prod *
          ((t.reverse.map (reflectionMatrix S.B)).prod * reflectionMatrix S.B a)
        = reflectionMatrix S.B a *
            ((t.map (reflectionMatrix S.B)).prod * (t.reverse.map (reflectionMatrix S.B)).prod) *
            reflectionMatrix S.B a := by simp only [mul_assoc]
      _ = reflectionMatrix S.B a * 1 * reflectionMatrix S.B a := by
            have h1 : (t.map (reflectionMatrix S.B)).prod *
                (t.reverse.map (reflectionMatrix S.B)).prod = 1 := ih
            rw [h1]
      _ = 1 := by
            rw [mul_one]
            exact reflectionMatrix_mul_self S a

/-- **Proposition 3.32**: All bipartite principal elements (any ordering of `N₁` followed
by `N₂`, or `N₂` followed by `N₁`) are conjugate. -/
theorem bipartite_principalElements_conjugate (G : BipartiteReflectionSystem n)
    {a₁ a₂ b₁ b₂ : List (Fin n)} (ha : a₁.Perm a₂) (hb : b₁.Perm b₂)
    (ha_part : ∀ i ∈ a₁, G.part i = true) (hb_part : ∀ i ∈ b₁, G.part i = false) :
    (wordProd G.toReflectionSystem (a₁ ++ b₁) =
      wordProd G.toReflectionSystem (a₂ ++ b₂)) ∧
    (∃ g g_inv : Matrix (Fin n) (Fin n) ℝ, g * g_inv = 1 ∧ g_inv * g = 1 ∧
      g_inv * wordProd G.toReflectionSystem (a₁ ++ b₁) * g =
        wordProd G.toReflectionSystem (b₂ ++ a₂)) := by
  have hA : wordProd G.toReflectionSystem a₁ = wordProd G.toReflectionSystem a₂ :=
    bipartite_wordProd_perm G true ha ha_part
  have hB : wordProd G.toReflectionSystem b₁ = wordProd G.toReflectionSystem b₂ :=
    bipartite_wordProd_perm G false hb hb_part
  have hsplit : ∀ u v : List (Fin n),
      wordProd G.toReflectionSystem (u ++ v) =
        wordProd G.toReflectionSystem u * wordProd G.toReflectionSystem v := by
    intro u v; simp [wordProd]
  constructor
  · rw [hsplit, hsplit, hA, hB]
  · refine ⟨wordProd G.toReflectionSystem a₁, wordProd G.toReflectionSystem a₁.reverse,
      wordProd_mul_reverse G.toReflectionSystem a₁, ?_, ?_⟩
    · simpa [List.reverse_reverse] using wordProd_mul_reverse G.toReflectionSystem a₁.reverse
    · rw [hsplit, hsplit, ← hA, ← hB]
      have hinv : wordProd G.toReflectionSystem a₁.reverse * wordProd G.toReflectionSystem a₁ = 1 := by
        simpa [List.reverse_reverse] using wordProd_mul_reverse G.toReflectionSystem a₁.reverse
      calc wordProd G.toReflectionSystem a₁.reverse *
            (wordProd G.toReflectionSystem a₁ * wordProd G.toReflectionSystem b₁) *
            wordProd G.toReflectionSystem a₁
          = (wordProd G.toReflectionSystem a₁.reverse * wordProd G.toReflectionSystem a₁) *
              wordProd G.toReflectionSystem b₁ * wordProd G.toReflectionSystem a₁ := by
            simp only [mul_assoc]
        _ = wordProd G.toReflectionSystem b₁ * wordProd G.toReflectionSystem a₁ := by
            rw [hinv, one_mul]

end ReflectionSystem

