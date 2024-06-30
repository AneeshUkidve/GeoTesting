import Mathlib.Geometry.Euclidean.PerpBisector
import Mathlib.Geometry.Euclidean.Sphere.Basic
import Mathlib.Geometry.Euclidean.Circumcenter

open Set
open scoped RealInnerProductSpace

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
variable [NormedAddTorsor V P]



/-variable {a b c d: P}-/

def coll : P → P → P → Prop
  | a, b, c => Collinear ℝ ({a, b, c} : Set P)


/-Rule 1-/
theorem coll_symm1 : ∀ a b c : P, coll a b c → coll b a c := by
  simp [coll]
  intro a b c h
  have h1 : ({a, b, c} : Set P) = ({b, a, c} : Set P) := by
    simp [Set.ext_iff]
    intro p
    apply Iff.intro
    intro h1
    apply Or.rotate; apply Or.rotate
    cases h1; rename_i h1
    left
    exact h1
    right
    rename_i h1
    exact Or.symm h1
    intro h1
    apply Or.rotate; apply Or.rotate
    cases h1; rename_i h1
    left
    exact h1
    right
    rename_i h1
    exact Or.symm h1
  rw [←h1]
  exact h



/-Rule 2-/
theorem coll_symm2 : ∀ a b c : P, coll a b c → coll c a b := by
  simp [coll]
  intro a b c h/-Rule 2-/
  have h1 : ({a, b, c} : Set P) = ({c, a, b} : Set P) := by
    ext
    rename_i p
    simp
    apply Iff.intro
    intro h
    apply Or.rotate; apply Or.rotate
    exact h
    intro h
    apply Or.rotate
    exact h
  rw [h1] at h
  exact h

/-Technically Rule 2-/
theorem coll_symm2' : ∀ a b c : P, coll a b c → coll a c b := by
  intro a b c h
  apply coll_symm2 at h
  apply coll_symm1 at h
  exact h

/-Rule 3-/
theorem coll4Points : ∀ a b c d : P , (a ≠ b) ∧ (coll a b c) ∧ (coll a b d) → coll a c d := by
  simp [coll]
  intro a b c d h0 h1 h2
  have ha : a ∈ ({a, b, c} : Set P) := by
    simp
  have hb : b ∈ ({a, b, c} : Set P) := by
    simp
  have hc : c ∈ ({a, b, c} : Set P) := by
    simp
  let hf1 := Collinear.mem_affineSpan_of_mem_of_ne h1 ha hb hc h0

  have ha : a ∈ ({a, b, d} : Set P) := by
    simp
  have hb : b ∈ ({a, b, d} : Set P) := by
    simp
  have hc : d ∈ ({a, b, d} : Set P) := by
    simp
  let hf2 := Collinear.mem_affineSpan_of_mem_of_ne h2 ha hb hc h0

  let hsup := collinear_insert_insert_of_mem_affineSpan_pair hf1 hf2

  have hsub : ({a, c, d} : Set P) ⊆ {c, d, a, b} := by
    simp [Set.subset_def]

  exact Collinear.subset hsub hsup

def para : P → P → P → P → Prop
  | a, b, c, d => AffineSubspace.Parallel line[ℝ, a, b] line[ℝ, c, d]

/-Rule 4-/
theorem para_symm1 : ∀ a b c d : P, para a b c d → para b a c d := by
  simp [para]
  intro a b c d h
  have h0 : ({a, b} : Set P) = {b, a} := by
    ext
    rename_i p
    apply Iff.intro
    intro h; cases h;rename_i h; simp; right; exact h
    rename_i h; simp; simp at h; left; exact h
    intro h; cases h;rename_i h; simp; right; exact h
    rename_i h; simp; simp at h; left; exact h
  have h1 : line[ℝ, a, b] = line[ℝ, b, a] := by
    rw [h0]
  rw [←h1]
  exact h

/-Rule 5-/
theorem para_symm2 : ∀ a b c d : P, para a b c d → para c d a b := by
  simp [para]
  intro a b c d h
  exact AffineSubspace.Parallel.symm h

/-Rule 6-/
theorem paraLines : ∀ a b c d e f : P, (para a b c d) ∧ (para c d e f) → para a b e f := by
  simp [para]
  intro a b c d e f h1 h2
  exact AffineSubspace.Parallel.trans h1 h2

def perp : P → P → P → P → Prop
  | a, b, c, d => (⟪a -ᵥ b, c -ᵥ d⟫ = 0) ∧ (Coplanar ℝ ({a, b, c, d}))

/-Rule 7-/
theorem perp_symm1 : ∀ a b c d : P, perp a b c d → perp b a c d := by
  simp [perp]
  intro a b c d h hc
  let h1 := real_inner_smul_left (a -ᵥ b) (c -ᵥ d) (-1)
  rw [h] at h1
  simp at h1
  apply And.intro
  exact h1
  have h2 : ({b, a, c, d} : Set P) = {a, b, c, d} := by
    simp [Set.Subset.antisymm_iff]
    simp [subset_def]
  rw [h2]
  exact hc

/-Rule 8-/
theorem perp_symm2 : ∀ a b c d : P, perp a b c d → perp c d a b := by
  simp [perp]
  intro a b c d h hc
  let h0 := real_inner_comm (a -ᵥ b) (c -ᵥ d)
  rw [h0]
  apply And.intro
  exact h
  have h2 : ({c, d, a, b} : Set P) = {a, b, c, d} := by
    simp [Set.Subset.antisymm_iff]
    simp [subset_def]
  rw [h2]
  exact hc


/-rule 9-/
theorem perpPerpPara : ∀ a b c d e f : P, (perp a b c d) ∧ (perp c d e f) → para a b e f := by
  simp [perp, para]
  intro a b c d e f h1 h2
  sorry

def midp : P → P → P → Prop
  | m, a, b => (m = midpoint ℝ a b)

/-Rule 10-/
theorem midp_symm : ∀ m a b : P, midp m a b → midp m b a := by
  simp [midp]
  intro m a b h
  rw [midpoint_comm]
  exact h

def cong : P → P → P → P → Prop
  | a, b, c, d => dist a b = dist c d

def circ : P → P → P → P → Prop
  | o, a, b, c => {a, b, c} ⊆ (Metric.sphere o (dist o a))

/-Rule 11-/
theorem cong_eq_circ : ∀ o a b c : P, (cong o a o b) ∧ (cong o a o c) → circ o a b c := by
  simp [cong, circ]
  intro o a b c h1 h2
  simp [Set.subset_def]
  apply And.intro
  simp [dist_comm]
  apply And.intro
  simp [dist_comm]
  exact Eq.symm h1
  simp [dist_comm]
  exact Eq.symm h2

def cycl : P → P → P → P → Prop
  | a, b, c, d => (EuclideanGeometry.Cospherical ({a, b, c, d} : Set P)) ∧ (Coplanar ℝ {a, b, c, d})

/-Rule 12-/
theorem cycl_quad : ∀ o a b c d : P, (cong o a o b) ∧ (cong o a o c) ∧ (cong o a o d) ∧ (Coplanar ℝ {o, a, b, c, d}) → cycl a b c d := by
  simp [cong, cycl]
  intro o a b c d h1 h2 h3 hc
  have hg1 : EuclideanGeometry.Cospherical {a, b, c, d} := by
    simp [EuclideanGeometry.cospherical_def]
    exists o
    apply And.intro
    rw [dist_comm b o, dist_comm a o]; exact Eq.symm h1
    apply And.intro
    rw [dist_comm c o, dist_comm a o]; exact Eq.symm h2
    rw [dist_comm d o, dist_comm a o]; exact Eq.symm h3

  have hg2 : Coplanar ℝ {a, b, c, d} := by
    have hs : ({a, b, c, d} : Set P) ⊆ {o, a, b, c, d} := by simp [subset_def]
    exact Coplanar.subset hs hc
  exact ⟨hg1, hg2⟩

/-Rule 13-/
theorem cycl_symm1 : ∀ a b c d : P, cycl a b c d → cycl b a c d := by
  simp [cycl]
  intro a b c d h1 h2
  have hs : ({b, a, c, d} : Set P) = {a, b, c, d} := by
    simp [Set.Subset.antisymm_iff, Set.subset_def]
  rw [hs]
  exact ⟨h1, h2⟩

/-Rule 14-/
theorem cycl_symm2 : ∀ a b c d : P, cycl a b c d → cycl a c b d := by
  simp [cycl]
  intro a b c d h1 h2
  have hs : ({a, c, b, d} : Set P) = {a, b, c, d} := by
    simp [Set.Subset.antisymm_iff, Set.subset_def]
  rw [hs]
  exact ⟨h1, h2⟩

/-Rule 15-/
theorem cycl_symm3 : ∀ a b c d : P, cycl a b c d → cycl a b d c := by
  simp [cycl]
  intro a b c d h1 h2
  have hs : ({a, b, d, c} : Set P) = {a, b, c, d} := by
    simp [Set.Subset.antisymm_iff, Set.subset_def]
  rw [hs]
  exact ⟨h1, h2⟩

/-Rule 16-/
theorem cycl5points : ∀ a b c d e : P, (cycl a b c d) ∧ (cycl a b c e) ∧ (a ≠ b) ∧ (a ≠ c) ∧ (b ≠ c) → cycl a b d e := by
  simp [cycl]
  intro a b c d e h1 hc1 h2 hc2 hab hac hbc
  let s := affineSpan ℝ {a, b, c}

  have habc : Coplanar ℝ {a, b, c} := by
    have hs : ({a, b, c} : Set P) ⊆ {a, b, c, d} := by simp [subset_def]
    exact Coplanar.subset hs hc1

  have hsp : EuclideanGeometry.Cospherical {a, b, c} := by
    have hs : ({a, b, c} : Set P) ⊆ {a, b, c, d} := by simp [subset_def]
    exact EuclideanGeometry.Cospherical.subset hs h1

  let hind := EuclideanGeometry.Cospherical.affineIndependent_of_ne hsp hab hac hbc

  have hs1 : ({a, b, c} : Set P).Finite := by
    simp
  let hs2 := finiteDimensional_vectorSpan_of_finite ℝ hs1
  let habc2 := Coplanar.finrank_le_two habc

  have hd : FiniteDimensional.finrank ℝ s.direction = 2 := by



#check finiteDimensional_vectorSpan_of_finite






/-Rule 17-/
theorem cong_symm1 : ∀ a b c d : P, cong a b c d → cong b a c d := by
  simp [cong]; intro a b c d h; rw [dist_comm]; exact h

/-Rule 18-/
theorem cong_symm2 : ∀ a b c d : P, cong a b c d → cong c d a b := by
  simp [cong]; intro a b c d h; exact Eq.symm h

/-Rule 19-/
theorem cong_trans : ∀ a b c d e f : P, (cong a b c d) ∧ (cong c d e f) → cong a b e f := by
  simp [cong]; intro a b c d e f h1 h2; exact Eq.trans h1 h2

def eqratio : P → P → P → P → P → P → P → P → Prop
  | a, b, c, d, p, q, r, s => (dist a b) * (dist r s) = (dist p q) * (dist c d)

/-Rule 20-/
theorem eqratio_symm1 : ∀ a b c d p q r s : P, eqratio a b c d p q r s → eqratio b a c d p q r s := by
  simp [eqratio]; intro a b c d p q r s h; rw [dist_comm]; exact h

/-Rule 21-/
theorem eqratio_symm2 : ∀ a b c d p q r s : P, eqratio a b c d p q r s → eqratio c d a b r s p q := by
  simp [eqratio]; intro a b c d p q r s h; rw [mul_comm, mul_comm (dist r s)]; exact Eq.symm h

/-Rule 22-/
theorem eqratio_symm3 : ∀ a b c d p q r s : P, eqratio a b c d p q r s → eqratio p q r s a b c d := by
  simp [eqratio]; intro a b c d p q r s h; exact Eq.symm h

/-Rule 23-/
theorem eqratio_symm4 : ∀ a b c d p q r s : P, eqratio a b c d p q r s → eqratio a b p q c d r s:= by
  simp [eqratio]; intro a b c d p q r s h; rw [mul_comm (dist c d)]; exact h

/-Rule 24-/
theorem eqratio_trans : ∀ a b c d p q r s u v w x : P, eqratio a b c d p q r s ∧ eqratio p q r s u v w x → eqratio a b c d u v w x := by
  simp [eqratio]; intro a b c d p q r s u v w x h1 h2;
  let A := dist a b; let B := dist c d
  let C := dist p q; let D := dist r s
  let E := dist u v; let F := dist w x
  have h1' : A * D = C * B := by simp [h1]
  have h2' : C * F = E * D := by simp [h2]
  sorry
