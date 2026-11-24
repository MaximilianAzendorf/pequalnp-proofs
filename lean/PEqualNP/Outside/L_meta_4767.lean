import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4767

open PEqualNP.CircuitLowerBounds

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_def (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.wires ⟨gs, o⟩ x = gs.foldl stp x := rfl

lemma stp_length (w : List Bool) (g : Gate) : (stp w g).length = w.length + 1 := by
  simp [stp]

lemma fold_length (gs : List Gate) : ∀ x : List Bool,
    (gs.foldl stp x).length = x.length + gs.length := by
  induction gs with
  | nil => intro x; simp
  | cons g gs ih =>
    intro x
    rw [List.foldl_cons, ih, stp_length, List.length_cons]
    omega

lemma stp_getD_lt (w : List Bool) (g : Gate) (j : ℕ) (hj : j < w.length) :
    (stp w g).getD j false = w.getD j false :=
  List.getD_append _ _ _ _ hj

lemma stp_getD_len (w : List Bool) (g : Gate) :
    (stp w g).getD w.length false
      = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  simp [stp]

lemma fold_getD_lt (gs : List Gate) : ∀ (x : List Bool) (j : ℕ), j < x.length →
    (gs.foldl stp x).getD j false = x.getD j false := by
  induction gs with
  | nil => intro x j _; rfl
  | cons g gs ih =>
    intro x j hj
    rw [List.foldl_cons, ih _ _ (by rw [stp_length]; omega)]
    exact stp_getD_lt _ _ _ hj

lemma fold_gate (pre : List Gate) (g : Gate) (post : List Gate) (x : List Bool) :
    ((pre ++ g :: post).foldl stp x).getD (x.length + pre.length) false
      = g.op.eval (g.inputs.map fun j =>
          if j < x.length + pre.length then
            ((pre ++ g :: post).foldl stp x).getD j false else false) := by
  have hw : (pre.foldl stp x).length = x.length + pre.length := fold_length pre x
  rw [List.foldl_append, List.foldl_cons]
  rw [fold_getD_lt post _ _ (by rw [stp_length]; omega)]
  have h1 : (stp (pre.foldl stp x) g).getD (x.length + pre.length) false
      = g.op.eval (g.inputs.map fun i => (pre.foldl stp x).getD i false) := by
    rw [← hw]
    exact stp_getD_len _ _
  rw [h1]
  congr 1
  apply List.map_congr_left
  intro j _
  by_cases hj : j < x.length + pre.length
  · simp only [hj, ite_true]
    rw [fold_getD_lt post _ _ (by rw [stp_length]; omega)]
    exact (stp_getD_lt _ _ _ (by omega)).symm
  · simp only [hj, ite_false]
    exact List.getD_eq_default _ _ (by omega)

def W {n : ℕ} (gs : List Gate) (j : ℕ) (x : Fin n → Bool) : Bool :=
  (gs.foldl stp (List.ofFn x)).getD j false

lemma W_input {n : ℕ} (gs : List Gate) (j : ℕ) (hj : j < n) (x : Fin n → Bool) :
    W gs j x = x ⟨j, hj⟩ := by
  unfold W
  rw [fold_getD_lt gs _ _ (by simpa using hj)]
  simp [List.getD_eq_getElem?_getD, hj]

lemma W_oob {n : ℕ} (gs : List Gate) (j : ℕ) (hj : n + gs.length ≤ j) (x : Fin n → Bool) :
    W gs j x = false := by
  unfold W
  apply List.getD_eq_default
  rw [fold_length]
  simpa using hj

lemma W_gate_aux {n : ℕ} (pre : List Gate) (g : Gate) (post : List Gate) (x : Fin n → Bool) :
    W (pre ++ g :: post) (n + pre.length) x
      = g.op.eval (g.inputs.map fun j =>
          if j < n + pre.length then W (pre ++ g :: post) j x else false) := by
  have h := fold_gate pre g post (List.ofFn x)
  simp only [List.length_ofFn] at h
  exact h

lemma W_gate {n : ℕ} (gs : List Gate) (i : ℕ) (hi : i < gs.length) (x : Fin n → Bool) :
    W gs (n + i) x
      = (gs[i]).op.eval ((gs[i]).inputs.map fun j =>
          if j < n + i then W gs j x else false) := by
  have hsplit : gs.take i ++ gs[i] :: gs.drop (i + 1) = gs := by
    rw [← List.drop_eq_getElem_cons hi, List.take_append_drop]
  have h := W_gate_aux (n := n) (gs.take i) gs[i] (gs.drop (i + 1)) x
  rw [hsplit] at h
  simpa [List.length_take, Nat.min_eq_left hi.le] using h

lemma W_and {n : ℕ} (gs : List Gate) (i : ℕ) (hi : i < gs.length)
    (hop : (gs[i]).op = GateOp.and) (x : Fin n → Bool) :
    W gs (n + i) x = true ↔ ∀ j ∈ (gs[i]).inputs, j < n + i ∧ W gs j x = true := by
  rw [W_gate gs i hi x, hop]
  simp [GateOp.eval]

lemma W_or {n : ℕ} (gs : List Gate) (i : ℕ) (hi : i < gs.length)
    (hop : (gs[i]).op = GateOp.or) (x : Fin n → Bool) :
    W gs (n + i) x = true ↔ ∃ j ∈ (gs[i]).inputs, j < n + i ∧ W gs j x = true := by
  rw [W_gate gs i hi x, hop]
  simp [GateOp.eval]

lemma W_mono {n : ℕ} (gs : List Gate)
    (hops : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin n → Bool) (hxy : ∀ k, x k = true → y k = true) :
    ∀ j, W gs j x = true → W gs j y = true := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    by_cases hj : j < n
    · rw [W_input gs j hj] at h ⊢
      exact hxy _ h
    · by_cases hj2 : j < n + gs.length
      · obtain ⟨i, rfl⟩ : ∃ i, j = n + i := ⟨j - n, by omega⟩
        have hi : i < gs.length := by omega
        rcases hops gs[i] (List.getElem_mem hi) with hop | hop
        · rw [W_and gs i hi hop] at h ⊢
          intro k hk
          exact ⟨(h k hk).1, ih k (h k hk).1 (h k hk).2⟩
        · rw [W_or gs i hi hop] at h ⊢
          obtain ⟨k, hk, hlt, hv⟩ := h
          exact ⟨k, hk, hlt, ih k hlt hv⟩
      · rw [W_oob gs j (by omega)] at h
        exact absurd h (by simp)

def ind {n : ℕ} (z : Sym2 (Fin n)) : Fin n → Bool := fun k => decide (k ∈ z)

def acc {n : ℕ} (gs : List Gate) (j : ℕ) (z : Sym2 (Fin n)) : Prop :=
  W gs j (ind z) = true

lemma acc_mono {n : ℕ} (gs : List Gate)
    (hops : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (j : ℕ) (v : Fin n) (z : Sym2 (Fin n)) (hv : v ∈ z) (h : acc gs j s(v, v)) :
    acc gs j z := by
  refine W_mono gs hops _ _ ?_ j h
  intro k hk
  simp only [ind, decide_eq_true_eq, Sym2.mem_iff, or_self] at hk ⊢
  rw [hk]
  exact hv

lemma acc_input {n : ℕ} (gs : List Gate) (j : ℕ) (hj : j < n) (z : Sym2 (Fin n)) :
    acc gs j z ↔ (⟨j, hj⟩ : Fin n) ∈ z := by
  unfold acc
  rw [W_input gs j hj]
  simp [ind]

lemma acc_oob {n : ℕ} (gs : List Gate) (j : ℕ) (hj : n + gs.length ≤ j) (z : Sym2 (Fin n)) :
    ¬ acc gs j z := by
  unfold acc
  rw [W_oob gs j hj]
  simp

def Sg {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate) (j : ℕ) (v : Fin n) : Prop :=
  acc gs j s(v, v) ∧ ∃ u, G.Adj v u

def Q {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate) (j : ℕ) (e : Sym2 (Fin n)) : Prop :=
  e ∈ G.edgeSet ∧ acc gs j e ∧ ∀ v ∈ e, ¬ acc gs j s(v, v)

def L {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate) (j : ℕ) (e : Sym2 (Fin n)) : Prop :=
  ∃ a b b', e = s(a, b) ∧ Sg G gs j b ∧ Sg G gs j b' ∧ b ≠ b' ∧ ∀ c, Sg G gs j c → G.Adj a c

def X {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate) (j : ℕ) (e : Sym2 (Fin n)) : Prop :=
  Q G gs j e ∨ L G gs j e

def OKw {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate)
    (ch : ℕ → Option (Sym2 (Fin n))) (D : Finset (Sym2 (Fin n))) (T : Finset (Fin n))
    (j : ℕ) : Prop :=
  (∀ e, X G gs j e → e ∈ D ∨ ch j = some e) ∧
  (∀ b, (∀ v, Sg G gs j v ↔ v = b) → ch j = none) ∧
  (∀ e, Q G gs j e → ∃ t ∈ T, t ∈ e)

def Good {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate)
    (D : Finset (Sym2 (Fin n))) (T : Finset (Fin n)) (w : ℕ) : Prop :=
  ∃ (c d : Option (Sym2 (Fin n))) (t : Option (Fin n)),
    (∀ e, X G gs w e → e ∈ D ∨ c = some e ∨ d = some e) ∧
    (∀ b, (∀ v, Sg G gs w v ↔ v = b) → c = none) ∧
    (∀ e, Q G gs w e → (∃ t' ∈ T, t' ∈ e) ∨ ∃ t', t = some t' ∧ t' ∈ e) ∧
    (d = none ∨ t = none)

lemma tri {n : ℕ} (p : Fin n → Prop) :
    (∀ v, ¬ p v) ∨ (∃ b, ∀ v, p v ↔ v = b) ∨ (∃ b b', b ≠ b' ∧ p b ∧ p b') := by
  by_cases h : ∃ b, p b
  · obtain ⟨b, hb⟩ := h
    by_cases h2 : ∃ b', b' ≠ b ∧ p b'
    · obtain ⟨b', hne, hb'⟩ := h2
      exact Or.inr (Or.inr ⟨b, b', hne.symm, hb, hb'⟩)
    · refine Or.inr (Or.inl ⟨b, fun v => ⟨fun hv => ?_, fun hv => hv ▸ hb⟩⟩)
      by_contra hne
      exact h2 ⟨v, hne, hv⟩
  · exact Or.inl (fun v hv => h ⟨v, hv⟩)

lemma center_unique {n : ℕ} (G : SimpleGraph (Fin n))
    (hC4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (p : Fin n → Prop) (b b' : Fin n) (hne : b ≠ b') (hb : p b) (hb' : p b')
    (a a' : Fin n) (ha : ∀ c, p c → G.Adj a c) (ha' : ∀ c, p c → G.Adj a' c) : a = a' := by
  by_contra h
  exact hC4 a b a' b' h hne ⟨ha b hb, (ha' b hb).symm, ha' b' hb', (ha b' hb').symm⟩

lemma nbr_of_mem {n : ℕ} (G : SimpleGraph (Fin n)) (e : Sym2 (Fin n)) (he : e ∈ G.edgeSet)
    (x : Fin n) (hx : x ∈ e) : ∃ u, G.Adj x u := by
  induction e using Sym2.ind with
  | _ u v =>
    rw [SimpleGraph.mem_edgeSet] at he
    rcases Sym2.mem_iff.mp hx with h | h
    · exact ⟨v, h ▸ he⟩
    · exact ⟨u, h ▸ he.symm⟩

lemma OKw_dead {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate)
    (ch : ℕ → Option (Sym2 (Fin n))) (D : Finset (Sym2 (Fin n))) (T : Finset (Fin n))
    (j : ℕ) (hdead : ∀ z : Sym2 (Fin n), ¬ acc gs j z) : OKw G gs ch D T j := by
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    rcases he with hq | ⟨a, b, b', -, hb, -⟩
    · exact absurd hq.2.1 (hdead e)
    · exact absurd hb.1 (hdead _)
  · intro b hb
    exact absurd ((hb b).mpr rfl).1 (hdead _)
  · intro e he
    exact absurd he.2.1 (hdead e)

lemma side {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate)
    (ch : ℕ → Option (Sym2 (Fin n))) (D : Finset (Sym2 (Fin n))) (T : Finset (Fin n))
    (j : ℕ) (hj : OKw G gs ch D T j) (a : Fin n) (ha : ∀ b, Sg G gs j b → G.Adj a b) :
    ∃ c : Option (Sym2 (Fin n)), (∀ e, X G gs j e → e ∈ D ∨ c = some e) ∧
      (∀ b, Sg G gs j b → s(a, b) ∈ D ∨ c = some s(a, b)) := by
  rcases tri (Sg G gs j) with h0 | ⟨b, hb⟩ | ⟨b, b', hne, hb, hb'⟩
  · exact ⟨ch j, hj.1, fun b hb => absurd hb (h0 b)⟩
  · have hnone := hj.2.1 b hb
    refine ⟨some s(a, b), fun e he => Or.inl ?_, fun b2 hb2 => Or.inr ?_⟩
    · rcases hj.1 e he with h | h
      · exact h
      · rw [hnone] at h
        cases h
    · rw [(hb b2).mp hb2]
  · refine ⟨ch j, hj.1, fun b2 hb2 => hj.1 _ (Or.inr ?_)⟩
    by_cases h : b2 = b
    · exact ⟨a, b2, b', rfl, hb2, hb', h ▸ hne, ha⟩
    · exact ⟨a, b2, b, rfl, hb2, hb, h, ha⟩

lemma assemble {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate)
    (ch : ℕ → Option (Sym2 (Fin n))) (D : Finset (Sym2 (Fin n))) (T : Finset (Fin n))
    (k : ℕ) (hinv : ∀ j < n + k, OKw G gs ch D T j) (hcard : D.card + T.card ≤ k)
    (hgood : Good G gs D T (n + k)) :
    ∃ (ch' : ℕ → Option (Sym2 (Fin n))) (D' : Finset (Sym2 (Fin n))) (T' : Finset (Fin n)),
      (∀ j < n + (k + 1), OKw G gs ch' D' T' j) ∧ D'.card + T'.card ≤ k + 1 := by
  obtain ⟨c, d, t, h1, h2, h3, h4⟩ := hgood
  refine ⟨Function.update ch (n + k) c, D ∪ d.toFinset, T ∪ t.toFinset, ?_, ?_⟩
  · intro j hj
    by_cases hjk : j = n + k
    · subst hjk
      refine ⟨?_, ?_, ?_⟩
      · intro e he
        rw [Function.update_self]
        rcases h1 e he with h | h | h
        · exact Or.inl (Finset.mem_union_left _ h)
        · exact Or.inr h
        · exact Or.inl (Finset.mem_union_right _ (by rw [h]; simp))
      · intro b hb
        rw [Function.update_self]
        exact h2 b hb
      · intro e he
        rcases h3 e he with ⟨t', ht', hm⟩ | ⟨t', ht', hm⟩
        · exact ⟨t', Finset.mem_union_left _ ht', hm⟩
        · exact ⟨t', Finset.mem_union_right _ (by rw [ht']; simp), hm⟩
    · have hlt : j < n + k := by omega
      obtain ⟨a1, a2, a3⟩ := hinv j hlt
      refine ⟨?_, ?_, ?_⟩
      · intro e he
        rw [Function.update_of_ne hjk]
        rcases a1 e he with h | h
        · exact Or.inl (Finset.mem_union_left _ h)
        · exact Or.inr h
      · intro b hb
        rw [Function.update_of_ne hjk]
        exact a2 b hb
      · intro e he
        obtain ⟨t', ht', hm⟩ := a3 e he
        exact ⟨t', Finset.mem_union_left _ ht', hm⟩
  · have hd : (D ∪ d.toFinset).card ≤ D.card + d.toFinset.card := Finset.card_union_le _ _
    have ht : (T ∪ t.toFinset).card ≤ T.card + t.toFinset.card := Finset.card_union_le _ _
    have hd1 : d.toFinset.card ≤ 1 := by cases d <;> simp
    have ht1 : t.toFinset.card ≤ 1 := by cases t <;> simp
    rcases h4 with h | h
    · subst h
      simp only [Option.toFinset_none, Finset.union_empty]
      omega
    · subst h
      simp only [Option.toFinset_none, Finset.union_empty]
      omega

lemma good_or {n : ℕ} (G : SimpleGraph (Fin n))
    (hC4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (gs : List Gate)
    (ch : ℕ → Option (Sym2 (Fin n))) (D : Finset (Sym2 (Fin n))) (T : Finset (Fin n))
    (w g h : ℕ) (hg : OKw G gs ch D T g) (hh : OKw G gs ch D T h)
    (hw : ∀ z : Sym2 (Fin n), acc gs w z ↔ acc gs g z ∨ acc gs h z) :
    Good G gs D T w := by
  have hS : ∀ v, Sg G gs w v ↔ Sg G gs g v ∨ Sg G gs h v := by
    intro v
    unfold Sg
    rw [hw]
    tauto
  have hQ : ∀ e, Q G gs w e → Q G gs g e ∨ Q G gs h e := by
    intro e ⟨he, ha, hns⟩
    rcases (hw e).mp ha with h1 | h1
    · exact Or.inl ⟨he, h1, fun v hv hc => hns v hv ((hw _).mpr (Or.inl hc))⟩
    · exact Or.inr ⟨he, h1, fun v hv hc => hns v hv ((hw _).mpr (Or.inr hc))⟩
  have hT : ∀ e, Q G gs w e → (∃ t' ∈ T, t' ∈ e) ∨ ∃ t', (none : Option (Fin n)) = some t' ∧ t' ∈ e := by
    intro e he
    rcases hQ e he with h1 | h1
    · exact Or.inl (hg.2.2 e h1)
    · exact Or.inl (hh.2.2 e h1)
  have hXQ : ∀ e, Q G gs w e → e ∈ D ∨ ch g = some e ∨ ch h = some e := by
    intro e he
    rcases hQ e he with h1 | h1
    · rcases hg.1 e (Or.inl h1) with h2 | h2
      · exact Or.inl h2
      · exact Or.inr (Or.inl h2)
    · rcases hh.1 e (Or.inl h1) with h2 | h2
      · exact Or.inl h2
      · exact Or.inr (Or.inr h2)
  rcases tri (Sg G gs w) with h0 | ⟨b, hb⟩ | ⟨b, b', hne, hb, hb'⟩
  · refine ⟨ch g, ch h, none, ?_, ?_, hT, Or.inr rfl⟩
    · intro e he
      rcases he with hq | ⟨a, b, b', -, hb, -⟩
      · exact hXQ e hq
      · exact absurd hb (h0 b)
    · intro b hb
      exact absurd ((hb b).mpr rfl) (h0 b)
  · have hnoL : ∀ e, ¬ L G gs w e := by
      rintro e ⟨a, b1, b2, -, hb1, hb2, hne, -⟩
      exact hne (((hb b1).mp hb1).trans ((hb b2).mp hb2).symm)
    have hbw : Sg G gs w b := (hb b).mpr rfl
    rcases (hS b).mp hbw with hgb | hhb
    · have hgs : ∀ v, Sg G gs g v ↔ v = b :=
        fun v => ⟨fun hv => (hb v).mp ((hS v).mpr (Or.inl hv)), fun hv => hv ▸ hgb⟩
      have hnone := hg.2.1 b hgs
      refine ⟨none, ch h, none, ?_, fun _ _ => rfl, hT, Or.inr rfl⟩
      intro e he
      rcases he with hq | hl
      · rcases hXQ e hq with h1 | h1 | h1
        · exact Or.inl h1
        · rw [hnone] at h1
          cases h1
        · exact Or.inr (Or.inr h1)
      · exact absurd hl (hnoL e)
    · have hhs : ∀ v, Sg G gs h v ↔ v = b :=
        fun v => ⟨fun hv => (hb v).mp ((hS v).mpr (Or.inr hv)), fun hv => hv ▸ hhb⟩
      have hnone := hh.2.1 b hhs
      refine ⟨none, ch g, none, ?_, fun _ _ => rfl, hT, Or.inr rfl⟩
      intro e he
      rcases he with hq | hl
      · rcases hXQ e hq with h1 | h1 | h1
        · exact Or.inl h1
        · exact Or.inr (Or.inr h1)
        · rw [hnone] at h1
          cases h1
      · exact absurd hl (hnoL e)
  · have hsing : ∀ b0, (∀ v, Sg G gs w v ↔ v = b0) → False := by
      intro b0 hb0
      exact hne (((hb0 b).mp hb).trans ((hb0 b').mp hb').symm)
    by_cases hcen : ∃ a, ∀ c, Sg G gs w c → G.Adj a c
    · obtain ⟨a, ha⟩ := hcen
      obtain ⟨cg, cg1, cg2⟩ := side G gs ch D T g hg a
        (fun x hx => ha x ((hS x).mpr (Or.inl hx)))
      obtain ⟨chh, ch1, ch2⟩ := side G gs ch D T h hh a
        (fun x hx => ha x ((hS x).mpr (Or.inr hx)))
      refine ⟨cg, chh, none, ?_, fun b0 hb0 => absurd hb0 (hsing b0), hT, Or.inr rfl⟩
      intro e he
      rcases he with hq | ⟨a', b1, b2, he, hb1, hb2, hne12, ha'⟩
      · rcases hQ e hq with h1 | h1
        · rcases cg1 e (Or.inl h1) with h2 | h2
          · exact Or.inl h2
          · exact Or.inr (Or.inl h2)
        · rcases ch1 e (Or.inl h1) with h2 | h2
          · exact Or.inl h2
          · exact Or.inr (Or.inr h2)
      · have haa : a' = a := center_unique G hC4 (Sg G gs w) b b' hne hb hb' a' a ha' ha
        subst haa
        subst he
        rcases (hS b1).mp hb1 with h1 | h1
        · rcases cg2 b1 h1 with h2 | h2
          · exact Or.inl h2
          · exact Or.inr (Or.inl h2)
        · rcases ch2 b1 h1 with h2 | h2
          · exact Or.inl h2
          · exact Or.inr (Or.inr h2)
    · refine ⟨ch g, ch h, none, ?_, fun b0 hb0 => absurd hb0 (hsing b0), hT, Or.inr rfl⟩
      intro e he
      rcases he with hq | ⟨a', b1, b2, -, -, -, -, ha'⟩
      · exact hXQ e hq
      · exact absurd ⟨a', ha'⟩ hcen

lemma good_empty {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate)
    (D : Finset (Sym2 (Fin n))) (T : Finset (Fin n)) (w : ℕ)
    (hX : ∀ e, ¬ X G gs w e) : Good G gs D T w :=
  ⟨none, none, none, fun e he => absurd he (hX e), fun _ _ => rfl,
    fun e he => absurd (Or.inl he) (hX e), Or.inl rfl⟩

lemma good_and2 {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate)
    (hops : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (D : Finset (Sym2 (Fin n))) (T : Finset (Fin n)) (w : ℕ)
    (hII : ∀ e₁ e₂ : Sym2 (Fin n), e₁ ∈ G.edgeSet → e₂ ∈ G.edgeSet →
      acc gs w e₁ → acc gs w e₂ → e₁ = e₂) :
    Good G gs D T w := by
  have hnoL : ∀ e, ¬ L G gs w e := by
    rintro e ⟨a, b1, b2, -, hb1, hb2, hne, ha⟩
    have e1 : s(a, b1) ∈ G.edgeSet := (SimpleGraph.mem_edgeSet G).mpr (ha b1 hb1)
    have e2 : s(a, b2) ∈ G.edgeSet := (SimpleGraph.mem_edgeSet G).mpr (ha b2 hb2)
    have a1 : acc gs w s(a, b1) := acc_mono gs hops w b1 _ (Sym2.mem_mk_right a b1) hb1.1
    have a2 : acc gs w s(a, b2) := acc_mono gs hops w b2 _ (Sym2.mem_mk_right a b2) hb2.1
    have h12 := hII _ _ e1 e2 a1 a2
    rcases Sym2.eq_iff.mp h12 with ⟨-, h⟩ | ⟨h1, h2⟩
    · exact hne h
    · exact hne (h2.trans h1)
  by_cases hex : ∃ e, Q G gs w e
  · obtain ⟨e, he⟩ := hex
    obtain ⟨u, hu⟩ : ∃ u, u ∈ e := by
      induction e using Sym2.ind with
      | _ u v => exact ⟨u, Sym2.mem_mk_left u v⟩
    refine ⟨some e, none, some u, ?_, ?_, ?_, Or.inl rfl⟩
    · intro e' he'
      rcases he' with hq | hl
      · exact Or.inr (Or.inl (congrArg some (hII _ _ he.1 hq.1 he.2.1 hq.2.1)))
      · exact absurd hl (hnoL e')
    · intro b hb
      exfalso
      have hsb : Sg G gs w b := (hb b).mpr rfl
      obtain ⟨u', hu'⟩ := hsb.2
      have e1 : s(b, u') ∈ G.edgeSet := (SimpleGraph.mem_edgeSet G).mpr hu'
      have a1 : acc gs w s(b, u') := acc_mono gs hops w b _ (Sym2.mem_mk_left b u') hsb.1
      have h12 := hII _ _ e1 he.1 a1 he.2.1
      exact he.2.2 b (h12 ▸ Sym2.mem_mk_left b u') hsb.1
    · intro e' he'
      refine Or.inr ⟨u, rfl, ?_⟩
      rw [hII _ _ he'.1 he.1 he'.2.1 he.2.1]
      exact hu
  · refine ⟨none, none, none, ?_, fun _ _ => rfl, ?_, Or.inl rfl⟩
    · intro e he
      rcases he with hq | hl
      · exact absurd ⟨e, hq⟩ hex
      · exact absurd hl (hnoL e)
    · intro e he
      exact absurd ⟨e, he⟩ hex

lemma and1_Q {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate)
    (hops : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (w g h : ℕ)
    (hw : ∀ z : Sym2 (Fin n), acc gs w z ↔ acc gs g z ∧ acc gs h z)
    (hI : ∀ z : Sym2 (Fin n), acc gs w z → z ∈ G.edgeSet) :
    (∀ v, ¬ Sg G gs w v) ∧ (∀ a b, Sg G gs g a → Sg G gs h b → G.Adj a b) ∧
    (∀ e, Q G gs w e → Q G gs g e ∨ Q G gs h e ∨
      ∃ a b, e = s(a, b) ∧ Sg G gs g a ∧ Sg G gs h b) := by
  have hns : ∀ v : Fin n, ¬ acc gs w s(v, v) := by
    intro v hv
    have h1 := (SimpleGraph.mem_edgeSet G).mp (hI _ hv)
    exact h1.ne rfl
  refine ⟨fun v hv => hns v hv.1, ?_, ?_⟩
  · intro a b ha hb
    have h1 : acc gs g s(a, b) := acc_mono gs hops g a _ (Sym2.mem_mk_left a b) ha.1
    have h2 : acc gs h s(a, b) := acc_mono gs hops h b _ (Sym2.mem_mk_right a b) hb.1
    exact (SimpleGraph.mem_edgeSet G).mp (hI _ ((hw _).mpr ⟨h1, h2⟩))
  · rintro e ⟨he, ha, hnse⟩
    obtain ⟨hag, hah⟩ := (hw e).mp ha
    by_cases hqg : Q G gs g e
    · exact Or.inl hqg
    by_cases hqh : Q G gs h e
    · exact Or.inr (Or.inl hqh)
    refine Or.inr (Or.inr ?_)
    obtain ⟨x, hx, hxa⟩ : ∃ x ∈ e, acc gs g s(x, x) := by
      by_contra hcon
      exact hqg ⟨he, hag, fun v hv hc => hcon ⟨v, hv, hc⟩⟩
    obtain ⟨y, hy, hya⟩ : ∃ y ∈ e, acc gs h s(y, y) := by
      by_contra hcon
      exact hqh ⟨he, hah, fun v hv hc => hcon ⟨v, hv, hc⟩⟩
    have hxy : x ≠ y := by
      rintro rfl
      exact hnse x hx ((hw _).mpr ⟨hxa, hya⟩)
    exact ⟨x, y, (Sym2.mem_and_mem_iff hxy).mp ⟨hx, hy⟩,
      ⟨hxa, nbr_of_mem G e he x hx⟩, ⟨hya, nbr_of_mem G e he y hy⟩⟩

lemma and1_alpha {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate)
    (hops : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (ch : ℕ → Option (Sym2 (Fin n))) (D : Finset (Sym2 (Fin n))) (T : Finset (Fin n))
    (w g h : ℕ) (hg : OKw G gs ch D T g) (hh : OKw G gs ch D T h)
    (hw : ∀ z : Sym2 (Fin n), acc gs w z ↔ acc gs g z ∧ acc gs h z)
    (hI : ∀ z : Sym2 (Fin n), acc gs w z → z ∈ G.edgeSet)
    (hno : ∀ a b, ¬ (Sg G gs g a ∧ Sg G gs h b)) : Good G gs D T w := by
  obtain ⟨hSw, -, hQ⟩ := and1_Q G gs hops w g h hw hI
  refine ⟨ch g, ch h, none, ?_, ?_, ?_, Or.inr rfl⟩
  · intro e he
    rcases he with hq | ⟨a, b, b', -, hb, -⟩
    · rcases hQ e hq with h1 | h1 | ⟨a, b, -, ha, hb⟩
      · rcases hg.1 e (Or.inl h1) with h2 | h2
        · exact Or.inl h2
        · exact Or.inr (Or.inl h2)
      · rcases hh.1 e (Or.inl h1) with h2 | h2
        · exact Or.inl h2
        · exact Or.inr (Or.inr h2)
      · exact absurd ⟨ha, hb⟩ (hno a b)
    · exact absurd hb (hSw b)
  · intro b hb
    exact absurd ((hb b).mpr rfl) (hSw b)
  · intro e he
    rcases hQ e he with h1 | h1 | ⟨a, b, -, ha, hb⟩
    · exact Or.inl (hg.2.2 e h1)
    · exact Or.inl (hh.2.2 e h1)
    · exact absurd ⟨ha, hb⟩ (hno a b)

lemma and1_beta {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate)
    (hops : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (ch : ℕ → Option (Sym2 (Fin n))) (D : Finset (Sym2 (Fin n))) (T : Finset (Fin n))
    (w g h : ℕ) (hg : OKw G gs ch D T g) (hh : OKw G gs ch D T h)
    (hw : ∀ z : Sym2 (Fin n), acc gs w z ↔ acc gs g z ∧ acc gs h z)
    (hI : ∀ z : Sym2 (Fin n), acc gs w z → z ∈ G.edgeSet)
    (a : Fin n) (hga : ∀ v, Sg G gs g v ↔ v = a) : Good G gs D T w := by
  obtain ⟨hSw, hbip, hQ⟩ := and1_Q G gs hops w g h hw hI
  have hnone := hg.2.1 a hga
  have haS : Sg G gs g a := (hga a).mpr rfl
  obtain ⟨c, c1, c2⟩ := side G gs ch D T h hh a (fun b hb => hbip a b haS hb)
  refine ⟨c, none, some a, ?_, ?_, ?_, Or.inl rfl⟩
  · intro e he
    rcases he with hq | ⟨a', b, b', -, hb, -⟩
    · rcases hQ e hq with h1 | h1 | ⟨a', b, he', ha', hb⟩
      · rcases hg.1 e (Or.inl h1) with h2 | h2
        · exact Or.inl h2
        · rw [hnone] at h2
          cases h2
      · rcases c1 e (Or.inl h1) with h2 | h2
        · exact Or.inl h2
        · exact Or.inr (Or.inl h2)
      · rw [he', (hga a').mp ha']
        rcases c2 b hb with h2 | h2
        · exact Or.inl h2
        · exact Or.inr (Or.inl h2)
    · exact absurd hb (hSw b)
  · intro b hb
    exact absurd ((hb b).mpr rfl) (hSw b)
  · intro e he
    rcases hQ e he with h1 | h1 | ⟨a', b, he', ha', hb⟩
    · exact Or.inl (hg.2.2 e h1)
    · exact Or.inl (hh.2.2 e h1)
    · refine Or.inr ⟨a, rfl, ?_⟩
      rw [he', (hga a').mp ha']
      exact Sym2.mem_mk_left a b

lemma good_and1 {n : ℕ} (G : SimpleGraph (Fin n))
    (hC4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (gs : List Gate)
    (hops : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (ch : ℕ → Option (Sym2 (Fin n))) (D : Finset (Sym2 (Fin n))) (T : Finset (Fin n))
    (w g h : ℕ) (hg : OKw G gs ch D T g) (hh : OKw G gs ch D T h)
    (hw : ∀ z : Sym2 (Fin n), acc gs w z ↔ acc gs g z ∧ acc gs h z)
    (hI : ∀ z : Sym2 (Fin n), acc gs w z → z ∈ G.edgeSet) : Good G gs D T w := by
  obtain ⟨-, hbip, -⟩ := and1_Q G gs hops w g h hw hI
  rcases tri (Sg G gs g) with g0 | ⟨a, ha⟩ | ⟨a, a', hne, ha, ha'⟩
  · exact and1_alpha G gs hops ch D T w g h hg hh hw hI (fun a b hab => g0 a hab.1)
  · exact and1_beta G gs hops ch D T w g h hg hh hw hI a ha
  · rcases tri (Sg G gs h) with h0 | ⟨b, hb⟩ | ⟨b, b', hne', hb, hb'⟩
    · exact and1_alpha G gs hops ch D T w g h hg hh hw hI (fun a b hab => h0 b hab.2)
    · exact and1_beta G gs hops ch D T w h g hh hg
        (fun z => by rw [hw z]; exact and_comm) hI b hb
    · exact absurd ⟨hbip a b ha hb, (hbip a' b ha' hb).symm, hbip a' b' ha' hb',
        (hbip a b' ha hb').symm⟩ (hC4 a b a' b' hne hne')

lemma gate_good {n : ℕ} (G : SimpleGraph (Fin n))
    (hC4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (gs : List Gate)
    (hops : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hand : ∀ i (hi : i < gs.length), (gs[i]).op = GateOp.and →
      (∀ z : Sym2 (Fin n), acc gs (n + i) z → z ∈ G.edgeSet) ∨
      (∀ e₁ e₂ : Sym2 (Fin n), e₁ ∈ G.edgeSet → e₂ ∈ G.edgeSet →
        acc gs (n + i) e₁ → acc gs (n + i) e₂ → e₁ = e₂))
    (ch : ℕ → Option (Sym2 (Fin n))) (D : Finset (Sym2 (Fin n))) (T : Finset (Fin n))
    (i : ℕ) (hi : i < gs.length) (hinv : ∀ j < n + i, OKw G gs ch D T j) :
    Good G gs D T (n + i) := by
  have hops' : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or := fun g hg => (hops g hg).1
  have hdead : ∀ z : Sym2 (Fin n), ¬ acc gs (n + gs.length) z := acc_oob gs _ le_rfl
  obtain ⟨eff, heff, hOK⟩ : ∃ eff : ℕ → ℕ,
      (∀ j (z : Sym2 (Fin n)), (j < n + i ∧ acc gs j z) ↔ acc gs (eff j) z) ∧
      (∀ j, OKw G gs ch D T (eff j)) := by
    refine ⟨fun j => if j < n + i then j else n + gs.length, ?_, ?_⟩
    · intro j z
      by_cases hj : j < n + i
      · simp [hj]
      · simp [hj, hdead z]
    · intro j
      by_cases hj : j < n + i
      · simp only [hj, ite_true]
        exact hinv j hj
      · simp only [hj, ite_false]
        exact OKw_dead G gs ch D T _ hdead
  have hlen := (hops gs[i] (List.getElem_mem hi)).2
  rcases (hops gs[i] (List.getElem_mem hi)).1 with hop | hop
  · have hacc : ∀ z : Sym2 (Fin n),
        acc gs (n + i) z ↔ ∀ j ∈ (gs[i]).inputs, acc gs (eff j) z := by
      intro z
      have h0 := W_and gs i hi hop (ind z)
      constructor
      · intro h j hj
        exact (heff j z).mp ((h0.mp h) j hj)
      · intro h
        exact h0.mpr (fun j hj => (heff j z).mpr (h j hj))
    rcases hand i hi hop with hI | hII
    · rcases hin : (gs[i]).inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
      · apply good_empty
        intro e he
        have hall : ∀ z : Sym2 (Fin n), acc gs (n + i) z := by
          intro z
          rw [hacc z, hin]
          simp
        rcases he with hq | ⟨a, b, b', -, hb, -⟩
        · obtain ⟨u, hu⟩ : ∃ u, u ∈ e := by
            induction e using Sym2.ind with
            | _ u v => exact ⟨u, Sym2.mem_mk_left u v⟩
          exact hq.2.2 u hu (hall _)
        · have h1 := (SimpleGraph.mem_edgeSet G).mp (hI _ hb.1)
          exact h1.ne rfl
      · exact good_and1 G hC4 gs hops' ch D T (n + i) (eff a) (eff a) (hOK a) (hOK a)
          (fun z => by rw [hacc z, hin]; simp) hI
      · exact good_and1 G hC4 gs hops' ch D T (n + i) (eff a) (eff b) (hOK a) (hOK b)
          (fun z => by rw [hacc z, hin]; simp) hI
      · rw [hin] at hlen
        simp at hlen
    · exact good_and2 G gs hops' D T (n + i) hII
  · have hacc : ∀ z : Sym2 (Fin n),
        acc gs (n + i) z ↔ ∃ j ∈ (gs[i]).inputs, acc gs (eff j) z := by
      intro z
      have h0 := W_or gs i hi hop (ind z)
      constructor
      · intro h
        obtain ⟨j, hj, hj2⟩ := h0.mp h
        exact ⟨j, hj, (heff j z).mp hj2⟩
      · rintro ⟨j, hj, hj2⟩
        exact h0.mpr ⟨j, hj, (heff j z).mpr hj2⟩
    rcases hin : (gs[i]).inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
    · exact good_or G hC4 gs ch D T (n + i) (n + gs.length) (n + gs.length)
        (OKw_dead G gs ch D T _ hdead) (OKw_dead G gs ch D T _ hdead)
        (fun z => by rw [hacc z, hin]; simp [hdead z])
    · exact good_or G hC4 gs ch D T (n + i) (eff a) (eff a) (hOK a) (hOK a)
        (fun z => by rw [hacc z, hin]; simp)
    · exact good_or G hC4 gs ch D T (n + i) (eff a) (eff b) (hOK a) (hOK b)
        (fun z => by rw [hacc z, hin]; simp)
    · rw [hin] at hlen
      simp at hlen

lemma inv_all {n : ℕ} (G : SimpleGraph (Fin n))
    (hC4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (gs : List Gate)
    (hops : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hand : ∀ i (hi : i < gs.length), (gs[i]).op = GateOp.and →
      (∀ z : Sym2 (Fin n), acc gs (n + i) z → z ∈ G.edgeSet) ∨
      (∀ e₁ e₂ : Sym2 (Fin n), e₁ ∈ G.edgeSet → e₂ ∈ G.edgeSet →
        acc gs (n + i) e₁ → acc gs (n + i) e₂ → e₁ = e₂)) :
    ∀ k, k ≤ gs.length →
      ∃ (ch : ℕ → Option (Sym2 (Fin n))) (D : Finset (Sym2 (Fin n))) (T : Finset (Fin n)),
        (∀ j < n + k, OKw G gs ch D T j) ∧ D.card + T.card ≤ k := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨fun _ => none, ∅, ∅, ?_, by simp⟩
    intro j hj
    have hj' : j < n := by omega
    have hnoQ : ∀ e, ¬ Q G gs j e := by
      rintro e ⟨-, ha, hns⟩
      have hm := (acc_input gs j hj' e).mp ha
      exact hns _ hm ((acc_input gs j hj' _).mpr (Sym2.mem_mk_left _ _))
    refine ⟨?_, fun _ _ => rfl, fun e he => absurd he (hnoQ e)⟩
    intro e he
    exfalso
    rcases he with hq | ⟨a, b, b', -, hb, hb', hne, -⟩
    · exact hnoQ e hq
    · have h1 := (acc_input gs j hj' _).mp hb.1
      have h2 := (acc_input gs j hj' _).mp hb'.1
      simp only [Sym2.mem_iff, or_self] at h1 h2
      exact hne (h1.symm.trans h2)
  | succ k ih =>
    intro hk
    obtain ⟨ch, D, T, hinv, hcard⟩ := ih (by omega)
    exact assemble G gs ch D T k hinv hcard
      (gate_good G hC4 gs hops hand ch D T k (by omega) hinv)

lemma main (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hC4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (gates : List Gate) (out : ℕ)
    (hops : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (heval : ∀ x : Fin n → Bool, Circuit.eval ⟨gates, out⟩ (List.ofFn x)
      = decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true))
    (hand : ∀ i : Fin gates.length, (gates.get i).op = GateOp.and →
      (∀ x : Fin n → Bool,
        (Circuit.wires ⟨gates, 0⟩ (List.ofFn x)).getD (n + (i : ℕ)) false = true →
          ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) ∨
      (∀ a b c d : Fin n, G.Adj a b → G.Adj c d →
        (Circuit.wires ⟨gates, 0⟩
          (List.ofFn (fun k => decide (k = a ∨ k = b)))).getD (n + (i : ℕ)) false = true →
        (Circuit.wires ⟨gates, 0⟩
          (List.ofFn (fun k => decide (k = c ∨ k = d)))).getD (n + (i : ℕ)) false = true →
        (a = c ∧ b = d) ∨ (a = d ∧ b = c))) :
    ∃ T : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ T ∨ v ∈ T) ∧
      G.edgeFinset.card + T.card ≤ gates.length + 1 := by
  have hWout : ∀ x : Fin n → Bool, W gates out x
      = decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) := heval
  have hF : ∀ z : Sym2 (Fin n), acc gates out z ↔ z ∈ G.edgeSet := by
    intro z
    unfold acc
    rw [hWout]
    simp only [decide_eq_true_eq, ind]
    constructor
    · rintro ⟨u, v, huv, hu, hv⟩
      rw [(Sym2.mem_and_mem_iff huv.ne).mp ⟨hu, hv⟩]
      exact (SimpleGraph.mem_edgeSet G).mpr huv
    · intro hz
      induction z using Sym2.ind with
      | _ u v =>
        exact ⟨u, v, (SimpleGraph.mem_edgeSet G).mp hz, Sym2.mem_mk_left u v,
          Sym2.mem_mk_right u v⟩
  have hind : ∀ a b : Fin n, (fun k => decide (k = a ∨ k = b)) = ind s(a, b) := by
    intro a b
    funext k
    simp [ind]
  have hand' : ∀ i (hi : i < gates.length), (gates[i]).op = GateOp.and →
      (∀ z : Sym2 (Fin n), acc gates (n + i) z → z ∈ G.edgeSet) ∨
      (∀ e₁ e₂ : Sym2 (Fin n), e₁ ∈ G.edgeSet → e₂ ∈ G.edgeSet →
        acc gates (n + i) e₁ → acc gates (n + i) e₂ → e₁ = e₂) := by
    intro i hi hop
    rcases hand ⟨i, hi⟩ hop with h | h
    · left
      intro z hz
      obtain ⟨u, v, huv, hu, hv⟩ := h (ind z) hz
      simp only [ind, decide_eq_true_eq] at hu hv
      rw [(Sym2.mem_and_mem_iff huv.ne).mp ⟨hu, hv⟩]
      exact (SimpleGraph.mem_edgeSet G).mpr huv
    · right
      intro e₁ e₂ h1 h2 a1 a2
      induction e₁ using Sym2.ind with
      | _ a b =>
        induction e₂ using Sym2.ind with
        | _ c d =>
          have h3 := h a b c d ((SimpleGraph.mem_edgeSet G).mp h1)
            ((SimpleGraph.mem_edgeSet G).mp h2)
            (by rw [hind]; exact a1) (by rw [hind]; exact a2)
          exact Sym2.eq_iff.mpr h3
  by_cases hout : out < n + gates.length
  · obtain ⟨ch, D, T, hinv, hcard⟩ := inv_all G hC4 gates hops hand' gates.length le_rfl
    obtain ⟨o1, -, o3⟩ := hinv out hout
    have hQ : ∀ e ∈ G.edgeSet, Q G gates out e := by
      intro e he
      refine ⟨he, (hF e).mpr he, fun v _ hv => ?_⟩
      have h1 := (SimpleGraph.mem_edgeSet G).mp ((hF _).mp hv)
      exact h1.ne rfl
    refine ⟨T, ?_, ?_⟩
    · intro u v huv
      obtain ⟨t, ht, hm⟩ := o3 _ (hQ s(u, v) ((SimpleGraph.mem_edgeSet G).mpr huv))
      rcases Sym2.mem_iff.mp hm with h | h
      · exact Or.inl (h ▸ ht)
      · exact Or.inr (h ▸ ht)
    · have hsub : G.edgeFinset ⊆ D ∪ (ch out).toFinset := by
        intro e he
        rw [SimpleGraph.mem_edgeFinset] at he
        rcases o1 e (Or.inl (hQ e he)) with h | h
        · exact Finset.mem_union_left _ h
        · exact Finset.mem_union_right _ (by rw [h]; simp)
      have h1 := Finset.card_le_card hsub
      have h2 := Finset.card_union_le D (ch out).toFinset
      have h3 : (ch out).toFinset.card ≤ 1 := by
        cases (ch out) <;> simp
      omega
  · refine ⟨∅, ?_, ?_⟩
    · intro u v huv
      exfalso
      exact acc_oob gates out (by omega) s(u, v)
        ((hF _).mpr ((SimpleGraph.mem_edgeSet G).mpr huv))
    · have hE : G.edgeFinset = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro e he
        rw [SimpleGraph.mem_edgeFinset] at he
        exact acc_oob gates out (by omega) e ((hF e).mpr he)
      rw [hE]
      simp

end PEqualNP.Outside.L_meta_4767

theorem PEqualNP.Outside.L_meta_4767 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out⟩ (List.ofFn x) = decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) → (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ x : Fin n → Bool, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn x)).getD (n + (i : ℕ)) false = true → ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) ∨ (∀ a b c d : Fin n, G.Adj a b → G.Adj c d → (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun k => decide (k = a ∨ k = b)))).getD (n + (i : ℕ)) false = true → (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun k => decide (k = c ∨ k = d)))).getD (n + (i : ℕ)) false = true → (a = c ∧ b = d) ∨ (a = d ∧ b = c))) → ∃ T : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ T ∨ v ∈ T) ∧ G.edgeFinset.card + T.card ≤ gates.length + 1 := by
  intro n G _ hC4 gates out hops heval hand
  exact PEqualNP.Outside.L_meta_4767.main n G hC4 gates out hops heval hand
