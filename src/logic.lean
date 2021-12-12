section propositional

variables P Q R : Prop


------------------------------------------------
-- Proposições de dupla negaçao:
------------------------------------------------

theorem doubleneg_intro :
  P → ¬¬P  :=
begin
  intro p,
  intro np,
  apply np,
  exact p,
end

theorem doubleneg_elim :
  ¬¬P → P  :=
begin
  intro nnp,
  by_contradiction np,
  exact nnp np,
end

theorem doubleneg_law :
  ¬¬P ↔ P  :=
begin
  split,
  exact doubleneg_elim P,
  exact doubleneg_intro P,
end

------------------------------------------------
-- Comutatividade dos ∨,∧:
------------------------------------------------

theorem disj_comm :
  (P ∨ Q) → (Q ∨ P)  :=
begin
  intro pq,
  cases pq with p q,
  right,
  exact p,
  left,
  exact q,
end

theorem conj_comm :
  (P ∧ Q) → (Q ∧ P)  :=
begin
  intro pq,
  cases pq with p q,
  split,
  exact q,
  exact p,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos →,∨:
------------------------------------------------

theorem impl_as_disj_converse :
  (¬P ∨ Q) → (P → Q)  :=
begin
  intro npq,
  intro p,
  cases npq with np q,
  exfalso,
  exact np p,
  exact q,
end

theorem disj_as_impl :
  (P ∨ Q) → (¬P → Q)  :=
begin
  intros pq np,
  cases pq with p q,
  exfalso,
  exact np p,
  exact q,
end


------------------------------------------------
-- Proposições de contraposição:
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬Q → ¬P)  :=
begin
  intros hpq nq p,
  apply nq,
  apply hpq,
  exact p,
end

theorem impl_as_contrapositive_converse :
  (¬Q → ¬P) → (P → Q)  :=
begin
  intros nqp p,
  by_contradiction,
  have np := nqp h,
  apply np,
  exact p,
end

theorem contrapositive_law :
  (P → Q) ↔ (¬Q → ¬P)  :=
begin
  split,
  exact impl_as_contrapositive P Q,
  exact impl_as_contrapositive_converse P Q,
end


------------------------------------------------
-- A irrefutabilidade do LEM:
------------------------------------------------

theorem lem_irrefutable :
  ¬¬(P∨¬P)  :=
begin
  intro nnp,
  apply nnp,
  right,
  intro p,
  apply nnp,
  left,
  exact p,
end


------------------------------------------------
-- A lei de Peirce
------------------------------------------------

theorem peirce_law_weak :
  ((P → Q) → P) → ¬¬P  :=
begin
  intros pqp np,
  have h : P → Q,
  intro p,
  exfalso,
  apply np,
  exact p,
  apply np,
  have p := pqp h,
  exact p,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∨,∧:
------------------------------------------------

theorem disj_as_negconj :
  P∨Q → ¬(¬P∧¬Q)  :=
begin
  intros pq npq,
  cases pq with p q,
  cases npq with np nq,
  contradiction,
  cases npq with np nq,
  contradiction,
end

theorem conj_as_negdisj :
  P∧Q → ¬(¬P∨¬Q)  :=
begin
  intros pq npq,
  cases npq with np nq,
  cases pq with p q,
  contradiction,
  cases pq with p q,
  contradiction,
end


------------------------------------------------
-- As leis de De Morgan para ∨,∧:
------------------------------------------------

theorem demorgan_ndisj :
  ¬(P∨Q) → (¬P ∧ ¬Q)  :=
begin
  intro npq,
  split,
  intro p,
  apply npq,
  left,
  exact p,
  intro q,
  apply npq,
  right,
  exact q,
end

theorem demorgan_ndisj_converse :
  (¬P ∧ ¬Q) → ¬(P∨Q)  :=
begin
  intro npnq,
  intro pq,
  cases npnq with np nq,
  cases pq with p q,
  apply np,
  exact p,
  apply nq,
  exact q,
end

theorem demorgan_nconj_converse :
  (¬Q ∨ ¬P) → ¬(P∧Q)  :=
begin
  intros nqnp pq,
  cases nqnp with nq np,
  cases pq with p q,
  apply nq,
  exact q,
  cases pq with p q,
  apply np,
  exact p,
end


------------------------------------------------
-- Proposições de distributividade dos ∨,∧:
------------------------------------------------

theorem distr_conj_disj :
  P∧(Q∨R) → (P∧Q)∨(P∧R)  :=
begin
  --- acho melhor começar a usar uns nomes legais hehe
  intro p_and_q_or_r,
  cases p_and_q_or_r with p q_or_r,
  cases q_or_r with q r,
  left,
  split,
  exact p,
  exact q,
  right,
  split,
  exact p,
  exact r,
end

theorem distr_conj_disj_converse :
  (P∧Q)∨(P∧R) → P∧(Q∨R)  :=
begin
  --- o nome desse é grande demais
  intro pqpr,
  cases pqpr with pq pr,
  cases pq with p q,
  split,
  exact p,
  left,
  exact q,
  cases pr with p r,
  split,
  exact p,
  right,
  exact r,
end

theorem distr_disj_conj :
  P∨(Q∧R) → (P∨Q)∧(P∨R)  :=
begin
  intro pqr,
  cases pqr with p qr,
  split,
  left,
  exact p,
  left,
  exact p,
  cases qr with q r,
  split,
  right,
  exact q,
  right, 
  exact r,
end

theorem distr_disj_conj_converse :
  (P∨Q)∧(P∨R) → P∨(Q∧R)  :=
begin
  intro pqpr,
  cases pqpr with pq pr,
  cases pr with p r,
  left,
  exact p,
  cases pq with p q,
  left,
  exact p,
  right,
  split,
  exact q,
  exact r,
end


------------------------------------------------
-- Currificação
------------------------------------------------

theorem curry_prop :
  ((P∧Q)→R) → (P→(Q→R))  :=
begin
  intro pqr,
  intros p q,
  apply pqr,
  split,
  exact p,
  exact q,
end

theorem uncurry_prop :
  (P→(Q→R)) → ((P∧Q)→R)  :=
begin
  intros pqr pq,
  apply pqr,
  cases pq with p q,
  exact p,
  cases pq with p q,
  exact q,
end


------------------------------------------------
-- Reflexividade da →:
------------------------------------------------

theorem impl_refl :
  P → P  :=
begin
  intro p,
  exact p,
end

------------------------------------------------
-- Weakening and contraction:
------------------------------------------------

theorem weaken_disj_right :
  P → (P∨Q)  :=
begin
  intro p,
  left,
  exact p,
end

theorem weaken_disj_left :
  Q → (P∨Q)  :=
begin
  intro q,
  right,
  exact q,
end

theorem weaken_conj_right :
  (P∧Q) → P  :=
begin
  intro pq,
  cases pq with p q,
  exact p,
end

theorem weaken_conj_left :
  (P∧Q) → Q  :=
begin
  intro pq,
  cases pq with p q,
  exact q,
end

theorem conj_idempot :
  (P∧P) ↔ P :=
begin
  split,
  exact weaken_conj_right P P,
  intro p,
  split,
  exact p,
  exact p,
end

theorem disj_idemp :
  (P∨P) ↔ P  :=
begin
  split,
  intro p,
  cases p with p' p'',
  exact p',
  exact p'',
  exact weaken_disj_left P P,
end

end propositional


----------------------------------------------------------------


section predicate

variable U : Type
variables P Q : U -> Prop


------------------------------------------------
-- As leis de De Morgan para ∃,∀:
------------------------------------------------

theorem demorgan_exists_neg :
  (∃x, ¬P x) → ¬(∀x, P x)  :=
begin
  intros h ax,
  cases h with x hx,
  have xx := ax x,
  apply hx,
  exact xx,
end

theorem demorgan_neg_exists :
  ¬(∃x, P x) → (∀x, ¬P x)  :=
begin
  intros h x np,
  apply h,
  existsi x,
  exact np,
end

theorem demorgan_forall_neg :
  (∀x, ¬P x) → ¬(∃x, P x)  :=
begin
  intros h nx,
  cases nx with x hx,
  have xx := h x,
  apply xx,
  exact hx,
end

theorem demorgan_neg_forall :
  ¬(∀x, P x) → (∃x, ¬P x)  :=
begin
  intro h,
  by_contradiction nh,
  apply h,
  intro u,
  by_contradiction npu,
  apply nh,
  existsi u,
  exact npu,
end

theorem demorgan_exists_law :
  (∃x, ¬P x) ↔ ¬(∀x, P x)  :=
begin
  split,
  exact demorgan_exists_neg U P,
  exact demorgan_neg_forall U P,
end

theorem demorgan_forall_law :
  (∀x, ¬P x) ↔ ¬(∃x, P x)  :=
begin
  split,
  exact demorgan_forall_neg U P,
  exact demorgan_neg_exists U P,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∃,∀:
------------------------------------------------

theorem exists_as_neg_forall :
  (∃x, P x) → ¬(∀x, ¬P x)  :=
begin
  intros h nh,
  cases h with x hx,
  have xx := nh x,
  apply xx,
  exact hx,
end

theorem forall_as_neg_exists :
  (∀x, P x) → ¬(∃x, ¬P x)  :=
begin
  intros h nh,
  cases nh with x hx,
  have xx := h x,
  apply hx,
  exact xx,
end

theorem forall_as_neg_exists_converse :
  ¬(∃x, ¬P x) → (∀x, P x)  :=
begin
  intros h u,
  by_contradiction npu,
  apply h,
  existsi u,
  exact npu,
end

theorem exists_as_neg_forall_converse :
  ¬(∀x, ¬P x) → (∃x, P x)  :=
begin
  intros h,
  by_contradiction nep,
  apply h,
  intros u npu,
  apply nep,
  existsi u,
  exact npu,
end

theorem forall_as_neg_exists_law :
  (∀x, P x) ↔ ¬(∃x, ¬P x)  :=
begin
  split,
  exact forall_as_neg_exists U P,
  exact forall_as_neg_exists_converse U P,
end

theorem exists_as_neg_forall_law :
  (∃x, P x) ↔ ¬(∀x, ¬P x)  :=
begin
  split,
  exact exists_as_neg_forall U P,
  exact exists_as_neg_forall_converse U P,
end


------------------------------------------------
--  Proposições de distributividade de quantificadores:
------------------------------------------------

theorem exists_conj_as_conj_exists :
  (∃x, P x ∧ Q x) → (∃x, P x) ∧ (∃x, Q x)  :=
begin
  intros h,
  split,
  cases h with x hx,
  cases hx with px qx,
  existsi x,
  exact px,
  cases h with x hx,
  cases hx with px qx,
  existsi x,
  exact qx,
end

theorem exists_disj_as_disj_exists :
  (∃x, P x ∨ Q x) → (∃x, P x) ∨ (∃x, Q x)  :=
begin
  intros h,
  cases h with x hx,
  cases hx with px qx,
  left,
  existsi x,
  exact px,
  right,
  existsi x,
  exact qx,
end

theorem exists_disj_as_disj_exists_converse :
  (∃x, P x) ∨ (∃x, Q x) → (∃x, P x ∨ Q x)  :=
begin
  intros h,
  cases h with epx eqx,
  cases epx with x hx,
  existsi x,
  left,
  exact hx,
  cases eqx with x hx,
  existsi x,
  right,
  exact hx,
end

theorem forall_conj_as_conj_forall :
  (∀x, P x ∧ Q x) → (∀x, P x) ∧ (∀x, Q x)  :=
begin
  intros h,
  split,
  intro x,
  have xx := h x,
  cases xx with px qx,
  exact px,
  intro x,
  have xx := h x,
  cases xx with px qx,
  exact qx,
end

theorem forall_conj_as_conj_forall_converse :
  (∀x, P x) ∧ (∀x, Q x) → (∀x, P x ∧ Q x)  :=
begin
  intros h,
  cases h with apx aqx,
  intro x,
  split,
  exact apx x,
  exact aqx x,
end


theorem forall_disj_as_disj_forall_converse :
  (∀x, P x) ∨ (∀x, Q x) → (∀x, P x ∨ Q x)  :=
begin
  intros h,
  cases h with apx aqx,
  intro x,
  left,
  exact apx x,
  intro x,
  right,
  exact aqx x,
end


/- NOT THEOREMS --------------------------------

theorem forall_disj_as_disj_forall :
  (∀x, P x ∨ Q x) → (∀x, P x) ∨ (∀x, Q x)  :=
begin
  sorry,
end

theorem exists_conj_as_conj_exists_converse :
  (∃x, P x) ∧ (∃x, Q x) → (∃x, P x ∧ Q x)  :=
begin
  sorry,
end

---------------------------------------------- -/

end predicate
