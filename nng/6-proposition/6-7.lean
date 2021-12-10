lemma imp_trans (P Q R : Prop) : (P → Q) → ((Q → R) → (P → R)) :=
begin
intros hpq hqr,
intro p,
apply hqr,
apply hpq,
exact p,
end