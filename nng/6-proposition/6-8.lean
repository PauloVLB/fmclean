lemma contrapositive (P Q : Prop) : (P → Q) → (¬ Q → ¬ P) :=
begin
repeat {rw not_iff_imp_false},
intros hpq hqf p,
apply hqf,
apply hpq,
exact p,
end