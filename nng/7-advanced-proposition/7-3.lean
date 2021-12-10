lemma and_trans (P Q R : Prop) : P ∧ Q → Q ∧ R → P ∧ R :=
begin
intros f h,
cases f with p q,
cases h with q r,
split,
exact p,
exact r,
end