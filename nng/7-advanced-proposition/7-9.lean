lemma contra (P Q : Prop) : (P ∧ ¬ P) → Q :=
begin
intro h,
exfalso,
rw not_iff_imp_false at h,
cases h with p pf,
apply pf,
exact p,
end