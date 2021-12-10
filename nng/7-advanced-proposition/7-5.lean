lemma iff_trans (P Q R : Prop) : (P ↔ Q) → (Q ↔ R) → (P ↔ R) :=
begin
intros f h,
cases f with pq qp,
cases h with qr rq,
split,
intro p,
apply qr,
apply pq,
exact p,
intro r,
apply qp,
apply rq,
exact r,
end