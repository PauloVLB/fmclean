lemma example3 (a b : mynat) (h : succ a = b) : succ(succ(a)) = succ(b) :=
begin
rw ← h,
refl
end