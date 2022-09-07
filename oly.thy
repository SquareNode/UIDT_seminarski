theory oly
  imports Complex_Main
begin

(* https://www.imo-official.org/problems/IMO2012SL.pdf *)

lemma n6_lema:
  fixes x::nat and y::nat and n::nat
  assumes "\<forall> n . (x^(2^n)-1) mod (2^n*y + 1) = 0"
  shows "x=1"
  sorry

primrec prime'::"nat \<Rightarrow> nat \<Rightarrow> nat" where 
"prime' x 0 = (if x mod 2 = 0 then 1 else 0)" |
"prime' x (Suc y)  = (if x mod ((Suc y)+2) = 0 then 1 + prime' x y else prime' x y)"

primrec biggest::"nat \<Rightarrow> nat \<Rightarrow> nat" where 
"biggest p 0 = 0" |
"biggest p (Suc q) = (if (Suc q) * (Suc q) >  p then biggest p q else (Suc q))"

primrec prime'_inef::"nat \<Rightarrow> nat \<Rightarrow> nat" where 
"prime'_inef x 0 = 0" |
"prime'_inef x (Suc y) = (if x mod (Suc y) = 0 then 1 + prime'_inef x y else prime'_inef x y)"

fun prime::"nat \<Rightarrow> bool" where
(* "prime p = (if prime' p ((biggest p p)-2) = 0 then True else False)" *)
"prime p = (if prime'_inef p p \<le> 2 then True else False)"

value "biggest 14 14"
value "prime 12"
value "prime 144"
value "prime 13"
value "prime 7"
value "prime 6"
value "prime 2"
value "prime 1"

lemma n8_lemma:
  fixes p::nat and r::int and a::int and b::int
  assumes "p>100" "prime p"
  shows "\<forall> r . \<exists> a b . (a*a + b^5 - r) mod p = 0"
  sorry

end